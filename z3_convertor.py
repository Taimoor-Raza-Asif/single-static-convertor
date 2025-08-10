import re
from z3 import *

# Operator precedence and SMT operator mapping
precedence = {
    '==': 1, '!=': 1, '>': 1, '<': 1, '>=': 1, '<=': 1,
    '+': 2, '-': 2,
    '*': 3, '/': 3, '%': 3
}

smt_op_map = {
    '+': '+', '-': '-', '*': '*', '/': 'div', '%': 'mod',
    '==': '=', '!=': 'distinct', '>': '>', '<': '<', '>=': '>=', '<=': '<='
}

def tokenize(expr):
    # Split by operators, parentheses, and whitespace
    return re.findall(r'\w+|==|!=|>=|<=|[+\-*/%()<>]', expr)

def validate_parentheses(expr):
    """Check if parentheses in the expression are balanced."""
    balance = 0
    for char in expr:
        if char == '(':
            balance += 1
        elif char == ')':
            balance -= 1
        if balance < 0:
            return False
    return balance == 0

def infix_to_postfix(tokens):
    output = []
    stack = []
    for token in tokens:
        if token in precedence:
            while (stack and stack[-1] in precedence and
                   precedence[token] <= precedence[stack[-1]]):
                output.append(stack.pop())
            stack.append(token)
        elif token == '(':
            stack.append(token)
        elif token == ')':
            while stack and stack[-1] != '(':
                output.append(stack.pop())
            if stack and stack[-1] == '(':
                stack.pop()  # Remove '(' if it exists
            else:
                raise ValueError("Mismatched parentheses: extra closing parenthesis")
        else:
            output.append(token)
    while stack:
        if stack[-1] == '(':
            raise ValueError("Mismatched parentheses: unclosed parenthesis")
        output.append(stack.pop())
    return output

def postfix_to_smt(postfix):
    stack = []
    for token in postfix:
        if token in smt_op_map:
            b = stack.pop()
            a = stack.pop()
            stack.append(f"({smt_op_map[token]} {a} {b})")
        else:
            stack.append(token)
    return stack[0] if stack else ""

def infix_to_smt(expr):
    tokens = tokenize(expr)
    postfix = infix_to_postfix(tokens)
    return postfix_to_smt(postfix)

def parse_ssa_line(line):
    # Ignore assert and assume lines (handled elsewhere)
    if line.strip().startswith("assert") or line.strip().startswith("assume"):
        return None, None

    # Use regex to split on the first "=" not part of "=="
    match = re.match(r'^([^=]+?)\s*=\s*(.+)$', line)
    if not match:
        raise ValueError(f"Invalid SSA line format (could not parse): {line}")
    var, expr = match.group(1), match.group(2)
    return var.strip(), expr.strip()

def infer_type(expr):
    if re.search(r"\btrue\b|\bfalse\b", expr.lower()):
        return 'Bool'
    if '?' in expr and ':' in expr:
        return 'Int'
    if re.search(r"[<>]|==|!=|>=|<=", expr):
        return 'Bool'
    if 'select arr' in expr:
        return 'Int'
    return 'Int'

def extract_variables(expr):
    return set(re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expr))

def convert_expr_to_smt(expr, declarations):
    expr = expr.strip().replace('φ', 'phi')  # Replace φ with phi
    if not expr:
        raise ValueError("Empty expression provided")

    # Validate parentheses
    if not validate_parentheses(expr):
        raise ValueError(f"Invalid expression: unbalanced parentheses in '{expr}'")

    # Remove outer parentheses if present
    if expr.startswith('(') and expr.endswith(')'):
        inner_expr = expr[1:-1].strip()
        if validate_parentheses(inner_expr):
            expr = inner_expr

    # Handle ternary expressions (cond ? true_expr : false_expr)
    parts = []
    balance = 0
    start = 0
    for i, char in enumerate(expr):
        if char == '(':
            balance += 1
        elif char == ')':
            balance -= 1
        elif char == '?' and balance == 0:
            parts.append(expr[start:i].strip())
            start = i + 1
        elif char == ':' and balance == 0 and len(parts) == 1:
            parts.append(expr[start:i].strip())
            start = i + 1
    parts.append(expr[start:].strip())

    if len(parts) == 3:
        cond = convert_expr_to_smt(parts[0], declarations)
        true_expr = convert_expr_to_smt(parts[1], declarations)
        false_expr = convert_expr_to_smt(parts[2], declarations)
        return f"(ite {cond} {true_expr} {false_expr})"

    # Handle array accesses (e.g., arr[i] -> (select arr i))
    def replace_array_access(match):
        array_name = match.group(1)
        index = match.group(2)
        return f"(select {array_name} {index})"

    expr = re.sub(r'(\w+)\[(\w+)\]', replace_array_access, expr)

    # Handle boolean literals
    if expr.lower() in ['true', 'false']:
        return expr.lower()

    # Handle arithmetic and comparison expressions using infix_to_smt
    try:
        smt_expr = infix_to_smt(expr)
        return smt_expr
    except Exception as e:
        # Fallback for simple variables or numbers
        if re.match(r'^\w+$|^\d+$', expr):
            return expr
        raise ValueError(f"Failed to convert expression to SMT: {expr} (Error: {str(e)})")

def convert_ssa_to_smtlib(ssa_lines):
    declarations = {}
    assertions = []
    used_vars = set()
    arrays = set()

    for line in ssa_lines:
        if not line.strip() or '=' not in line:
            continue
        var, expr = parse_ssa_line(line)
        var = var.replace('φ', 'phi')  # Replace φ in variable name
        var_type = infer_type(expr)
        declarations[var] = var_type

        tokens = extract_variables(expr)
        for token in tokens:
            token = token.replace('φ', 'phi')
            if token not in declarations and token not in {"true", "false"}:
                if '[' in token and ']' in token and token.startswith('arr'):
                    declarations['arr'] = 'IntArray'
                    arrays.add('arr')
                else:
                    declarations[token] = 'Bool' if token.startswith('phi') else 'Int'
            used_vars.add(token)

        used_vars.add(var)
        smt_expr = convert_expr_to_smt(expr, declarations)
        assertions.append(f"(assert (= {var} {smt_expr}))")

    smt_code_lines = ["(set-logic QF_UFLIA)"]

    for arr in sorted(arrays):
        smt_code_lines.append(f"(declare-sort IntArray)")
        smt_code_lines.append(f"(declare-fun select (IntArray Int) Int)")
        smt_code_lines.append(f"(declare-fun store (IntArray Int Int) IntArray)")
        smt_code_lines.append(f"(declare-const {arr} IntArray)")

    for var in sorted(used_vars):
        if var not in arrays:
            vtype = declarations[var]
            smt_code_lines.append(f"(declare-const {var} {vtype})")

    smt_code_lines.extend(assertions)

    final_assertion_line = [line for line in ssa_lines if line.startswith("assert(")]
    if final_assertion_line:
        assertion_line = final_assertion_line[0].strip()
        if not (assertion_line.startswith("assert(") and assertion_line.endswith(")")):
            raise ValueError(f"Invalid assertion format: {assertion_line}")
        assertion_expr_raw = assertion_line[len("assert("):-1].strip().replace('φ', 'phi')
        if not assertion_expr_raw:
            raise ValueError("Empty assertion expression")

        # Validate the assertion expression
        if not validate_parentheses(assertion_expr_raw):
            raise ValueError(f"Invalid assertion expression: unbalanced parentheses in '{assertion_expr_raw}'")

        def replace_array_access_assert(match):
            array_name = match.group(1)
            index = match.group(2)
            return f"(select {array_name} {index})"

        assertion_expr = re.sub(r'(\w+)\[(\w+)\]', replace_array_access_assert, assertion_expr_raw)
        assertion_expr = convert_expr_to_smt(assertion_expr, declarations)
        smt_code_lines.append(f"(assert {assertion_expr})")

    smt_code_lines.append("(check-sat)")
    smt_code_lines.append("(get-model)")
    return "\n".join(smt_code_lines), declarations, arrays

def check_with_z3(smt_code, declarations, arrays):
    s = Solver()
    try:
        parsed = parse_smt2_string(smt_code)
        s.add(parsed)
        result = s.check()
        output = []

        if result == sat:
            model = s.model()
            output.append("Satisfiable. Model where assertions hold:")
            for d in model.decls():
                output.append(f"  {d.name()} = {model[d]}")
            return True, output
        elif result == unsat:
            final_assertion = [line for line in smt_code.split('\n') if line.strip().startswith('(assert')][-1]
            negated_smt_lines = smt_code.split('\n')
            negated_smt_lines[-3] = f"(assert (not {final_assertion[7:-1]}))"
            negated_smt = "\n".join(negated_smt_lines)
            s.reset()
            s.add(parse_smt2_string(negated_smt))
            counterexamples = []
            for _ in range(2):
                if s.check() == sat:
                    model = s.model()
                    counterexample = [f"Counterexample {_ + 1}:"]
                    for d in model.decls():
                        counterexample.append(f"  {d.name()} = {model[d]}")
                    counterexamples.append("\n".join(counterexample))
                    block = Not(And([d() == model[d] for d in model.decls()]))
                    s.add(block)
                else:
                    break
            if counterexamples:
                output.append("Unsatisfiable. Counterexamples where assertions fail:")
                output.extend(counterexamples)
            else:
                output.append("Unsatisfiable. No counterexamples found.")
            return False, output
        else:
            return False, ["Unknown result from solver."]
    except Exception as e:
        return False, [f"Error in Z3: {str(e)}"]

def convert_to_z3_and_check(ssa_lines):
    smt_output, declarations, arrays = convert_ssa_to_smtlib(ssa_lines)
    is_sat, z3_result = check_with_z3(smt_output, declarations, arrays)
    return is_sat, z3_result
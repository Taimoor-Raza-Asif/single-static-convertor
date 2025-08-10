import re

def parse_assignment(line):
    # Match scalar assignments of the form var := expr; or var = expr;
    match = re.match(r'(\w+)\s*(:=|=)\s*(.*?)\s*;', line)
    if match:
        return match.group(1), match.group(3)
    # Match array assignments of the form arr[i] := expr; or arr[i] = expr;
    array_match = re.match(r'(\w+)\[([^\]]*)\]\s*(:=|=)\s*(.*?)\s*;', line)
    if array_match:
        array_name, index, _, expr = array_match.groups()
        # Replace + with _ in index to create a valid variable name
        index = index.replace('+', '_')
        return f"{array_name}_{index}", expr  # Treat arr[i] as a unique variable
    return None, None

def convert_to_ssa(code_lines):
    var_versions = {}  # Tracks versions for both scalars and array elements (e.g., arr_j_1)
    ssa_output = []
    branches = []
    current_branch = []
    conditions = []
    after_if = []
    before_if = []
    inside = None
    final_exprs = []

    # Step 1: Parse code lines and categorize them
    for line in code_lines:
        stripped = line.strip()
        if re.match(r'^\d+\.', stripped):
            stripped = stripped[stripped.find('.') + 1:].strip()

        if stripped.startswith("if"):
            if inside == 'branch':
                branches.append((conditions[-1], current_branch))
                current_branch = []
            condition = re.search(r'\((.*)\)', stripped).group(1)
            conditions.append(condition)
            inside = 'branch'
        elif stripped.startswith("else if"):
            if inside == 'branch':
                branches.append((conditions[-1], current_branch))
                current_branch = []
            condition = re.search(r'\((.*)\)', stripped).group(1)
            conditions.append(condition)
            inside = 'branch'
        elif stripped.startswith("else"):
            if inside == 'branch':
                branches.append((conditions[-1], current_branch))
                current_branch = []
            conditions.append("else")
            inside = 'branch'
        elif stripped == "}":
            pass
        elif (':=' in stripped or '=' in stripped) and inside == 'branch':
            current_branch.append(stripped)
        elif (':=' in stripped or '=' in stripped) and inside is None:
            before_if.append(stripped)
        elif re.match(r'\w+\s*\(.*\);', stripped):
            final_exprs.append(stripped)
        else:
            after_if.append(stripped)

    if current_branch:
        branches.append((conditions[-1], current_branch))

    # Step 2: Process assignments before conditionals (initial assignments)
    for stmt in before_if:
        var, expr = parse_assignment(stmt)
        if var:
            version = 1
            var_versions[var] = [version]
            # Rewrite array accesses on the right side
            array_accesses = re.findall(r'(\w+)\[([^\]]*)\]', expr)
            for array_name, index in array_accesses:
                index = index.replace('+', '_')
                var_name = f"{array_name}_{index}"
                if var_name in var_versions:
                    expr = re.sub(rf'\b{array_name}\[{index}\]', f"{var_name}_{var_versions[var_name][-1]}", expr)
            ssa_output.append(f"{var}_{version} = {expr}")

    # Step 3: Process branches and assignments within them
    for i, (cond, stmts) in enumerate(branches):
        # Get current versions of all variables/array elements
        curr_versions = {v: var_versions[v][-1] for v in var_versions if var_versions[v]}
        cond_rewritten = cond

        # Rewrite array accesses in conditions (e.g., arr[j_1] -> arr_j_1_version)
        array_accesses = re.findall(r'(\w+)\[([^\]]*)\]', cond)
        for array_name, index in array_accesses:
            index = index.replace('+', '_')
            var_name = f"{array_name}_{index}"
            if var_name in curr_versions:
                cond_rewritten = re.sub(rf'\b{array_name}\[{index}\]', f"{var_name}_{curr_versions[var_name]}", cond_rewritten)

        # Rewrite scalar variables in conditions
        for v, ver in curr_versions.items():
            if not re.match(r'\w+_\w+', v):  # Only replace scalar variables, not array elements (already handled)
                cond_rewritten = re.sub(rf'\b{v}\b', f"{v}_{ver}", cond_rewritten)

        if cond != "else":
            ssa_output.append(f"φ{i + 1} = ({cond_rewritten})")
        else:
            if stmts:
                var, expr = parse_assignment(stmts[0])
                if var:
                    fallback_version = var_versions[var][-1]
                    else_value = f"{var}_{fallback_version - 1}"

                    prev_versions = {v: var_versions[v][-1] for v in var_versions if var_versions[v]}
                    # Rewrite array accesses in the expression
                    array_accesses = re.findall(r'(\w+)\[([^\]]*)\]', expr)
                    for array_name, index in array_accesses:
                        index = index.replace('+', '_')
                        var_name = f"{array_name}_{index}"
                        if var_name in prev_versions:
                            expr = re.sub(rf'\b{array_name}\[{index}\]', f"{var_name}_{prev_versions[var_name]}", expr)

                    # Rewrite scalar variables in the expression
                    for v, ver in prev_versions.items():
                        if not re.match(r'\w+_\w+', v):
                            expr = re.sub(rf'\b{v}\b', f"{v}_{ver}", expr)

                    version = len(var_versions.get(var, [])) + 1
                    var_versions.setdefault(var, []).append(version)
                    then_value = f"{var}_{version - 1}"

                    ternary_expr = f"(φ{i} ? {then_value} : {else_value})"
                    ssa_output.append(f"{var}_{version} = {ternary_expr}")

        for stmt in stmts:
            var, expr = parse_assignment(stmt)
            if var:
                prev_versions = {v: var_versions[v][-1] for v in var_versions if var_versions[v]}
                # Rewrite array accesses in the expression
                array_accesses = re.findall(r'(\w+)\[([^\]]*)\]', expr)
                for array_name, index in array_accesses:
                    index = index.replace('+', '_')
                    var_name = f"{array_name}_{index}"
                    if var_name in prev_versions:
                        expr = re.sub(rf'\b{array_name}\[{index}\]', f"{var_name}_{prev_versions[var_name]}", expr)

                # Rewrite scalar variables in the expression
                for v, ver in prev_versions.items():
                    if not re.match(r'\w+_\w+', v):
                        expr = re.sub(rf'\b{v}\b', f"{v}_{ver}", expr)

                version = len(var_versions.get(var, [])) + 1
                var_versions.setdefault(var, []).append(version)
                line = f"{var}_{version} = {expr}"
                ssa_output.append(line)

    # Step 4: Build phi expressions for variables with multiple versions
    def build_phi_expression(values, conditions, var_name):
        if len(values) == 1:
            return values[0]
        version = len(var_versions.get(var_name, [])) + 1
        result_var = f"{var_name}_{version}"
        var_versions.setdefault(var_name, []).append(version)

        if len(values) > 3:
            mid = len(values) // 2
            left_expr = build_phi_expression(values[:mid], conditions[:mid - 1], var_name)
            right_expr = build_phi_expression(values[mid:], conditions[mid - 1:], var_name)
            final_expr = f"({conditions[mid - 1]} ? {left_expr} : {right_expr})"
        else:
            final_expr = values[-1]
            for i in range(len(values) - 2, -1, -1):
                final_expr = f"({conditions[i]} ? {values[i]} : {final_expr})"

        ssa_output.append(f"{result_var} = {final_expr}")
        return result_var

    for var, versions in var_versions.items():
        if len(versions) > 1:
            phi_ver = len(versions) + 1
            ssa_versions = [f"{var}_{v}" for v in versions]
            phi_conditions = [f"φ{i + 1}" for i in range(len(versions) - 1)]
            phi_result_var = build_phi_expression(ssa_versions, phi_conditions, var)
            var_versions[var].append(phi_ver)

    # Step 5: Process final expressions (e.g., return statements)
    seen_exprs = set()
    for expr in final_exprs:
        original_expr = expr
        # Rewrite array accesses in the final expression
        array_accesses = re.findall(r'(\w+)\[([^\]]*)\]', expr)
        for array_name, index in array_accesses:
            index = index.replace('+', '_')
            var_name = f"{array_name}_{index}"
            if var_name in var_versions:
                expr = re.sub(rf'\b{array_name}\[{index}\]', f"{var_name}_{var_versions[var_name][-1]}", expr)

        # Rewrite scalar variables in the final expression
        for var in var_versions:
            if not re.match(r'\w+_\w+', var):
                expr = re.sub(rf'\b{var}\b', f"{var}_{var_versions[var][-1]}", expr)

        if expr not in seen_exprs:
            seen_exprs.add(expr)
            ssa_output.append(expr)

    return "\n".join(ssa_output)

def collect_loops_recursive(code_lines, i=0):
    loop_headers = {}
    while i < len(code_lines):
        line = code_lines[i].strip()
        loop_match = re.match(r"(for\s*\(.*;.*;.*\)|while\s*\(.*\))\s*\{?$", line)
        if loop_match:
            loop_header = loop_match.group(1)
            loop_headers[loop_header] = None

            loop_start_index = i + 1
            brace_level = 1 if "{" in line else 0
            loop_body = []
            j = loop_start_index

            while j < len(code_lines):
                body_line = code_lines[j]
                loop_body.append(body_line)
                brace_level += body_line.count("{")
                brace_level -= body_line.count("}")
                if brace_level == 0:
                    break
                j += 1

            nested_loops = collect_loops_recursive(loop_body)
            loop_headers.update(nested_loops)
            i = j + 1
        else:
            i += 1
    return loop_headers

def unroll_loop(code_lines, loop_unroll_counts, indent_level=0):
    indent = "    " * indent_level
    i = 0
    output = []
    while i < len(code_lines):
        line = code_lines[i].strip()
        loop_match = re.match(r"(for\s*\(.*;.*;.*\)|while\s*\(.*\))\s*\{?$", line)
        if loop_match:
            loop_header = loop_match.group(1)
            loop_start_index = i + 1
            loop_body_lines = []
            brace_level = 1 if "{" in line else 0
            end_index = -1
            while loop_start_index < len(code_lines):
                body_line = code_lines[loop_start_index]
                stripped_body_line = body_line.strip()
                if "{" in stripped_body_line:
                    brace_level += stripped_body_line.count("{")
                if "}" in stripped_body_line:
                    brace_level -= stripped_body_line.count("}")
                    if brace_level == 0:
                        end_index = loop_start_index
                        break
                loop_body_lines.append(body_line)
                loop_start_index += 1

            if brace_level == 0:
                n = loop_unroll_counts.get(loop_header, 1)
                unrolled_body = unroll_single_loop(loop_header, [lb.rstrip() for lb in loop_body_lines], n, indent, indent_level, loop_unroll_counts)
                output.extend(unrolled_body)
                i = end_index + 1
            else:
                output.append(f"{indent}Error: Unmatched braces in loop starting at line {i + 1}")
                i += 1
        else:
            output.append(f"{indent}{line}")
            i += 1
    return output

def unroll_single_loop(loop_header, loop_body_lines, n, indent, indent_level, loop_unroll_counts):
    unrolled_code = []
    if "for" in loop_header:
        match = re.search(r"for\s*\(([^;]*);([^;]*);([^)]*)\)", loop_header)
        if match:
            init, cond, inc = [part.strip() for part in match.groups()]
        else:
            unrolled_code.append(f"{indent}Warning: Could not parse for loop header: {loop_header}")
            return unrolled_code
    elif "while" in loop_header:
        match = re.search(r"while\s*\(([^)]*)\)", loop_header)
        if match:
            cond = match.group(1).strip()
            init = ""
            inc = ""
        else:
            unrolled_code.append(f"{indent}Warning: Could not parse while loop header: {loop_header}")
            return unrolled_code
    else:
        unrolled_code.append(f"{indent}Warning: Unrecognized loop type: {loop_header}")
        return unrolled_code

    if init:
        unrolled_code.append(f"{indent}{init};")

    # Nest each iteration inside the previous one
    current_indent_level = indent_level
    for i in range(n):
        current_indent = "    " * current_indent_level
        unrolled_code.append(f"{current_indent}if ({cond}) {{")
        inner_unrolled = unroll_loop(loop_body_lines, loop_unroll_counts, current_indent_level + 1)
        unrolled_code.extend(inner_unrolled)
        if inc:
            unrolled_code.append(f"{current_indent}    {inc};")
        current_indent_level += 1  # Increase indent for next nesting

    # Close all opened braces
    for j in reversed(range(n)):
        closing_indent = "    " * (indent_level + j)
        unrolled_code.append(f"{closing_indent}}}")

    return unrolled_code

# Main program
# print("Enter your code line by line. Press Enter on an empty line to finish:")
# input_code = []
# while True:
#     line = input()
#     if line.strip() == "":
#         break
#     # Strip line numbers (e.g., '1.', '123.') if present, otherwise keep line as-is
#     cleaned_line = re.sub(r'^\d+\.\s*', '', line).strip()
#     if cleaned_line:  # Only append non-empty lines
#         input_code.append(cleaned_line)

# # Step 1: Collect loops
# loops = collect_loops_recursive(input_code)

# # Step 2: Get unroll counts
# for loop in loops:
#     while True:
#         try:
#             count = int(input(f"How many times to unroll: {loop} ? "))
#             if count >= 0:
#                 loops[loop] = count
#                 break
#             else:
#                 print("Please enter a non-negative integer.")
#         except ValueError:
#             print("Please enter a valid integer.")

# # Step 3: Unroll loops
# unrolled_code = unroll_loop(input_code, loops)

# # Step 4: Print unrolled code
# print("\n=== CODE AFTER LOOP UNROLLING ===")
# for line in unrolled_code:
#     print(line)

# # Step 5: Convert to SSA
# print("\n=== SSA FORM ===")
# ssa_result = convert_to_ssa(unrolled_code)
# print(ssa_result)
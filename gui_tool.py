import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, simpledialog
from singleStaticForm import collect_loops_recursive, unroll_loop, convert_to_ssa
from z3_convertor import convert_ssa_to_smtlib, convert_to_z3_and_check
import re

class FMToolGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("FM GUI TOOL")
        self.root.geometry("1200x800")

        # Configure styles with colors
        self.style = ttk.Style()
        self.style.configure('TFrame', background='#e6f3ff')  # Light blue background
        self.style.configure('TButton', font=('Arial', 10, 'bold'), background='#4CAF50', foreground='#000000')  # Green button, black text
        self.style.configure('TLabel', font=('Arial', 10), background='#e6f3ff')
        self.style.configure('Header.TLabel', font=('Arial', 12, 'bold'), background='#e6f3ff', foreground='#003087')
        self.style.configure('TNotebook', background='#ffffff')
        self.style.configure('TNotebook.Tab', font=('Arial', 10), background='#bbdefb', foreground='#003087')
        # Main frame
        main_frame = ttk.Frame(root, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Set up tabs
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        # Input Tab
        self.input_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.input_frame, text="Input Programs")

        # Results Tab
        self.results_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.results_frame, text="Results")

        # === Input Frame ===
        # Mode selector and controls (centered)
        input_header = ttk.Frame(self.input_frame, style='TFrame')
        input_header.pack(fill=tk.X, padx=10, pady=5)

        control_frame = ttk.Frame(input_header, style='TFrame')
        control_frame.pack(anchor='center', pady=5)

        # Mode selector
        mode_frame = ttk.Frame(control_frame, style='TFrame')
        mode_frame.pack(side=tk.LEFT, padx=10)

        self.mode_var = tk.StringVar(value="Verify")
        mode_label = ttk.Label(mode_frame, text="Analysis Mode:", style='Header.TLabel')
        mode_label.pack(side=tk.LEFT, padx=5)

        modes = ttk.Combobox(mode_frame, textvariable=self.mode_var, 
                            values=["Verify", "Equivalence"], width=15, state="readonly")
        modes.pack(side=tk.LEFT, padx=5)
        modes.bind("<<ComboboxSelected>>", self.mode_changed)

        # Example Codes dropdown
        example_frame = ttk.Frame(control_frame, style='TFrame')
        example_frame.pack(side=tk.LEFT, padx=10)

        example_label = ttk.Label(example_frame, text="Example Codes:", style='Header.TLabel')
        example_label.pack(side=tk.LEFT, padx=5)

        self.example_var = tk.StringVar(value="Default")
        examples = ttk.Combobox(example_frame, textvariable=self.example_var, 
                               values=["Default", 
                                       "Example 1: If-Else", 
                                       "Example 2: Loop", 
                                       "Example 3: Bubble Sort",
                                       "Example 4: Array Sum",
                                       "Example 5: Max Element"], 
                               width=20, state="readonly")
        examples.pack(side=tk.LEFT, padx=5)
        examples.bind("<<ComboboxSelected>>", self.load_example)

        # Run button
        run_frame = ttk.Frame(control_frame, style='TFrame')
        run_frame.pack(side=tk.LEFT, padx=10)

        self.run_btn = ttk.Button(run_frame, text="RUN", command=self.run_tool, style='TButton')
        self.run_btn.pack(padx=5)
        # Program input area
        program_frame = ttk.Frame(self.input_frame, style='TFrame')
        program_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # Program 1
        prog_a_frame = ttk.Frame(program_frame, style='TFrame')
        prog_a_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)

        prog_a_label = ttk.Label(prog_a_frame, text="Program 1:", style='Header.TLabel')
        prog_a_label.pack(anchor='w', padx=5, pady=5)

        self.input1 = scrolledtext.ScrolledText(prog_a_frame, width=50, height=20, 
                                              font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.input1.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.input1.insert("1.0", """x := 3;
if (x < 5) {
    y := x + 1;
} else {
    y := x - 1;
}
assert(y > 0);""")

        # Program 2
        self.prog_b_frame = ttk.Frame(program_frame, style='TFrame')
        self.prog_b_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)

        self.prog_b_label = ttk.Label(self.prog_b_frame, text="Program 2:", style='Header.TLabel')
        self.prog_b_label.pack(anchor='w', padx=5, pady=5)

        self.input2 = scrolledtext.ScrolledText(self.prog_b_frame, width=50, height=20, 
                                              font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.input2.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.input2.insert("1.0", """# For equivalence mode, enter second program here
x := 3;
if (x < 5) {
    y := x + 1;
} else {
    y := x - 1;
}
assert(y > 0);""")

        # Initially hide Program 2 for Verify mode
        if self.mode_var.get() == "Verify":
            self.prog_b_frame.pack_forget()

        # === Results Frame ===
        results_notebook = ttk.Notebook(self.results_frame)
        results_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # Unrolled Code tab
        unrolled_frame = ttk.Frame(results_notebook, style='TFrame')
        results_notebook.add(unrolled_frame, text="Unrolled Code")

        unrolled_label = ttk.Label(unrolled_frame, text="Code After Loop Unrolling:", style='Header.TLabel')
        unrolled_label.pack(anchor='w', padx=5, pady=5)

        self.unrolled_display = scrolledtext.ScrolledText(unrolled_frame, width=100, height=20, 
                                                       font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.unrolled_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # SSA Form tab
        ssa_frame = ttk.Frame(results_notebook, style='TFrame')
        results_notebook.add(ssa_frame, text="SSA Form")

        ssa_label = ttk.Label(ssa_frame, text="SSA Form:", style='Header.TLabel')
        ssa_label.pack(anchor='w', padx=5, pady=5)

        self.ssa_display = scrolledtext.ScrolledText(ssa_frame, width=100, height=20, 
                                                   font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.ssa_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Analysis Results tab
        result_frame = ttk.Frame(results_notebook, style='TFrame')
        results_notebook.add(result_frame, text="Analysis Results")

        result_label = ttk.Label(result_frame, text="Analysis Results:", style='Header.TLabel')
        result_label.pack(anchor='w', padx=5, pady=5)

        self.result_display = scrolledtext.ScrolledText(result_frame, width=100, height=20, 
                                                      font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.result_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # SMT Code tab
        smt_frame = ttk.Frame(results_notebook, style='TFrame')
        results_notebook.add(smt_frame, text="SMT Code")

        smt_label = ttk.Label(smt_frame, text="Generated SMT Code:", style='Header.TLabel')
        smt_label.pack(anchor='w', padx=5, pady=5)

        self.smt_display = scrolledtext.ScrolledText(smt_frame, width=100, height=20, 
                                                   font=('Courier New', 10), bg='#ffffff', fg='#000000')
        self.smt_display.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

    def mode_changed(self, event=None):
        if self.mode_var.get() == "Verify":
            self.prog_b_frame.pack_forget()
        else:
            self.prog_b_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)

    def load_example(self, event=None):
        example = self.example_var.get()
        self.input1.delete("1.0", tk.END)
        if example == "Example 1: If-Else":
            self.input1.insert("1.0", """x := 3;
if (x < 5) {
    y := x + 1;
} else {
    y := x - 1;
}
assert(y > 0);""")
        elif example == "Example 2: Loop":
            self.input1.insert("1.0", """x := 0;
while (x < 4) {
    x := x + 1;
}
assert(x == 4);""")
        elif example == "Example 3: Bubble Sort":
            self.input1.insert("1.0", """for (i := 0; i < n; i := i + 1) {
    for (j := 0; j < n - i - 1; j := j + 1) {
        if (arr[j] > arr[j+1]) {
            temp := arr[j];
            arr[j] := arr[j+1];
            arr[j+1] := temp;
        }
    }
}
assert(for (i in range (n)):arr[i] < arr[i+1]);""")
        elif example == "Example 4: Array Sum":
            self.input1.insert("1.0", """sum := 0;
i := 0;
while (i < n) {
    sum := sum + arr[i];
    i := i + 1;
}
assert(sum >= 0);""")
        elif example == "Example 5: Max Element":
            self.input1.insert("1.0", """max := arr[0];
i := 1;
while (i < n) {
    if (arr[i] > max) {
        max := arr[i];
    }
    i := i + 1;
}
assert(for (i in range (n)):arr[i] <= max);""")
        if self.mode_var.get() == "Equivalence":
            self.input2.delete("1.0", tk.END)
            self.input2.insert("1.0", self.input1.get("1.0", tk.END))

    def run_tool(self):
        try:
            code1 = [line.strip() for line in self.input1.get("1.0", tk.END).strip().splitlines() if line.strip()]
            code2 = [line.strip() for line in self.input2.get("1.0", tk.END).strip().splitlines() if line.strip()]

            # Clear outputs
            self.unrolled_display.delete("1.0", tk.END)
            self.ssa_display.delete("1.0", tk.END)
            self.result_display.delete("1.0", tk.END)
            self.smt_display.delete("1.0", tk.END)

            # Switch to Results tab
            self.notebook.select(1)

            if self.mode_var.get() == "Verify":
                # Single program verification
                loops = collect_loops_recursive(code1)
                loop_unroll_counts = {}
                for loop in loops:
                    while True:
                        try:
                            count = simpledialog.askinteger("Unroll Loop", f"How many times to unroll:\n{loop}", 
                                                          parent=self.root, minvalue=0)
                            if count is not None:
                                loop_unroll_counts[loop] = count
                                break
                            else:
                                messagebox.showwarning("Warning", "Unroll count is required.")
                        except Exception:
                            messagebox.showerror("Error", "Invalid number entered.")

                unrolled_code = unroll_loop(code1, loop_unroll_counts)
                self.unrolled_display.insert(tk.END, "=== CODE AFTER LOOP UNROLLING ===\n")
                self.unrolled_display.insert(tk.END, "\n".join(unrolled_code))

                ssa_code = convert_to_ssa(unrolled_code).strip().split('\n')
                self.ssa_display.insert(tk.END, "=== SSA FORM ===\n")
                self.ssa_display.insert(tk.END, "\n".join(ssa_code))

                is_sat, z3_result = convert_to_z3_and_check(ssa_code)
                self.result_display.insert(tk.END, "=== Z3 ANALYSIS RESULTS ===\n")
                self.result_display.insert(tk.END, "\n".join(z3_result))

                smt_code, _, _ = convert_ssa_to_smtlib(ssa_code)
                self.smt_display.insert(tk.END, smt_code)

            else:
                # Program equivalence checking
                if not code2 or all(line.startswith('#') for line in code2):
                    messagebox.showerror("Error", "Please enter both programs for equivalence checking.")
                    return

                # Process Program 1
                loops1 = collect_loops_recursive(code1)
                loop_unroll_counts1 = {}
                for loop in loops1:
                    while True:
                        try:
                            count = simpledialog.askinteger("Unroll Loop", f"How many times to unroll:\n{loop}", 
                                                          parent=self.root, minvalue=0)
                            if count is not None:
                                loop_unroll_counts1[loop] = count
                                break
                            else:
                                messagebox.showwarning("Warning", "Unroll count is required.")
                        except Exception:
                            messagebox.showerror("Error", "Invalid number entered.")

                unrolled_code1 = unroll_loop(code1, loop_unroll_counts1)
                self.unrolled_display.insert(tk.END, "=== Program 1 (UNROLLED) ===\n")
                self.unrolled_display.insert(tk.END, "\n".join(unrolled_code1))

                ssa_code1 = convert_to_ssa(unrolled_code1).strip().split('\n')
                self.ssa_display.insert(tk.END, "=== Program 1 (SSA FORM) ===\n")
                self.ssa_display.insert(tk.END, "\n".join(ssa_code1))

                # Process Program 2
                loops2 = collect_loops_recursive(code2)
                loop_unroll_counts2 = {}
                for loop in loops2:
                    while True:
                        try:
                            count = simpledialog.askinteger("Unroll Loop", f"How many times to unroll:\n{loop}", 
                                                          parent=self.root, minvalue=0)
                            if count is not None:
                                loop_unroll_counts2[loop] = count
                                break
                            else:
                                messagebox.showwarning("Warning", "Unroll count is required.")
                        except Exception:
                            messagebox.showerror("Error", "Invalid number entered.")

                unrolled_code2 = unroll_loop(code2, loop_unroll_counts2)
                self.unrolled_display.insert(tk.END, "\n\n=== Program 2 (UNROLLED) ===\n")
                self.unrolled_display.insert(tk.END, "\n".join(unrolled_code2))

                ssa_code2 = convert_to_ssa(unrolled_code2).strip().split('\n')
                self.ssa_display.insert(tk.END, "\n\n=== Program 2 (SSA FORM) ===\n")
                self.ssa_display.insert(tk.END, "\n".join(ssa_code2))

                # Equivalence checking (simplified for demo)
                is_sat1, z3_result1 = convert_to_z3_and_check(ssa_code1)
                is_sat2, z3_result2 = convert_to_z3_and_check(ssa_code2)

                self.result_display.insert(tk.END, "=== EQUIVALENCE ANALYSIS ===\n\n")
                self.result_display.insert(tk.END, "Program 1 Results:\n")
                self.result_display.insert(tk.END, "\n".join(z3_result1) + "\n\n")
                self.result_display.insert(tk.END, "Program 2 Results:\n")
                self.result_display.insert(tk.END, "\n".join(z3_result2) + "\n\n")

                if is_sat1 == is_sat2:
                    self.result_display.insert(tk.END, "=== SUMMARY ===\nPrograms may be equivalent (same satisfiability).\n")
                else:
                    self.result_display.insert(tk.END, "=== SUMMARY ===\nPrograms are NOT equivalent (different satisfiability).\n")

                smt_code1, _, _ = convert_ssa_to_smtlib(ssa_code1)
                smt_code2, _, _ = convert_ssa_to_smtlib(ssa_code2)
                self.smt_display.insert(tk.END, "=== Program 1 SMT CODE ===\n")
                self.smt_display.insert(tk.END, smt_code1 + "\n\n")
                self.smt_display.insert(tk.END, "=== Program 2 SMT CODE ===\n")
                self.smt_display.insert(tk.END, smt_code2)

        except Exception as e:
            messagebox.showerror("Error", f"An error occurred: {str(e)}")
            import traceback
            traceback.print_exc()

if __name__ == '__main__':
    try:
        root = tk.Tk()
        app = FMToolGUI(root)
        root.mainloop()
    except Exception as e:
        print(f"Fatal error: {e}")
        import traceback
        traceback.print_exc()
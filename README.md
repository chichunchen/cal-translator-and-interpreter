# cal-translator-and-interpreter
Transate a Fortan-like language to AST and interpret the AST with a REPL (Read Evaluate Print Loop). In addition, it supports several run-time analysis for the interpreter.

## What has done
- Omit AST in memory
- Translate to C
- Runtime Program analysis
    - Unexpected end of input (attempt to read when there’s nothing there)
    - Non-numeric input (the extended calculator language accepts only integers)
    - Use of an uninitialized variable—one to which a value has not yet been assigned (read-ing counts as assignment). 
    - Divide by zero
    
## Demo
```
[ocamlshell@454]$ read n cp := 2 do check n > 0 found := 0 cf1 := 2 cf1s := cf1 * cf1 do check cf1s <= cp cf2 := 2 pr := cf1 * cf2 do check pr <= cp if pr == cp found := 1 fi cf2 := cf2 + 1 pr := cf1 * cf2 od cf1 := cf1 + 1 cf1s := cf1 * cf1 od if found == 0 write cp n := n - 1 fi cp := cp + 1 od
10
2
3
5
7
11
13
17
19
23
29
[ocamlshell@454]$ read a write a * 100
100
10000
[ocamlshell@454]$ gg
syntax error: expected := ; saw $$
type again!
[ocamlshell@454]$ Bye :)
```

## Details

### File Structure
- `translator.ml`
    - implement both translator and interpreter
    - `ocaml translator` print no output, we call the testing in `test.ml`
- `test.ml`
    - execute the test in translator
    - execute: `ocaml test.ml`
- `eval.ml`
    - implement the read eval print loop using our interpreter
    - execute: `ocaml eval.ml`
    
### AST
create the ast tree recursively from the given parse tree
- ast_ize_P
    - recursively calls `ast_ize_SL sl` until match PT_term "$$"
- ast_ize_SL
    - recursively calls `ast_ize_S s` until the statement lists is empty
- ast_ize_S
    - match the parse tree by using the pattern matching
        - when match PT_nt ("S", [PT_id lhs; PT_term ":="; expr])
            - construct AST_assign(lhs, (ast_ize_expr expr))
        - when match PT_nt ("S", [PT_term "read"; PT_id id])
            - construct AST_read(id)
        - when match PT_nt ("S", [PT_term "write"; expr])
            - construct AST_write(ast_ize_expr expr)
        - when match PT_nt ("S", [PT_term "if"; expr; sl; PT_term "fi"])
            - construct AST_if(ast_ize_expr expr, ast_ize_SL sl)
        - when match PT_nt ("S", [PT_term "do"; sl; PT_term "od"])
            - construct AST_do(ast_ize_SL sl)
        - when match PT_nt ("S", [PT_term "check"; expr])
            - construct AST_check(ast_ize_expr expr)
- ast_ize_expr
    - expression is an R, E, T, or F so match each case
        - PT_nt ("R", [e; et])
            - construct R by calling ast_ize_reln_tail
            - pass `ast_ize_expr e` as lhs
            - pass et as rhs
        - PT_nt ("E", [t; tt])
            - construct E by calling ast_ize_expr_tail
            - pass `ast_ize_expr t` as lhs
            - pass tt as rhs
        - PT_nt ("T", [f; ft])
            - construct E by calling ast_ize_expr_tail
            - pass `ast_ize_expr f` as lhs
            - pass ft as rhs
        - PT_nt ("F", [PT_id id])
            - construct AST_id(id)
        - PT_nt ("F", [PT_num num])
            - construct AST_num(num)
        - PT_nt ("F", [PT_term "("; expr; PT_term ")"])
            - construct by calling ast_ize_expr(expr)
- ast_ize_reln_tail
    - ET -> ro E ET
        - match ro and construct AST_binop (ro, lhs, ast_ize_expr rhs)
- ast_ize_expr_tail
    - ast_ize_expr_tail has 2 arguments, lhs and tail, and lhs is constructed by ast_ize_e
    - expression tail can be
        - TT -> ao T TT
            - call ast_ize_expr_tail by passing (AST_binop(ao, lhs, ast_ize_expr t)) and tt
        - TT -> epsilon
            - return lhs
        - FT -> mo F FT
            - call ast_ize_expr_tail by passing (AST_binop ("*", lhs, ast_ize_expr f)) and ft
        - FT -> epsilon
            - return lhs
            
### Translate to C
Translate the calculator program into C code using AST and implement some dynamic error checks.

- remove_duplicates xs
    - This function removes duplicated items in a list.
    - It uses `cons_uniq: 'a list -> 'a -> 'a list = <fun>` to `fold_left` the list.
- code_gen_preface
    - This is a string of necessary libraries and functions for the target C program.
    - In `int getint()`, we check unexpected end of input and non-numeric input.
    - `int putint(int n)` is just a simple `printf("%d\n", n);`.
    - `int zero_breaker(int n)` captures divide by 0 error.
- rec translate (ast: ast_sl) : string * string
    - Get AST and translate the calculator program into C.
    - Returns a tuple of string * string. First string is a warning message for assigned but never used variables. Second is our translated C program.
    - The translate results are printed in the `translator ()` function, where
        - t1, t2, t3, t4 are our demo inputs. For example, we call `print_string (snd (translate t1))` and the translating result of t1 is output to the command line.
        - t1 contains a variable that is assigned but never used, and a variable that is used but not assigned.
        - `translate` returns a tuple of `string * string`, so we use `snd` here to get the result, which is the second of the tuple.
    - We first traverse the AST to get all assigned and used variables.
        - rec traverse_assigned_variables (ast:ast_sl) : string list
            - We match each item in the AST (a list) in order
            - If we get a match of `AST_assign` or `AST_read`, we keep the current `id` and call the function recursively on the rest of list.
            - If we match `AST_if` or `AST_do`, we call the function on stmt_list and on tail of list, and concatenate them together.
            - Otherwise, just call the function recursively on the tail of list.
        - rec traverse_used_variables is much the same, except that we only keep `id`s in expr parts.
        - `var_list_assigned` and `var_list_used` store the variable lists obtained from the two traverse functions. 
        - assign_error and unused warning_both take `var_list_assigned` and `var_list_used` as parameters and generate messages ("" for no error/warning).
        - The function returns a tuple (string * string), where the second element is the target C program.
        - In the very beginning of `main()`, we write an if clause for warning message, which is always printed when there are variables assigned but never used.
        - Following comes another if clause that raises used without assign error when there exists one.


- translate_sl (ast: ast_sl) : string
    - start translation from stmt_list
    - if matches [] then return ""
    - if matches h::t then translate_s h (h is stmt) and translate_sl t (t is stmt_list) and concatenate them (^)
- translate_s (s: ast_s) : string
    - matches assign, read, write, if, do, check statements, and go on translating
    - translate_assign (id:string) (expr:ast_e) : string
        - translate into `id = expr;`
    - translate_read (id:string) : string
        - translate into `id = getint();`
    - translate_write (expr:ast_e) : string
        - translate into `putint(expr);`
    - translate_if (expr:ast_e) (sl:ast_sl) : string
        - translate into `if (expr) {stmt_list}`
    - translate_do (ast:ast_sl) : string
        - translate into `while(1) {stmt_list}`
    - translate_check (expr:ast_e) : string
        - translate into `if(!expr) break;`
- translate_expr (expr: ast_e) : string
    - matches num, id, or binop.
    - if matches binop, if the op is "/" then we wrap the divisor with the zero_breaker function mentioned before. It is not so easy to just add some "if" clauses here to catch the divided by zero error.
    
### Interpreter
- Execute directly by using AST without producing any code
- interpert (ast:ast_sl) (stdin:string) : string
    - get ast and standard input as arguments and return the output of the program(standard output)
    - first, convert the standard input from a string to a list of string which using space as a seperator
        - example: interpreter(ast, "0 0")
            - we get ["0", "0"] as stdin
    - second, call interpret_sl by passing ast, standard input, memory list(initiated as []), and a standard output list(initiated as [])
    - join the output string list from interpret_sl and then return
- interpret_sl
    - get status * memory * string list * string list as arguments, which is the same as the interface in A3 initial code from last year
    - call interpret_s until the status is not `Good` or the statement list is empty
- interpret_s
    - match ast structure to and call interpret_assign, interpret_read, interpret_write, interpret_if, interpret_do, or interpret_check
- interpret_assign
    - firstly, check if the id we want to assign is in memory list, if it is, we drop it and add the new one, if it is not in memory list, then we simply append it to the memory list
- interpret_read
    - if there is no id in AST_read then print "no input in read" and return a `Bad` status
    - if the input is not a integer, then return a `Bad` status
    - if the input is a integer, much as interpret_assign, we append the tuple of id and value to memory list
- interpret_write
    - if the interpret_expr function returns a `Good` status, then we append the result to standard ouput
    - if the interpret_expr function returns a `Bad` status, we propagate the `Bad` status up, therefore, the interpret_sl function can terminate the interpretation
- interpret_if
    - if the return value of expression is not zero, then we call interpret_sl
    - if the return value is zero, then we return (Good, memorylist, input, output)
    - if the interpret_expr function returns a `Bad` status, we propagate the `Bad` status up, therefore, the interpret_sl function can terminate the interpretation
- interpret_do
    - call interpret_sl and if the status returns from it is `Good`, then we call interpret_do again
    - if the status returns from interpret_sl is `Done`, then we knows that the loop is broke by interpret_check, and we return (Good, memorylist, input, output)
    - if the status returns from interpret_sl is`Bad`, we propagate the `Bad` status up, therefore, the interpret_sl function can terminate the interpretation
- interpret_check
    - if the expression returns 0 then we break the loop by return (Done, memorylist, input, output)
    - if the expression is not zero then return (Good, memorylist, input, output)
- interpret_expr
    - if the expression is simply num, then just return the value
    - if the expression is a id, then we update that id-value pair in memory as used, which is for detecting the variable usage
    - if the expression is a binop, then we first evaluated the lhs and if the return value is not an Error, we continue to evaluate the rhs, and then we check the value again, if both is good, return the result
        - we check the divide by zero issue here by checking if both the op is `/` and the rhs is `0`
        
### Eval
- seperate to `eval.ml`
- execute by typing `ocaml eval.ml`
- example
    - the input after the shell prompt is the prime_prog without newline, and then we enter `10`
    - the last is the standard output
    - the second prompt shows that we can interpret the program repeatly just as we use some real-world interpreter
    - if the program is not valid, `eval` catch the error and ask user to type again!
    - type eof(ctrl-d) to exit the program

### More
https://hackmd.io/IwZg7AJmYEwIYFpgAYDGBOBAWARgNhwXQwFNtgAOOVcHAVggoDMg#

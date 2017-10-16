# A3 Translator

### TODO
- [X] AST
- [X] translate to C
    - [X] unexpected end of input (attempt to read when there’s nothing there)
    - [X] non-numeric input (the extended calculator language accepts only integers)
    - [X] "Warning: Assigned but never used" check use of an uninitialized variable—one to which a value has not yet been assigned (read-ing counts as assignment). 
    - [X] divide by zero (C's automatically generated “floating exception” is not helpful:
      you want something like “divide by zero at line 23”). (Done, yet not know if this method violates the
      "not taking advantage of imperative language features" rule.)
- [X] interpret via ast
    - [X] unexpected end of input (attempt to read when there’s nothing there)
    - [X] non-numeric input (the extended calculator language accepts only integers)
    - [X] use of an uninitialized variable—one to which a value has not yet been assigned (read-ing counts as assignment). 
    - [X] divide by zero
    - [ ] Generate warning messages at the end of execution for any values that were assigned into a variable and then never used. (Extra credit of last year)

### Details
https://hackmd.io/IwZg7AJmYEwIYFpgAYDGBOBAWARgNhwXQwFNtgAOOVcHAVggoDMg#

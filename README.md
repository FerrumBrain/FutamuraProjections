Run [main.cpp](main.cpp) providing path to the input file
1. For the turing machine interpreter, you can use [turing.in](turing.in)
2. For the specializer test, you can use [mix_easy.in](mix_easy.in)
3. For first Futamura projection use [first_projection.in](first_projection.in)
4. For second Futamura projection use [second_projection.in](second_projection.in)
5. For compiler test (it uses output of second projection) you can use [compiler.in](compiler.in)
6. For third Futamura projection use [third_projection.in](third_projection.in)

P.S. for each run, you need to adjust `.in` file so that it contains correct filepath

General explanation of how to run:
1. Create file with your flowchart code
2. Create file that has address of you code file on the first line and all the inputs (each in one line) separated by lines
3. Build and run main.cpp and provide your file from p.2 as input

Modifications of a language:
1. List: `(a $ b $ ... $ z)`. `$` as a separator, list is in braces
2. Literals: `%abacaba/`. Starts with `%` and ends with `/`
3. Labels: `#label!`. Starts with `#` and ends with `!`
4. Program state: `[a $ %1/ $ b $ %2/]`. `$` as a separator, state is in square braces. Should be: name, value, name, value ...
5. Flowchart program should start with `{` and end with `}`
6. Turing machine program should start with `<` and end with `>`
7. `:=` is an assignment operator and should be at the beginning of the line: `:= x %5/;`
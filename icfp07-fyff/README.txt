To run the tests using the model:
---------------------------------

 1. Open "tests.ss" in DrScheme

 2. Change DrScheme's current language to "(module ...)"

 3. Click "Run"

The first time you do this, DrScheme will pause for a while to
download and install PLT Redex, which is requested at the top
of the "tests.ss" file (and all the other files).

Afterward, in the REPL window that appears to show the output, you can
try your own expressions using the `show' function. The program
`call/cc-loop' is helpfully defined, so that you can try

 (show call/cc-loop)


To read the program:
--------------------

After a quick look at "grammar.ss", read "reduce.ss". If you become
interested in a metafunction, see "meta.ss"

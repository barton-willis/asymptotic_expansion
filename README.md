# Asymptotic expansions

This package extends the Maxima function `stirling0.` The function `stirling0` is used internally by the limit code to find asymptotic expansions for gamma, factorial, and polylogarithm expressions. The `asymptotic_expansion` package extends `stirling0` to handle more cases. There are no user-level functions in this package.

The `asymptotic_expansion` package and the three associated files that are described below are _not_ ready for general work. The three associated files are:

* `simplimexpt` is a new implementation of the function that computes the limit of an exponential expression. 

* `my-infsimp` is a new implementation of the functions `simpab`, `simpinf`, and `infsimp`.  Each of these three functions are used internally by the limit code to do extended real arithmetic. The intent is to make these functions handle more cases and to make these functions easier to extend and fix.

* `continuous_p` is a function that attempts to determine if an expression is continuous.


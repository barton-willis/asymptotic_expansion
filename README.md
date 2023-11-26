# Asymptotic expansions

This is Maxima code (written in Common Lisp) for finding asymptotic expansions. There are no user-level functions in this code; the sole purpose of this code is for computing limits. 

This package extends the Common Lisp (CL) function `stirling0` that does 
asymptotic expansions for gamma, factorial, and polylogarithm functions.
The `asymptotic_expansion` package extends `stirling0` to handle 
more functions (and effectively renames it `asympototic-expansion`).

At one time, the package `asymptotic_expansion` fixed several testsuite bugs. Most (likely all) of these fixes were blended into Maxima. As of November 2023, using this package _causes_ several testsuite failures and fixes _no_ failures.

At one time, this code modified the CL function `gruntz1` to call the function `asymptotic-expansion` before entering the main code for computing limits.

Additionally, this repository has three related files that are not a part of the
asymptotic expansion package; these files are:

* `simplimexpt` is new implementation of the function that computes the limit of an exponential function. Running the testsite with `simplimexpt` fixes seven rtest_limit_extra failures, and it also causes 55 testsuite failures (some of these
55 failures are syntatic, not semantic failures) plus one
test that triggers multiple calls to asksign.

* `my-infsimp` is an effort at a new implementation of the function `simpinf.` 
The function `simpinf` does extended real arithmetic; for example, it should
simplify `ind + 1`  to `ind.` The testsuite stalls during `rtestsum` when this file has been loaded, but removing one test from `rtestsum` allows the entire testsuite to finish. Doing so, fixes `rtest_limit_extra` failures 111, 125, 267, and 317. Additionally, it causes seven testsuite failures, but for some of these, the expected results are sub optional and the result using `my-infsimp` are better.

* `continuous_p` is a function that attempts to determine if an expression is continuous.


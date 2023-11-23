# Asymptotic expansions

This is Maxima code (written in Common Lisp) for finding asymptotic expansions. There are no user-level functions in this code--the sole purpose of this code is for computing limits. 

At one time, this package fixed several testsuite bugs. Most (likely all) of these
fixes were blended into Maxima. As of November 2023, using this package
_causes_ several testsuite failures and fixes no failures.

This code modifies the Common Lisp (CL) function `stirling0.` This function is called by various functions in the limit code. Possibly the original intent was that `stirling0` would only apply the Stirling approximation for the gamma function, but over the years, it gained other duties. 

At one time this code modified the CL function `gruntz1` to call the function `asymptotic-expansion` before entering the main code for computing limits.

Additionally, the file `simplimexpt` is a new implementation of the function that computes the limit of an exponential function.

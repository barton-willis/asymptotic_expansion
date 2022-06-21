# Asymptotic expansions

This is Maxima code (written in Common Lisp) for finding asymptotic expansions of various functions, including bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, polylogarithm, and  polygamma functions. 

The purpose of this code is for computing limits. Possibly the function `asymptotic-expansion` could be promoted to a user level function, but for now it isn't intended to be used that way.

This code hooks into the limit code in two ways.  First it modifies the CL function `stirling0`  that is called by various functions in the limit code. Possibly the original  intent was that `stirling0` would only apply the Stirling approximation, but over the years, it gained other duties. Second it modifies the CL function `gruntz1` to call the function  `asymptotic-expansion` before entering the main code for computing limits.


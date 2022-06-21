# Asymptotic expansions

This is Maxima code for finding asymptotic expansions of various functions, including bessel_j, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, polylogarithm, and 
polygamma functions. 

The purpose of this code is for computing limits. Possibly the function `asymptotic-expansion` could be promoted to a user level function, but for now it isn't intended to be a used that way.

This code hooks in the the limit code two ways.  First it modifies the CL function `stirling0.`  And second it modifies the CL function `gruntz1` to call the function  `asymptotic-expansion` before entering the main code for computing limits.


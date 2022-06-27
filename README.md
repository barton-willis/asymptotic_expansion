# Asymptotic expansions

This is Maxima code (written in Common Lisp) for finding asymptotic expansions of various functions, including bessel_j, bessel_k, erf, erfc, expintegral_e1, expintegral_ei, gamma, factorial, polylogarithm, and polygamma functions. 

The purpose of this code is for computing limits. There are no functions in this code that are intended to be user-level functions.

This code hooks into the limit code in two ways. First it modifies the Common Lisp (CL) function `stirling0.`  This function is called by various functions in the limit code. Possibly the original intent was that `stirling0` would only apply the Stirling approximation, but over the years, it gained other duties. Second it modifies the CL function `gruntz1` to call the function  `asymptotic-expansion` before entering the main code for computing limits. Additionally it makes some assumptions about the limit variable that may help the simplifier.

Here is a sample of limits that fail with standard Maxima, but work with this package:

```
(%i3)	limit(gamma(x)/gamma(1/x),x,0,plus);
(%o3) 0

(%i4)	gruntz(atan2(x^2-2,x^3-2*x),x,sqrt(2),minus);
(%o4) atan(1/sqrt(2))-%pi

(%i6)	block([domain:'complex],limit((2^(2*x+1)+(2^x*x^100)^(3/2))/(4^x-100*2^x),x,inf));
(%o6) 2
```


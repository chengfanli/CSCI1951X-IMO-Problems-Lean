## The Formalization of 1968 IMO Q5

The final project for CSCI 1951X: Formal Proof and Verification.

The problem comes from [IMO's official archive](https://www.imo-official.org/problems.aspx) and has not yet been formalized in [this repo](https://github.com/leanprover-community/mathlib4/tree/master/Archive/Imo), as described in the project description.



#### Problem Description

Let $f$ be a real-valued function defined for all real numbers $x$ such that, for some positive constant $a$, the equation 

​                                             $ f(x + a) = \frac{1}{2} + \sqrt{f(x) - [f(x)]^2} $

holds for all \( x \).  

(a) Prove that the function $f$ is periodic (i.e., there exists a positive number $b$ such that  $f(x + b) = f(x)$ for all $x$.   

(b) For $a = 1$, give an example of a non-constant function with the required properties.



#### Solution

(a) Since we can observe that 

​     $ f(x + a)(1 - f(x + a)) = \frac{1}{4} - (f(x) - f(x)f(x)) = (f(x) - \frac{1}{2})^2$

​     Then

​     $f(x + 2a) = \frac{1}{2} + \sqrt{(\frac{1}{2} - f(x))^2} = f(x)$

​     So that we can prove that there exists a positive number $b = 2a$ such that  $f(x + b) = f(x)$ for all $x$

(b) We can construct the following $f$

​	$  f(x) = \begin{cases} 1 & \text{if } \lfloor x \rfloor \text{ is even}, \\ \frac{1}{2} & \text{if } \lfloor x \rfloor \text{ is odd}. \end{cases}$

​      And we can verify that 

​	$ f(x + 1) = \frac{1}{2} + \sqrt{f(x) - [f(x)]^2} $



#### Formalization

A formal proof of this problem is located in the `./LoVe/src/1968-IMO-Q5.lean`.

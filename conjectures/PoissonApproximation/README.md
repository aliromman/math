# The largest binomial–Poisson discrepancy occurs at zero

For every positive integer $n$ and every $0\le\lambda\le1$,

$$
d_K\!\left(\operatorname{Bin}(n,\lambda/n),\operatorname{Pois}(\lambda)\right)
=e^{-\lambda}-(1-\lambda/n)^n.
$$

Here $d_K$ is the largest absolute difference between the two cumulative probabilities over all real thresholds. The probability of getting zero successes gives the exact error. At $n=2$ and $\lambda=1$, for example, the distance is $e^{-1}-1/4$.

Nagaev and Chebotarev conjectured this formula for $\lambda=1$ in equation (84). They also identified the resulting limit $n d_K\to1/(2e)$. Their separate conjecture (82) compares different sample sizes at a fixed success probability. [Original article, §6](https://doi.org/10.3390/math9080845)

## Proof at mean one

Write $B_j$ and $P_j$ for the binomial and Poisson probabilities of $j$ successes, $D_j=\sum_{i=0}^j(B_i-P_i)$, and $q=1-1/n$. First take $n\ge2$. We have $D_0=q^n-e^{-1}<0$. The mass ratios obey

$$
\frac{B_1}{P_1}=\frac{B_2}{P_2}=e q^{n-1}>1,
\qquad
\frac{B_{j+1}/P_{j+1}}{B_j/P_j}=\frac{n-j}{n-1} \quad (j<n).
$$

For $3\le j\le n$, the factors $n,n-1,\ldots,n-j+1$ have arithmetic mean at most $n-1$. Their product is at most $(n-1)^j$. Hence $B_j/P_j\le e q^n<1$. For $j>n$ the binomial mass vanishes. Thus the cumulative difference rises from $D_0$ to $D_2$ and then decreases to zero.

It remains to compare $D_2$ and $-D_0$. Substituting the first three masses gives the equivalent inequality

$$
e q^{n-1}\left(1-\frac{4}{7n}\right)\le1.
$$

For $n\ge3$, the elementary bound $\log v\ge 2(v-1)/(v+1)$ for $v\ge1$, with $v=n/(n-1)$, gives $e q^{n-1}\le\sqrt{n/(n-1)}$. The displayed inequality follows from $(7n-4)^2\le49n(n-1)$, which reduces to $16\le7n$. At $n=2$ it follows from $e<14/5$. At $n=1$ the binomial law has all its mass at one, and $e<3$ gives the result.

## All means up to one

Set $r=\lambda$ and $q=1-r/n$. For $n\ge2$, the same falling-product bound gives $B_j\le P_j$ for $j\ge3$, since $n-1\le nq$. Also $B_1\ge P_1$, as $(n-1)\log(1/q)\le(n-1)r/(n-r)\le r$. It suffices to check $D_0+D_1\le0$ and $D_0+D_2\le0$.

Put $y=3r^2/(6n-4r)$ and $v=1+y+y^2/2$. The logarithmic bound

$$
-\log(1-z)-z\ge\frac{3z^2}{6-4z}\quad(0\le z<1)
$$

follows by differentiation. The derivative of the difference is $4z^3/((1-z)(6-4z)^2)$. It gives $e^{-r}/q^n\ge e^y\ge v$. The two comparisons now follow from

$$
\begin{aligned}
2q^2+rq &\le q^2(2+r)v,\\
4q^2+2rq+(1-1/n)r^2 &\le q^2(4+2r+r^2)v.
\end{aligned}
$$

To check the algebra, set $r=1/(1+a)$ and $n=2+b$. Clearing positive denominators in each right side minus its left side leaves a polynomial in $a,b$ with nonnegative coefficients. The value $r=0$ gives equality. At $n=1$, the comparison reduces to $(2-r)e^r\le2+r$. The exponential series gives $e^r\le1+r+r^2/2+r^3/4$ on $[0,1]$, and multiplication by $2-r$ gives $2+r-r^4/4$.

## Prior work and verification

Adell, Anoz and Lekuona proved the formula for $\lambda\le2-\sqrt2$ and gave an algorithm for larger means, together with an asymptotic location of the maximum. Their Corollary 1.5 already implies the scaled limit at $\lambda=1$. Searches of the original conjecture, its citations and exact binomial–Poisson distance results found no earlier proof of (84) for all $n$ or of the formula throughout $[0,1]$. OpenAI Codex developed the proof and its Lean formalization. [Earlier article](https://doi.org/10.1155/2009/965712)

Lean uses Mathlib’s binomial and Poisson probability measures. It takes the supremum over all real thresholds and proves the scaled limit. [Statement](Statement.lean) · [General theorem and resolution](Solution.lean) · [Limit](Limit.lean)

```sh
lake exe cache get
lake build conjectures.PoissonApproximation.Solution
lake env leanchecker conjectures.PoissonApproximation.Solution
```

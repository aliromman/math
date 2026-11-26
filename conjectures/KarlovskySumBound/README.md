# The sharp sum bound for distinct factors

Five different positive integers whose product is 23 times their sum can add up to at most 240. The numbers $1,2,3,4,230$ attain that limit. The same bound has a single formula for every number of distinct factors and every positive integer multiplier. This proves Petr Karlovsky’s Conjecture 2. [Original paper, §9](https://doi.org/10.3390/math9212779)

Suppose $x_1<\cdots<x_n$ are positive integers, $n\ge4$, and $\prod x_i=F\sum x_i$ for a positive integer $F$. Write $k=n-2$, $K=k!$, and $C=Kk(k+1)/2$. Then

$$
\sum_{i=1}^n x_i\le\frac{(F+1)(F+1+C)}K.
$$

For each $y>k$, put $F=Ky-1$. The tuple $(1,2,\ldots,k,y,F(k(k+1)/2+y))$ attains the bound. Thus the estimate is sharp for infinitely many multipliers at every order.

## Proof

Let $Q,T$ be the product and the sum of the first $k+1$ entries, and put $z=x_n$. The equation gives $(Q-F)z=FT$. The integer $d=Q-F$ is positive. Since $T\le(k+1)z$, it satisfies $d\le (k+1)F$.

Write $y=x_{k+1}$ and $x_i=i+u_i$ for $i\le k$. In the expansion of $\prod_{i=1}^k(i+u_i)$, the constant term is $K$ and the linear coefficient of $u_i$ is $K/i\ge K/k$. All higher terms are nonnegative. Multiplying by $y>k$ gives $KT\le Q+C$.

The full sum is $S=QT/d$. Combining the two estimates gives

$$
KS\le\frac{(F+d)(F+d+C)}d\le(F+1)(F+1+C).
$$

For the last inequality, multiply by $d$. The difference between the right and left numerators is $(d-1)(F(F+C)-d)$. Both factors are nonnegative because $C\ge k+1$ and $d\le (k+1)F$.

## Source and verification

Petr Karlovsky, *Diophantine Equations Relating Sums and Products of Positive Integers*, Mathematics **9** (2021), 2779, §9, Conjecture 2, equation (18). The paper established a larger bound allowing repeated terms. Bukor, Filakovszky and Tóth studied the equation with repeated terms and estimated solution counts. Sándor and Zakarczemny bounded products for $F=n^h$ with repeated terms. Searches for the conjecture, author, and distinct-term bound found no earlier proof. [Karlovsky](https://www.mdpi.com/2227-7390/9/21/2779) · [Bukor, Filakovszky and Tóth](https://journals.us.edu.pl/index.php/AMSIL/article/view/14169) · [Sándor and Zakarczemny](https://arxiv.org/abs/2611.20799)

The proof accepts every increasing positive integer tuple from equation (17). Its estimate for the partial product also appears in the separate proof of Karlovsky’s equality conjecture. OpenAI Codex developed and formalized the argument. [Statement](Statement.lean) · [Proof](Solution.lean)

```sh
lake exe cache get
lake build conjectures.KarlovskySumBound.Solution
lake env leanchecker conjectures.KarlovskySumBound.Solution
```

# Proof of Karlovsky’s Conjecture 3 on attainment of the distinct-factor sum bound

Fix $n\ge4$, put $k=n-2$, and let $K=k!$ and $t=k(k+1)/2$. Among distinct positive integers whose product is $F$ times their sum, Karlovsky’s bound is attained **exactly when $F=Ky-1$ for an integer $y>k$**. For every such $F$, the only maximizing tuple in increasing order is

$$
(1,2,\ldots,k,\;y,\;F(t+y)).
$$

This proves Karlovsky’s Conjecture 3 and identifies every equality case. For five terms the condition is $F\equiv5\pmod6$ and $F\ge23$. At $F=23$, the unique maximizer is $(1,2,3,4,230)$, of sum 240. [Original conjecture, §9](https://doi.org/10.3390/math9212779)

## Proof

Write $z$ for the largest entry, $y$ for the next largest, and $Q,T$ for the product and sum of the entries other than $z$. Then $d=Q-F$ is a positive integer and $dz=FT$. The inequality $T\le(k+1)z$ gives $d\le(k+1)F$. Set $C=Kt$.

Write the smallest $k$ entries as $i+u_i$ with $u_i\ge0$. Expanding their product gives at least $K+\sum_i(K/i)u_i$. As $y>k$, multiplying by $y$ yields $KT\le Q+C$, strictly if any $u_i>0$. For the full sum $S$ it follows that

$$
KS=\frac{QKT}d\le\frac{(F+d)(F+d+C)}d\le(F+1)(F+1+C).
$$

The final inequality, multiplied by $d$, has difference $(d-1)(F(F+C)-d)$. Since $C\ge k+1$ and $d\le(k+1)F$, its second factor is positive. Equality therefore forces $d=1$ and all $u_i=0$. Now $F+1=Q=Ky$ and $z=FT=F(t+y)$. Conversely, these terms are positive and strictly increasing, their product is $F$ times their sum, and both inequalities are equalities. Their sum is a maximum over every other solution.

## Source and verification

Petr Karlovsky, *Diophantine Equations Relating Sums and Products of Positive Integers*, Mathematics **9** (2021), 2779, §9, Conjecture 3, equation (19). The author predicted the complete set of multipliers and exhibited numerical examples. We prove necessity, sufficiency and uniqueness. Searches by author, equation and distinct-term equality conditions found no earlier proof. Earlier work on repeated terms gives estimates on their counts or on their largest coordinates. [Karlovsky](https://www.mdpi.com/2227-7390/9/21/2779) · [Bukor, Filakovszky and Tóth](https://journals.us.edu.pl/index.php/AMSIL/article/view/14169) · [Sándor and Zakarczemny](https://arxiv.org/abs/2611.20799)

The proof uses the sum bound from Conjecture 2 and its necessary conditions for equality. OpenAI Codex developed and formalized both proofs. [Statement](Statement.lean) · [Shared sum bound](../KarlovskySumBound/Solution.lean) · [Equality and uniqueness](Solution.lean)

```sh
# Run at the merge commit for PR #78.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

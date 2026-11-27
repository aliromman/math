# Proof of Liu’s Conjecture 2 on Walker’s inequality with side-sum weights

For every acute triangle with sides $a,b,c$ and every real $k\ge-10$, Jian Liu conjectured

$$
\sum_{\mathrm{cyc}}(a-b)(a-c)(b^2+c^2-a^2)(b+c)^k \ge 0.
$$

The following proof also covers right triangles. It gives the range $m=0$, $n\ge-10$ in Liu's later, two-parameter question (5.2). [Liu (2020), Conjecture 2, equation (7.4), p. 6671](https://www.aimspress.com/fileOther/PDF/Math/math-05-06-428.pdf#page=15) · [Liu (2024), §5](https://scik.org/aia/article/2024-1/aia-2024-1.pdf#page=19)

## Proof

By symmetry, order the sides as $a\le b\le c$. If $b=c$, only the nonnegative term at $a$ can be nonzero. Otherwise set $s=a+b$, $d=b-a$, and

$$
U=\frac{c-a}{c-b},\qquad V=\frac{c^2+ds}{c^2-ds},\qquad
H=\frac{c+b}{c+a},\qquad r=\frac ba.
$$

The denominators are positive. We prove $UV\ge H^{10}$. Since $H\ge1$ and $-k\le10$, this gives $UV\ge H^{-k}$. After multiplication by the denominators and by $b-a$, the term at $a$ offsets the term at $b$. The remaining term at $c$ is nonnegative.

We use two instances of the following inequality. For $t\ge1$ and $m>n>0$, set $A=(m+n)t+m-n$ and $B=(m-n)t+m+n$. Then $(A/B)^m\le t^n$. Indeed, $n\log t-m\log(A/B)$ vanishes at $1$, and its derivative is

$$
\frac{n(m^2-n^2)(t-1)^2}{tAB}\ge0.
$$

* If $8c\ge5s$, cross multiplication gives $H\le(5+13r)/(13+5r)$. Use $(m,n)=(9,4)$ to get $H^9\le r^4$. Also $U\ge r^2H$ and $V\ge r^2$. After clearing denominators, both comparisons reduce to $(b^2-a^2)(a^2+b^2-c^2)\ge0$. Their product gives $UV\ge r^4H\ge H^{10}$.
* If $8c<5s$, cross multiplication gives $H\le(4+5U)/(5+4U)$. Use $(m,n)=(9,1)$ to get $H^9\le U$. Also $V\ge H$ because the numerator of their difference is $d[s(2c+s)-c^2]\ge0$. Hence $UV\ge H^{10}$ in this case as well.

## Verification

The statement uses positive side lengths and the three strict squared-side inequalities. The law of cosines identifies these inequalities with acuteness, and they imply the strict triangle inequalities. The theorem `LiuWalkerTwo.nonobtuse` allows weak squared-side inequalities, in accordance with the terminology in Liu's introduction. [Statement.lean](Statement.lean) · [Solution.lean](Solution.lean)

Run these commands at the repository root.

```sh
lake exe cache get
python3 scripts/verify.py
```

Lean verifies the two scalar inequalities by expansion in $x-y\ge0$ and $y>0$. The axiom check for `LiuWalkerTwo.result` accepts `propext`, `Classical.choice`, and `Quot.sound`.

## Prior work and attribution

Liu proved the case $k=0$ in Corollary 12, equation (5.12), of the original paper. [Liu (2020), p. 6667](https://www.aimspress.com/fileOther/PDF/Math/math-05-06-428.pdf#page=11)

Liu's equation (2.19) in 2024 uses an ordered-term comparison for the weight $a(b+c-a)$. The same paper asks for the admissible exponents of $a^m(b+c)^n$. A search by title, DOI, formula, and exponent range on 24 November 2026 located no earlier proof of (7.4). The OpenAlex and Semantic Scholar citation records returned two other papers on related inequalities. Unindexed publications may exist. [Liu (2024)](https://doi.org/10.28919/aia/8682) · [OpenAlex citations](https://api.openalex.org/works?filter=cites:W3080239477)

OpenAI Codex derived the proof and wrote the Lean formalization.

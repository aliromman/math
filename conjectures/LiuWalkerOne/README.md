# Proof of Liu’s Conjecture 1 on Walker’s inequality with side-power weights

Jian Liu conjectured that every acute triangle with sides $a,b,c$ satisfies

$$
\sum_{\mathrm{cyc}}(a-b)(a-c)(b^2+c^2-a^2)a^k \ge 0
\qquad\text{for every real } k\le 4.
$$

The theorem below proves the conjecture. At $k=2$ the sum gives Walker's inequality through Liu's identity (7.1). Liu proved $k=1$ in Corollary 11 and $k=0$ in Corollary 12. [J. Liu, *AIMS Mathematics* 5 (2020), 6657–6672, Conjecture 1, equation (7.3), p. 6671](https://www.aimspress.com/fileOther/PDF/Math/math-05-06-428.pdf#page=15)

## Proof

The sum is symmetric. Order the sides as $a\le b\le c$. The middle term is the only one that can be negative. Acuteness gives

$$
D=(b^2-a^2)(a^2+b^2-c^2)\ge0.
$$

Expanding $D$ in two ways gives

$$
\begin{aligned}
a^2(c^2-a^2)-b^2(c^2-b^2)&=D,\\
a^2(b^2+c^2-a^2)-b^2(c^2+a^2-b^2)&=D.
\end{aligned}
$$

The first line gives $a^2(c-a)\ge b^2(c-b)$ after division by $c+a$, since $c+b\ge c+a$. Multiply this inequality by the second comparison. All four factors are nonnegative. This shows that

$$
a^4(c-a)(b^2+c^2-a^2) \ge b^4(c-b)(c^2+a^2-b^2).
$$

Since $a^{k-4}\ge b^{k-4}>0$, the same comparison holds with exponent $k$. Multiply by $b-a$. The term at $a$ then offsets the term at $b$, and the term at $c$ is nonnegative.

## Verification

The formal statement follows equation (7.3) and uses three positive real side lengths. By the law of cosines, the three strict squared-side inequalities characterize acute triangles. They also imply the strict triangle inequalities. Liu's introduction includes non-obtuse triangles in its terminology. The theorem `LiuWalkerOne.nonobtuse` proves the result with weak squared-side inequalities and includes right triangles. [Statement.lean](Statement.lean) · [Solution.lean](Solution.lean)

Run these commands from the repository root with the pinned Lean and Mathlib versions.

```sh
lake exe cache get
python3 scripts/verify.py
```

The build checks the axiom report for `LiuWalkerOne.result`. Its transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. The final command replays both project modules in the Lean kernel.

## Prior work and attribution

In 2024, Liu used a comparison of ordered terms to prove equation (2.19) with weight $a(b+c-a)$. He also asked for the full range of two exponents in equations (5.1) and (5.2). This proof gives $n=0$, $m\le 4$ for both questions. [Liu (2024), §§2 and 5](https://scik.org/aia/article/2024-1/aia-2024-1.pdf)

On 24 November 2026, searches by title, DOI, formula, and conjecture number, together with the OpenAlex and Semantic Scholar citation records, located no earlier proof of the full range $k\le4$. The citation indexes returned two other papers by Liu on related inequalities. Unindexed work may exist. [OpenAlex citation record](https://api.openalex.org/works?filter=cites:W3080239477) · [Liu (2021)](https://doi.org/10.7153/jmi-2021-15-92) · [Liu (2022)](https://doi.org/10.1007/s00022-022-00630-w)

OpenAI Codex derived the argument and wrote the Lean proof.

# Proof of Liu’s Conjecture 3 on Walker’s inequality with triangle-excess weights

Jian Liu asked whether every acute triangle with sides $a,b,c$ satisfies

$$
\sum_{\mathrm{cyc}}(a-b)(a-c)(b^2+c^2-a^2)(b+c-a)^k\ge 0
\qquad (k\in\mathbb R,\ k\ge-3).
$$

The inequality holds throughout this range, including for right triangles.
Liu states it as Conjecture 3, equation (7.5), on p. 6671 of *AIMS Mathematics*
5 (2020), 6657–6672. [Original paper, §7](https://www.aimspress.com/fileOther/PDF/Math/math-05-06-428.pdf#page=15)

## Proof

By symmetry, order the sides as $a\le b\le c$. Put $d=b-a$,
$t=a+b-c$, and $Q=a^2+b^2-c^2$. The triangle inequality gives $t>0$,
and the angle opposite $c$ gives $Q\ge0$ by the law of cosines.
Set

$$
A=(c-a)(b^2+c^2-a^2),\qquad B=(c-b)(c^2+a^2-b^2).
$$

The first two summands add to $d[A(c+d)^k-B(c-d)^k]$.
The third summand is $(c-a)(c-b)Qt^k\ge0$.
The following factorization settles the endpoint $k=-3$.

```math
\begin{aligned}
A(c-d)^3-B(c+d)^3
 = d\big[&t^3(c^2+d^2)\\ &+2Q\{t^2(2c-a-b)+4(a+b)(c-a)(c-b)\}\big]\ge0.
\end{aligned}
```

Each factor on the right is nonnegative. Divide by the positive
$(c-d)^3(c+d)^3$ to get $A(c+d)^{-3}\ge B(c-d)^{-3}$.
For $k\ge-3$, the function $x\mapsto x^{k+3}$ is nondecreasing
on positive $x$. Since $A,B\ge0$ and $c+d\ge c-d>0$,
this gives $A(c+d)^k\ge B(c-d)^k$.

## Formal verification

The three strict squared-side inequalities in the Lean statement characterize
acute triangles by the law of cosines. For positive side lengths they also
imply the triangle inequalities. The theorem `nonobtuse` uses weak
squared-side inequalities. The theorem `result` proves the published
statement. [Statement.lean](Statement.lean) · [Solution.lean](Solution.lean)

Run these commands from the repository root.

```sh
lake exe cache get
python3 scripts/verify.py
```

The build checks that the transitive axioms of `LiuWalkerThree.result` are
`propext`, `Classical.choice`, and `Quot.sound`. The last command replays
the declarations of both project modules in the Lean kernel.

## Prior work and attribution

Liu proved the case $k=0$ in Corollary 12, equation (5.12), of the original paper. [Liu (2020), p. 6667](https://www.aimspress.com/fileOther/PDF/Math/math-05-06-428.pdf#page=11)

In 2024, Liu proved a related inequality with weight $a(b+c-a)$ in (2.19).
Open Problem 1 of that paper asks which weights $a^m(b+c-a)^n$ work.
The result here gives the ray $m=0$, $n\ge-3$. Open Problem 2 uses the
weight $a^m(b+c)^n$. [Liu (2024), §§2 and 5](https://scik.org/aia/article/2024-1/aia-2024-1.pdf)

Searches on 24 November 2026 by title, DOI, conjecture number, and formula,
and a check of the original paper's indexed citations, found no previous
proof of the full range $k\ge-3$. Publication priority remains uncertain.
[OpenAlex citation index](https://api.openalex.org/works?filter=cites:W3080239477)

OpenAI Codex derived the polynomial certificate and wrote the Lean proof.

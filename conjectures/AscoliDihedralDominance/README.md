# Products beat quotients in generalized dihedral groups

In every finite nonabelian generalized dihedral group, subsets with more products than quotients outnumber subsets with more quotients than products. For a finite abelian group $H$ with an element of order at least three, set $G=H\rtimes C_2$, where the nonidentity element of $C_2$ sends $h$ to $-h$. Then

$$
\#\{A\subseteq G: |AA|>|AA^{-1}|\}
\;>\;
\#\{A\subseteq G: |AA|<|AA^{-1}|\}.
$$

Here $AA=\{xy:x,y\in A\}$ and $AA^{-1}=\{xy^{-1}:x,y\in A\}$. The statement includes the groups with base $H=C_2^r\times C_3$, which the authors singled out as beyond their estimates. This is Conjecture 1.6 in the 2022 preprint by Ascoli, Cheigh, Dantas e Moura, Jeong, Keisling, Lilly, Miller, Ngamlamai and Phang. Their separate Conjecture 1.7 concerns each subset size individually. [Original conjecture, pp. 2–5](https://arxiv.org/pdf/2210.00669) [Published chapter](https://link.springer.com/chapter/10.1007/978-3-032-08549-8_1)

For $n=|H|\ge128$, let $W$ and $L$ be the two counts on the left and right. The proof gives the stronger bound

$$
(3n-4)L\le(n+2)W.
$$

When $L>0$, this gives $W/L\ge 3-10/(n+2)$.

## Proof

Put $n=|H|$, $z=|\{h\in H:2h=0\}|$ and $t=n+z-1$. The group $G$ has $z$ central elements and $t$ elements of order two. Also $2z\le n$.

For each $A$, let $p(A)$ count missing products and $w(A)$ count missing quotients that have order two. A missing quotient gives a strict product advantage when all products occur. More generally, the sign of $|AA|-|AA^{-1}|$ is at least $\mathbf{1}_{w(A)>0}-p(A)$. Set $F=\sum_A w(A)$, $D=\sum_A w(A)^2$ and $P=\sum_A p(A)$. Cauchy–Schwarz gives at least $F^2/D$ subsets with a witness. It therefore suffices to prove $F^2>DP$.

For a fixed element $g$ of order two, $g$ is missing from $AA^{-1}$ exactly when $A$ contains at most one endpoint of each pair $\{x,gx\}$. Each of the $n$ pairs gives three choices. Hence $F=t3^n$. Two distinct involutions give disjoint matchings, whose union consists of cycles. A cycle of length $k\ge3$ has $L_k$ independent sets, where $L_k$ is the Lucas number and $L_k^4\le7^k$. Two witnesses thus occur together for at most $7^{n/2}$ subsets.

A product $g$ is missing when $A$ avoids adjacent vertices in the cycles of $x\mapsto x^{-1}g$. Applying this map twice sends $x$ to $g^{-1}xg$. The fixed points of that second iterate form the centralizer of $g$. A noncentral element has at most $n$ such points. The same cycle bound gives at most $3^n(7/9)^{n/4}$ choices of $A$ for each noncentral $g$, and at most $3^n$ for each central $g$.

For $n\ge32$, these bounds give

$$
D \le 1.9\,t3^n,
\qquad
P \le \left(z+\tfrac{17}{125}(2n-z)\right)3^n.
$$

Since $1.9\left(z+\tfrac{17}{125}(2n-z)\right)<n+z-1=t$, this proves the strict inequality. For $n\ge128$, the sharper bounds $P\le(z+1)3^n$ and $D\le(t+1)3^n$ give $W-L\ge(n-3)3^n$. Each quotient-dominant set misses a product, so $L\le P$. Together these inequalities give the stated ratio.

For $n<32$, the structure theorem for finite abelian groups leaves 43 possibilities. Lean checks the same witness bound separately at each subset size. For $n\le16$, removing labels missing from both sets sharpens the bound without changing the difference. For a cycle, the coefficient of $s^m$ in its independence polynomial counts admissible $m$-sets. These polynomials satisfy $C_0=2$, $C_1=1$ and $C_{k+2}=C_{k+1}+sC_k$. The cycles from two quotient labels $g,h$ have length $2\operatorname{ord}(gh)$. A common missing label that is a rotation gives an independent-set count on $H$ and a separate cycle count on the reflections. The finite check sums the resulting lower bounds on the signed excess over all sizes. In three groups it also counts small subsets directly.

| Abelian base $H$ | Subset sizes counted directly | Excess of product-dominant subsets in those sizes |
| --- | --- | ---: |
| $C_6$ | 0–3 | 144 |
| $C_2\times C_4$ | 0–5 | 2,928 |
| $C_2\times C_6$ | 0–4 | 7,320 |

The smallest certified lower bound on the total excess is two, for $H=C_4$.

## Prior work and attribution

Miller and Vissuet posed the cyclic-base case. Ascoli and coauthors extended the question to all finite abelian bases in 2022. Amit and coauthors proved the cyclic-base case in 2026 using moments and graphs that encode missing products or quotients. Their results also cover many large finite groups. The proof here counts witnesses among involutions and subtracts missing products. The literature search found no earlier proof for every eligible abelian base. [Ascoli et al.](https://arxiv.org/abs/2210.00669) [Amit et al., Theorems 1.5 and 6.2](https://arxiv.org/html/2610.12912v1)

OpenAI Codex agents developed the argument, searched the literature and wrote the Lean proof. The finite checks use integer arithmetic and the Lean kernel.

## Verification

From the repository root, run

```sh
lake exe cache get
lake build conjectures.AscoliDihedralDominance.Solution
lake env leanchecker conjectures.AscoliDihedralDominance.Solution
```

The independent statement is in [Statement.lean](Statement.lean). The final theorem is [AscoliDihedral.proved](Solution.lean). Its axiom check allows propositional extensionality, classical choice and quotient soundness.

# Proof of Chauve, Ponty and Wallner’s Conjecture 4.5 on extremal duplication–loss histories

For every terminal count $n\ge2$, the caterpillar has the most ordered duplication–loss histories among rooted binary trees with $k$ leaves. The balanced tree has the fewest. Both statements characterize the tree shape up to swaps of the two children. With four leaves and two terminals, these counts are 39 and 34. At $n=1$, every tree has exactly $k$ histories.

Write $E(T)=\lim_{n\to\infty} h_T(n)^{1/n}$ for the exponential growth factor of the counts. For a constant $c>0$, the balanced growth factor satisfies $E(\mathrm{balanced}_k)/k\to c$. The proof also gives

$$
E(\mathrm{caterpillar}_k)\ge \tfrac12 k^{3/2},
\qquad k\le E(\mathrm{balanced}_k)\le64k.
$$

This proves Conjecture 4.5 of Cédric Chauve, Yann Ponty and Michael Wallner. They proposed eventual extremality, superlinear growth for caterpillars, and linear growth for balanced trees. Their Theorem 3.4 gives an asymptotic formula for each fixed tree. Here the comparison holds as soon as two terminals are present. A balanced split divides the leaves as evenly as possible at every node. At each internal node of a caterpillar, at least one child is a leaf. [Source, §4.2 and Conjecture 4.5](https://doi.org/10.1007/s00285-019-01465-x)

## Proof

Let $H_T(z)=\sum_{n\ge1}h_T(n)z^n$, and put $P_T=1+H_T$. The source grammar distinguishes an ordered duplication from a split between the two child trees. At a split, either child can lose its lineage. The leaf and internal recurrences are

$$
H_\bullet=z+H_\bullet^2,
\qquad H_T=H_T^2+H_A+H_B+H_AH_B.
$$

Thus $Q_T=P_T-H_T^2$ equals $1+z$ at a leaf and $P_A P_B$ at a split. Suppose a change of inputs multiplies $Q$ by $1+D$. If $a$ and $b$ are the old and new output series $H$, direct multiplication gives

$$
\frac{1+b}{1+a}=1+D\left(1+\frac{a+b+ab}{1-a^2-b-ab}\right).
$$

The multiplier has nonnegative coefficients and increases coefficient by coefficient in either argument. For a balanced tree with $2j$ leaves, the two child factors are $P_j,P_j$. The next two sizes have factors $P_j,P_{j+1}$ and $P_{j+1},P_{j+1}$. Both steps multiply the input by the same $P_{j+1}/P_j$. The displayed identity therefore shows inductively that adjacent output ratios increase with tree size. For caterpillars, each step keeps the same leaf child, which gives the same conclusion directly.

Within either family, moving one leaf from a smaller child to a larger child increases the product of the two factors. Balanced splitting minimizes it and splitting off one leaf maximizes it. The increase is strict at degree two whenever the split has actually become less even. The duplication term propagates this strict inequality to every later coefficient. Induction through the tree gives both extremizers and their equality cases.

Root duplication gives $h_T(i+j)\ge h_T(i)h_T(j)$. A finite exponential upper bound and Fekete's lemma give the stated limit, which is at least any single $n$th root. The size-two recurrence on a caterpillar gives $4h_T(2)\ge k^3$.

For the balanced upper bound, let $U$ be the positive Catalan series satisfying $U=16kz+U^2$. For a subtree with $m$ leaves put $s=m/k$ and $w(s)=(s+s^2)/16$. At a balanced split of normalized sizes $x,z$, one has $x\le2z$ and $z\le2x$. Expansion gives

$$
w(x+z)^2+w(x)+w(z)+w(x)w(z)\le w(x+z).
$$

Since $U^2\le U$ coefficient by coefficient, the grammar gives $H_T\le w(s)U$ by induction. The Catalan bound $C_n\le4^n$ gives $E(T)\le64k$. The lower bound $E(T)\ge k$ follows from $h_T(1)=k$.

The limiting constant comes from replacing every leaf of an outer tree of growth $r$ by the same $m$-leaf tree. The resulting growth factor is between $mr$ and $mr+C_m$, for a constant $C_m$ that depends only on the inner tree. In generating functions this operation substitutes $Q_{\mathrm{inner}}-1$ for $z$. Its first coefficient is $m$, and a finite exponential bound on the other coefficients gives
$ m z \le Q_{\mathrm{inner}}-1 \le m z/(1-C_mz)$.
Substitution in the outer series gives the lower bound. Substitution in the upper geometric series $1/(1-rz)$ gives the upper bound.

For the complete tree with $2^h$ leaves, the ratio $E/2^h$ increases with $h$ and is bounded by 64. For each fixed $m$, grafting a balanced $m$-leaf tree under every leaf of the complete tree gives the balanced tree with $m2^h$ leaves. Its ratio has the same limit. Monotonicity then bounds every other leaf count between consecutive multiples of $2^h$. As $m$ increases, the relative gap between adjacent multiples is at most $1/m$.

## Verification

The statement defines each history as an element of the corresponding finite disjoint union and counts it by cardinality. The final theorem proves the source's extremal conditions, convergence of the roots of the actual counts, superlinear caterpillar growth and a common positive limit for normalized growth across all balanced shapes.

From the repository root, run

```sh
# Run at the merge commit for PR #43.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The guarded axiom report permits only propositional extensionality, classical choice, and quotient soundness. Searches by conjecture number, exact growth terminology, author names, and citations found the source's analysis and computations. No earlier proof was located. OpenAI Codex developed the proof and Lean formalization.

Cédric Chauve, Yann Ponty and Michael Wallner, Counting and sampling gene family evolutionary histories in the duplication-loss and duplication-loss-transfer models, §4.2, Conjecture 4.5. [Publication](https://link.springer.com/article/10.1007/s00285-019-01465-x)

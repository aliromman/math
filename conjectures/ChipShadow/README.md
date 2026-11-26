# The double gap is uniform

Start with $N\ge2$ chips in consecutive rooms of the integer line. Choose an adjacent occupied pair uniformly. Move its left chip to the nearest vacant room on the left and its right chip to the nearest vacant room on the right. Continue until no adjacent pair remains. Exactly one gap then has two empty rooms. Each of its $N-1$ possible positions has probability

$$
\frac1{N-1}.
$$

This proves Conjecture 7.1 of Tanya Khovanova and Rich Wang. They classified the possible final configurations and checked uniformity through $N=13$. The probability of a specific configuration depends on its location. For example, four chips can end in five configurations with probabilities $1/6,1/6,1/3,1/6,1/6$, in order of increasing sum of room numbers. Grouping translations gives three gap positions of probability $1/3$ each. [Khovanova and Wang, “Ending States of a Special Variant of the Chip-Firing Algorithm,” §7.1](https://ecajournal.kms-ks.org/Volume2024/ECA2024_S2A20.pdf)

## Proof

Number the chips from left to right, starting at zero. Write $x_i$ for the room of chip $i$ and put $w_i=x_i-2i$. Translate the starting configuration so that the initial knots $w_i$ are $N-1,N-2,\ldots,0$.

Within any run of consecutive rooms, the knots descend by one at each rank. Suppose their extremes are $H>L$. After a cut, the lower ranks shift one room left and the upper ranks shift one room right. In the multiset of knots, this replaces $L,H$ by $p,p+1$, once for each $p=L,\ldots,H-1$. Consequently the rational function $F_w(z)=\prod_i(z-w_i)^{-1}$ is preserved in conditional expectation. The entire calculation is

$$
\sum_{p=L}^{H-1}\frac1{(z-p)(z-p-1)}
=\frac1{z-H}-\frac1{z-L}
=\frac{H-L}{(z-L)(z-H)}.
$$

For each $j\ge1$, sum the coefficients of $(z-h)^{-j}$ in the Laurent expansions of $F_w$ at all integer knots $0\le h<N$. Each sum is also preserved in expectation. Initially all poles are simple, and the sum of their residues is zero since $F_w(z)=O(z^{-2})$ at infinity. The entire vector of sums therefore starts at zero.

The knots stay in $[0,N-1]$, and $w_j\le w_i+1$ holds whenever $i\le j$. The integer $\sum_i2^i w_i$ strictly increases at each move. The gain at the first rank that shifts right outweighs all preceding losses. Thus every path stops within a common finite time. At that time the knots are nondecreasing, and the last cut left a strict increase. They have the form $h,\ldots,h,h+1,\ldots,h+1$. The break marks the double gap.

Let $V(a,b)$ be the vector of coefficient sums for $a$ copies of $h$ and $b$ copies of $h+1$. Translation does not affect it. Write $e_j$ for the unit vector at pole order $j$. Partial fractions give

$$
V(0,j)=V(j,0)=e_j,\qquad V(a,b)=V(a-1,b)-V(a,b-1)\quad(a,b>0).
$$

Suppose $\sum_{r=1}^{N-1}p_rV(r,N-r)=0$. The recurrence gives $(p_1-p_{N-1})e_{N-1}$ and a combination on the preceding diagonal, with coefficients $p_{r+1}-p_r$. Vectors on the interior of that diagonal have zero coordinate at order $N-1$. Hence $p_1=p_{N-1}$ and the preceding combination vanishes. Induction from $N=2$ makes the successive differences constant. They sum to zero, so all $p_r$ are equal. Applying this to the terminal probabilities gives $p_r=1/(N-1)$.

## Verification and attribution

The statement records uniform random choice among all moves. The formal proof also identifies the indexed moves with adjacent occupied rooms, proves termination, and derives the terminal probabilities from the Laurent coefficients. The result concerns the position of the gap up to translation. The paper's recursive-tree conjecture 7.2 concerns the finer distribution of absolute positions.

```sh
lake exe cache get
lake build conjectures.ChipShadow.Solution
lake env leanchecker conjectures.ChipShadow.Solution
```

Searches by author, title, clusterons, two-sided dispersion, uniform gaps, and splines located no earlier proof of Conjecture 7.1. OpenAI Codex developed the argument and formal proof.

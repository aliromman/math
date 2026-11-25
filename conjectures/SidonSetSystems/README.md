# Almost all shapes fit in one Sidon set system

For every fixed $k\ge 3$, the largest Sidon system of $k$-element subsets of $\{1,\ldots,n\}$ has size

$$
F_k(n)=\binom{n-1}{k-1}+O_k(n^{k-2}).
$$

In a Sidon system, the sumset $A+B=\{a+b:a\in A,\ b\in B\}$ determines the unordered pair $A,B$, including when $A=B$. For example, $F_4(n)=n^3/6+O(n^2)$. The coefficient $1/6$ is the first leading coefficient left open in the original paper.

Cilleruelo, Serra and Wötzel proved $F_k(n)\le U_k(n)=\binom{n-1}{k-1}+n-k$. They conjectured after Theorem 1.3 that $F_k(n)/U_k(n)\to 1$ for every fixed $k\ge2$. They proved $F_2(n)=2n-3$ and the asymptotic result for $k=3$. The formula above resolves all remaining cases. [Original paper](https://ems.press/journals/rmi/articles/16730) · [Author manuscript, p. 1 and §6.1](https://arxiv.org/pdf/1802.10511)

## Proof

Subtract the least member of each set to get its *shape*. Each shape contains zero. Our construction removes $O_k(n^{k-2})$ shapes and assigns a small translation to every survivor.

**Record a collision.** Order the elements of four shapes $A,B,C,D$. If $A+B=C+D$, choose an equal sum on the opposite side for each sum on either side. Only finitely many such patterns exist at fixed $k$. Each gives homogeneous linear equations in the $4(k-1)$ entries other than the minima. Let $V$ be their rational solution space. The coordinate functions in $V^*$ give four sets of $k$ points with the prescribed sumset equality. If one set has dependent nonzero coordinates, its numerical entries satisfy a fixed nonzero linear relation. Fixing all but one entry leaves at most one choice. Discarding these shapes over all patterns costs $O_k(n^{k-2})$. In any surviving collision all four sets of coordinate functions are affine simplices.

**Separate the simplices.** Write $h_A(q)=\max_{a\in A}q(a)$ and let $U_A$ be the span of the differences between points of $A$. If $h_A$ is a linear combination of three other support functions, $U_A$ lies in one of their three direction spaces. To see this, suppose $v\in U_A$ lies outside all three spaces. Choose an affine form vanishing on each corresponding set with linear part positive on $v$. The alternating sum over subsets of these three forms, added to a probe $q$, kills every competing support function. It cannot kill $h_A$ for every $q$. Each nonempty sum of forms has positive spread on $A$. Choose $\delta>0$ no larger than the smallest such spread. Affine independence lets $q$ raise any chosen subset of vertices by $\delta$. Alternating over these subsets gives zero for each nonempty sum of forms, since raising one lowest vertex cannot change the maximum. For the empty sum it gives $-\delta$. Interchanging the two alternating sums gives a contradiction.

Thus if $U_A\ne U_B$, the two equal-dimensional spaces match $U_C,U_D$ up to exchange. Take the order $U_A=U_C$, $U_B=U_D$. A linear form constant on $B,D$ and varying on $A,C$ exposes disjoint top and bottom faces of the latter simplices. The gap $h_A-h_C$ equals the gap between their top faces and also the gap between their bottom faces. Indeed, maximize a large multiple of the chosen form, with an arbitrary probe added to break ties. Write $X,Y,Z,W$ for the direction spaces of the top and bottom faces of $A$, then $C$. Opposite faces of a simplex give $X\cap Y=Z\cap W=0$. The two expressions for the support gap give $X+W=Y+Z$. Comparing dimensions gives $\dim X=\dim Z$, $\dim Y=\dim W$ and $X\cap W=Y\cap Z=0$. The preceding support-function argument now gives $X=Z$ and $Y=W$. Projecting onto $X$ and killing $Y$ makes the common gap the evaluation of a fixed translation vector. Hence the simplices $A,C$ are translates, as are $B,D$. Numerical shapes have minimum zero, so this collision is trivial.

**Translate the survivors.** In a nontrivial collision all four direction spaces therefore agree. Their coordinate functions span $V^*$, so the values of any one shape determine the other three once the pattern and its slots are fixed. Join two distinct shapes by an edge whenever they occur together in a nontrivial collision. The degree has a bound $D(k)$ independent of $n$. Color the graph in $D(k)+1$ colors and translate each shape of color $j$ by $3^j$. If two translated sumsets coincide, their minima agree. The base-three digits determine the unordered pair of colors, even for a repeated color. Every two different shapes in a nontrivial collision have different colors. Thus the colors identify both summands. Reserving a margin of $3^{D(k)}$ at the edge of the interval costs only $O_k(n^{k-2})$ more shapes.

## Prior work and verification

Wötzel announced a stronger result concerning arbitrary choices of translations in a 2023 extended abstract. He withdrew the full preprint in February 2024 after a referee identified a false step. The construction here chooses its translations. A search of the paper, its citations and the subsequent literature found no other proof of the general extremal asymptotic. [Extended abstract](https://journals.phil.muni.cz/eurocomb/article/view/35648) · [Author’s withdrawal](https://arxiv.org/abs/2211.14011)

From the repository root, run

```sh
lake exe cache get
lake build conjectures.SidonSetSystems.Solution
```

`Statement.lean` defines the extremal function and the conjecture. `Solution.lean` proves the limit, and `ErrorTerm.lean` gives the quantitative error. Both theorems check their transitive axioms. AI agents developed the construction, the mathematical proof and its Lean formalization.

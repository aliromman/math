# A leafless subtree maximizes local density

Join two three-leaf stars by a path with nine internal vertices. In this 17-vertex tree, the middle vertex alone has the greatest possible local subtree density, **31/52**. It has degree two. This disproves Ruoyu Wang’s Conjecture 20. The paper reported that every maximizer in its enumeration of nonpath trees through 15 vertices contained a leaf. [Original conjecture and Example 18](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p60/pdf/)

For a proper nonempty subtree $S$, choose a subtree $U$ that contains $S$ uniformly from all such subtrees. Wang’s local density is

$$
D_T(S)=\frac{\mathbb E[|U|-|S|]}{|T|-|S|}.
$$

The six leaves are the three neighbors of each star center outside the joining path. If the path vertices are $0,1,\ldots,10$, the maximizers are the singleton $\{5\}$ and the two subtrees obtained by taking a star and all the joining path up to vertex 5. Thus leaf-containing and leafless maximizers coexist in this tree.

## Why the center wins

Deleting $S$ leaves branches $C_1,\ldots,C_r$. Root each at its attachment to $S$. The intersection of $U$ with a branch is either empty or a connected subtree containing its root. These choices are independent and uniform. Write $d(C)$ for the expected number of chosen vertices in $C$, divided by $|C|$. Then

$$
D_T(S)=\frac{\sum_i |C_i|\,d(C_i)}{\sum_i |C_i|}.
$$

Each branch of an oriented edge can serve as the entire complement of $S$. The largest local density is therefore the largest oriented-edge score $d(C)$. A subtree attains it precisely when every branch outside it has that score.

A cut on the joining path leaves a branch consisting of one three-leaf star and $h$ vertices before its center, for $0\le h\le9$. A selection that stops before the star has one of the sizes $0,1,\ldots,h$. A selection that reaches the star contains the whole stem and the center, followed by any subset of the three leaves. Hence

$$
d_h=\frac{h(h+1)/2+8(h+1)+12}{(h+4)(h+9)},\qquad
\frac{31}{52}-d_h=\frac{(h-4)(5h-19)}{52(h+4)(h+9)}.
$$

A cut at a leaf has scores $1/2$ and $173/292$ in its two orientations. For the latter score, conditioning on that leaf gives 73 possible subtrees and 692 additional vertices counted with multiplicity. The product $(h-4)(5h-19)$ is nonnegative for every integer $h$ and vanishes only at $h=4$. Thus $h=4$ gives the unique largest branch score. Both branches outside the central singleton have this length.

## Source and verification

Ruoyu Wang, *Extrema of Local Mean and Local Density in a Tree*, Electronic Journal of Combinatorics **33** (2026), P1.60, Conjecture 20, p. 19. In Example 18, Wang already showed that every proper subtree of a path has density $1/2$. The middle vertex of a three-vertex path therefore violates the literal statement. The 17-vertex example above resolves the nonpath case that motivated the conjecture. The counterexample above has six leaves and its local density varies with the chosen subtree. Searches by title, conjecture wording and citations found no earlier resolution. [Journal article](https://doi.org/10.37236/13813) · [Author’s preprint](https://arxiv.org/abs/2306.13422)

The Lean statement uses finite simple trees and connected induced vertex sets. The proof generates all 275 nonempty subtrees of the example. It verifies that the family contains all singletons and is closed under adding any neighbor. Checking these two properties certifies that the enumeration is exhaustive. The proof computes the exact maxima by ordinary kernel reduction. OpenAI Codex developed the argument and the Lean formalization. [Statement](Statement.lean) · [Classification and disproof](Solution.lean)

```sh
lake exe cache get
lake build conjectures.WangLocalDensity.Solution
lake env leanchecker conjectures.WangLocalDensity.Solution
```

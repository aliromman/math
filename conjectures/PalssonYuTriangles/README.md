# Four triangle shapes force a regular heptagon

Seven is the largest number of points in the plane that determine exactly four triangle shapes. A set of seven attains this bound precisely when it is the vertex set of a regular heptagon.

Eyvindur A. Pálsson and Edward Yu proved the corresponding result for three shapes and the regular hexagon. Their Conjecture 10 asks for the next case. A shape here means a congruence class. Reflections are allowed, scale matters, and three distinct collinear points also count. [Original paper, Conjecture 10](https://doi.org/10.37236/12360).

## Proof

Assign the same color to two edges when their lengths agree. A triangle's shape is determined by the multiset of its three colors. The regular heptagon has three chord lengths, numbered from shortest to longest. Its four triangle shapes are

$$
(1,1,2),\quad (1,2,3),\quad (1,3,3),\quad (2,2,3).
$$

For the converse, take any seven points with at most four shapes. Four points cannot have all six edges of one length. Also, for any two fixed points, at most two other points can have a prescribed distance to each of them, since two circles have at most two common points.

Color the edges one new vertex at a time. For each edge, try every color already used and one new color. Discard an assignment when it produces a fifth triangle shape or violates either planar condition. Combine assignments that differ only by names of vertices and colors. The numbers of surviving patterns are

| Vertices | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- | --- |
| Patterns | 1 | 3 | 24 | 32 | 31 | 6 |

Five final patterns are impossible. In each, equal distances place three points on a perpendicular bisector. If one is equidistant from the other two, it is their midpoint. In two patterns a segment must then equal its own half. In two others the squared lengths of two positive segments must each be four times the other. In the fifth, two distinct points must be the same midpoint.

In the sixth pattern the cyclic shift of the vertices preserves every edge length. It therefore extends to an isometry of the plane. Its action on the seven points has order seven. A reflection or glide reflection has a translation as its square, and a translation that preserves a finite set is the identity. The shift must therefore be a rotation of order seven. Its orbit is a regular heptagon.

Finally, suppose there were eight points with at most four shapes. Deleting any point would leave a regular heptagon. Fix two points $A,B$. In each heptagon containing them, exactly two vertices are at distance $AB$ from $A$. Deleting any of the other six must leave that same count, so those six are either all at distance $AB$ from $A$ or all at a different distance. The resulting count is six or one. This excludes eight, and hence every larger set.

## Verification and prior work

The Lean bound covers arbitrary subsets of the Euclidean plane, represented by complex numbers. An infinite set contains an eight-point subset. The search verifies each discarded pattern or relabeling inside the kernel, one predecessor row at a time. It requires no numerical coordinates. Reproduce the proof with the pinned Lean and Mathlib versions from the repository root.

```sh
lake build conjectures.PalssonYuTriangles.Solution
lake env leanchecker conjectures.PalssonYuTriangles.Solution
```

`Statement.lean` gives the original conjecture. `Solution.lean` proves `PalssonYu.resolution` and checks its axioms. An independent enumeration of labeled edge patterns and an independent audit of the geometry checked the classification.

Erdős and Fishburn studied the analogous extremal question for distinct distances. Lan and Wei classified the seven-point sets that determine exactly four distances. Here the bound is on the number of congruence classes of triangles, with no assumption on the number of distances. Searches of the triangle paper, subsequent citations, and related distance classifications found no earlier proof of this conjecture. AI agents derived the argument, performed the enumerations, and wrote and audited the Lean proof. [Pálsson and Yu](https://arxiv.org/abs/2308.13107) · [Lan and Wei](https://doi.org/10.1134/S000143461303019X).

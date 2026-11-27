# Proof of Edelsbrunner, Garber and Saghafian’s Conjecture C on maximal planar hypertriangulations

Edelsbrunner, Garber, and Saghafian’s Conjecture C holds at every level. We also obtain a local test. If a hypertriangulation has fewer triangles than the maximum, one can split a single face into three by inserting one admissible point. Each such step adds two triangles.

## The question

Take a finite set $A$ in the plane, with no three points on a line and no four on a circle. Choose $1\le k<|A|$. Label each $k$-point average by the subset of $A$ that produced it. A hypertriangulation triangulates the convex hull of these averages. It may omit some averages. Each edge must join two labels that differ by one exchange. If several labels give the same point, a triangulation may use at most one there.

A hypertriangulation is *maximal* if it admits no proper subdivision of the same kind. Is its triangle count as large as that of any level-$`k`$ hypertriangulation of $A$? The authors established the level-two case, cited the case of points in convex position, and posed the general question in §6, p. 30. [Original article, *Advances in Mathematics* 461 (2025), 110055](https://doi.org/10.1016/j.aim.2024.110055)

## A face weight

Write $Ua$ for $`U\cup\{a\}`$. Fix a triangle and orient it counterclockwise. Its three labels have one of two forms.

| Face | Labels in cyclic order | Eligible points inside the original triangle $abc$ |
|---|---|---|
| White | $Ua,Ub,Uc$ | $p\notin U$ |
| Black | $Xbc,Xca,Xab$ | $p\in X$ |

Give the face weight $1+2m$, where $m$ counts its eligible points. A white face is a translated and scaled copy of $abc$. Each eligible $p$ gives a new interior vertex $Up$. A black face is a translated, scaled, and centrally reflected copy of $abc$. Its new interior vertex is $`(X\setminus\{p\})abc`$. In both cases the new label differs by one exchange from each corner, so joining it to the corners is an admissible subdivision.

## Why the total is constant

Identify each label with its zero–one vector. All labels lie in the hypersimplex

```math
\Delta(k,A)=\left\{x\in[0,1]^A:\sum_{a\in A}x_a=k\right\}.
```

A labelled triangular face lifts to a triangular two-dimensional face of this polytope. Give the reverse orientation the negative weight. The signed sum around each three-dimensional face vanishes. There are two cases.

* A tetrahedron varies four original points. Every other input point contributes its signed triangle indicators. Their alternating sum is zero because the two projected sides of the tetrahedral boundary cover the plane with equal multiplicities. This remains true when one of the four points is inside the triangle of the other three. In that case the large triangle counts this point and contributes $1+2=3$ against three smaller triangles of weight one. When the four points form a convex quadrilateral, two triangles appear on each side. For a black tetrahedron, the omitted corner of each three-point test belongs to the fixed set for that face, so the same accounting applies.
* An octahedron varies two choices among four points $a,b,c,d$. Opposite faces correspond to the same original triangle with opposite boundary signs. Their constant terms cancel. For the pair varying $a,b,c$, the white face has fixed set $Xd$ and the black face has fixed set $X$. The three vertices of $abc$ cannot be interior, and $d$ is excluded from both counts. Thus each point outside $`\{a,b,c,d\}`$ contributes its signed triangle indicator with a fixed coefficient, either $+2$ or $-2$. Its four indicators again have alternating sum zero.

A convex polytope has zero second homology. Consequently a closed chain of triangular faces is a sum of boundaries of three-dimensional faces. The total signed weight of a lifted triangulation therefore depends only on its oriented boundary. The Lean proof constructs the corresponding weights on individual edges directly by adding one input label at a time. Its two local consistency checks are precisely the tetrahedron and octahedron identities above.

Every triangulation has the same labelled boundary. For any supporting direction, a maximizing label chooses the $k$ largest projected coordinates. At most two input points tie at the cutoff, because no three input points are collinear. Each boundary edge therefore has the same two endpoint labels in every triangulation. This argument also permits coincident or collinear averages in the interior.

Let $M$ be the common total weight. Every triangle contributes at least one, so every triangulation has at most $M$ triangles. A maximal triangulation has no eligible point in any face, hence exactly $M$ triangles. Conversely, a triangulation with fewer than $M$ triangles has a face of weight greater than one and admits the three-way split described above.

## Prior work and attribution

The source gives the level-two theorem and discusses earlier results in convex position. Olarte and Santos studied hypersimplicial subdivisions and separation. Kaylor developed an enumeration algorithm for small configurations. Searches for the conjecture by number, title, authors, maximality, and face counts found no earlier general proof. OpenAI Codex developed the conserved face weight and constructed the proof and Lean formalization. [Olarte–Santos](https://doi.org/10.1007/s00029-021-00722-6) · [Kaylor’s thesis](https://scholarworks.utrgv.edu/etd/1591/)

## Verification

From the repository root, run the following commands with the pinned toolchain.

```sh
# Run at the merge commit for PR #87.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Edelsbrunner, Garber and Saghafian, “Order-2 Delaunay triangulations optimize angles,” Advances in Mathematics 461 (2025), 110055, §6, Conjecture C, p. 30, DOI 10.1016/j.aim.2024.110055. [Publication](https://pub.ista.ac.at/~edels/Papers/2025-01-Order2Angles.pdf#page=30)

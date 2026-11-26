# A leaf move disproves the maximum conjecture for maximal matchings

Take the path from 0 to 11, attach a two-edge arm $2,12,13$ at vertex 2,
and add a leaf at vertex 9. This is the proposed maximizer on 15 vertices
of diameter 11. Move the leaf from 9 to 3. The average size of a maximal
matching increases from **6** to **259/43**, an increase of **1/43**.

## Conjecture

John Engbers and Aysel Erey studied the mean number of edges in a uniformly
chosen inclusion-maximal matching. They determined the extremal trees of
fixed order for diameters up to 5. Lukai Sui and Qiuli Li give the maximum
conjecture in full as Conjecture 1.2 and prove the diameter-6 case.
[Engbers and Erey, *Discrete Applied Mathematics* 341 (2023), 308–321](https://doi.org/10.1016/j.dam.2023.08.022).
[Sui and Li, *Discrete Applied Mathematics* 377 (2025), 518–528](https://www.sciencedirect.com/science/article/pii/S0166218X25004573).

Fix an order $n$ and diameter $d\ge 5$. Begin with a path on vertices
$0,\ldots,d$. The conjecture specifies a unique maximizing tree, up to
isomorphism, in each of two cases.

- If $n+d$ is odd, attach $(n-d-1)/2$ additional two-edge arms at vertex 2.
- If $n$ and $d$ are both odd, attach $(n-d-2)/2$ additional two-edge
  arms at vertex 2 and one leaf at vertex $d-2$.

In the authors' branch notation, the path segment $2,1,0$ supplies one
of the length-two arms. The example violates the upper bound in the second case.

## Proof

Write $T_j$ for the tree with the leaf attached at $j$. Both $T_9$
and $T_3$ contain the original 11-edge path. The tip of the added arm
has the same distances to vertices 2 through 11 as vertex 0. The added
leaf is at distance at most 10 from every vertex. Thus both diameters are 11.

| Tree | Maximal matchings of size 5 | Size 6 | Size 7 | Mean size |
|---|---:|---:|---:|---:|
| Proposed $T_9$ | 7 | 22 | 7 | $216/36=6$ |
| Competitor $T_3$ | 3 | 36 | 4 | $259/43=6+1/43$ |

The table can be obtained by a short recurrence. Give a maximal matching
of size $s$ weight $x^s$. Weights multiply over components. A maximal
matching covers the neighbor of a leaf. Condition on its matched edge,
delete the two endpoints, and multiply the remaining weight by $x$.

For the path on $j$ vertices this gives $F_0=F_1=1$, $F_2=x$, and
$F_j=x(F_{j-2}+F_{j-3})$ for $j\ge3$. A center with two arms of length
2 and a third arm of length $j$ has weight $B_j=x^2(F_{j+1}+2F_j)$.
Either both outer edges of the two short arms are used, or one inner edge
and the opposite outer edge are used.

At vertex 3 the three possible partners are 2, 4, and the new leaf.
At vertex 9 they are 8, 10, and the new leaf. The respective sums are

```text
T₃   x³(4F₈ + 3F₇)             = 3x⁵ + 36x⁶ + 4x⁷
T₉   x((B₅ + B₆)F₂ + B₆ F₁)   = 7x⁵ + 22x⁶ + 7x⁷
```

## Verification and provenance

From the repository root, run

```sh
lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Combinatorics.SimpleGraph.Diam Mathlib.Data.Nat.Dist Mathlib.Data.Rat.Defs
lake build
python3 scripts/verify.py
lake env leanchecker conjectures.EngbersErey.Solution
```

[Statement.lean](Statement.lean) quantifies over edge lists on `Fin n`.
Every finite simple graph has such a labeling. Each edge occurs once,
with its smaller endpoint first. A sublist is a maximal matching precisely
when its edges are pairwise disjoint and every graph edge meets one of them.
[Solution.lean](Solution.lean) proves treehood and diameter with Mathlib,
computes both rational averages in the kernel, and checks the transitive
axioms of `EngbersErey.counterexample`.

Title, author, and counterexample searches and forward citation searches
of the two papers on 2026-11-24 found the diameter-6 result and no prior
refutation of the maximum conjecture. The exact statement used here is
the published restatement by Sui and Li.

OpenAI Codex agents found the witness, derived the recurrence, and wrote
the Lean formalization. A separate agent audited the statement and proof.

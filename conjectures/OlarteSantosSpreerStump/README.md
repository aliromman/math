# Disproof of Olarte, Santos, Spreer and Stump’s Conjecture 3.5 on dual pairs in flag complexes

A flag triangulation on 12 vertices has two families of faces that are each
other’s intersecting dual. The pair has nine essential vertices. The boundary
of the three-dimensional cross-polytope has six vertices. Thus the two
complexes cannot have isomorphic dual pairs of this type.

## Statement

The intersecting dual of a family consists of all faces that meet every
member. A vertex is essential if it belongs to a minimal member. An
isomorphism of dual pairs is a bijection of the essential vertices that
carries the minimal members on both sides to those on the other pair.
It can interchange the two sides.

Olarte, Santos, Spreer and Stump conjectured that every dual pair in a
`d`-dimensional flag complex without boundary occurs up to isomorphism on the
boundary of the `(d + 1)`-dimensional cross-polytope. The journal numbers
this conjecture 3.5. It is Conjecture 3.8 in the preprint. The authors’
broader conjecture concerns the size of intersecting families of facets.
That question remains open. [Journal article](https://doi.org/10.1016/j.jcta.2019.105205) ·
[Preprint, definitions and conjecture](https://arxiv.org/pdf/1710.02518#page=14)

## Counterexample

Take the nine cells `(i,j)` of a three-by-three grid, with indices modulo
three. Join distinct cells when they share a row or a column. Add three
vertices `h₀, h₁, h₂`. Join `hₖ` to the six cells for which `j − i ≠ k`.
Take all cliques of this graph as faces.

Every clique of grid cells lies in a row or column. The neighbors of each
`hₖ` form a six-cycle. Its vertices are the edges of the bipartite graph
`K₃,₃` after one perfect matching is removed, with consecutive edges adjacent.
The facets are the six grid lines and the eighteen triangles obtained by
joining a center to an edge of its six-cycle. Each grid edge lies in its
grid line and one center triangle. Each edge at a center lies in two
triangles of that center. The complex is pure of dimension two and has
no boundary.

Any face meeting all three rows must contain a cell from each row. Those
three cells are pairwise adjacent, so they form one column. Conversely,
every column meets all three rows. Interchanging rows and columns proves
the reverse duality. All nine cells occur in the three minimal rows.

## Verification and provenance

[Statement.lean](Statement.lean) defines the published conjecture.
[Solution.lean](Solution.lean) checks the finite complex and both duals,
then rules out an injection of the nine essential vertices into the six
vertices of the octahedron. Run these commands from the repository root.

```sh
lake build conjectures.OlarteSantosSpreerStump.Solution
python3 scripts/verify.py
```

OpenAI Codex assisted with the construction and Lean proof. An independent
enumeration of all 4,096 vertex subsets found 73 faces, including the empty
face, and 24 triangular facets. A search of the papers citing the journal
article and of publications on its dual-pair conjecture found no earlier
counterexample.

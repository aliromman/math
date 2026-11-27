# Solution to Ferroni and Schröter’s Problem 3.5 on the initial entries of matroid base polytope f-vectors

For every $c$, two connected rank-two matroid base polytopes can have the same number of elements and the same first $c$ face counts, while their numbers of facets differ by one.

Luis Ferroni and Benjamin Schröter asked whether a universal number of initial entries determines the full $f$-vector of a matroid base polytope. Here $f_k$ counts the $k$-dimensional faces. Their experiments found that five entries suffice for connected matroids on at most nine elements. Our construction gives a negative answer for matroids of unbounded size, even when rank, ground-set size and connectedness are given. [Problem 3.5 in the journal article](https://doi.org/10.1017/S0963548325000021)

## A pair built from subsets

Choose $m\ge4$ with $m>c+1$. For each nonempty subset $S$ of $[m]$, make one class containing the $2|S|$ elements

```math
(S,j,b),\qquad j\in S,\quad b\in\{0,1\}.
```

Use the even-sized subsets for one matroid and the odd-sized subsets for the other. In both, a basis is any pair of elements from different classes. There are at least three classes, so both matroids are connected. The two ground sets have equal size. For a fixed $j$, toggling any other label in $S$ pairs the even and odd possibilities.

For $m=4$, the even matroid has six classes of size four and one of size eight. The odd matroid has four classes of size two and four of size six. Both have 32 elements and 432 vertices. Their numbers of facets are 39 and 40.

## Why the small faces agree

The support of a face consists of the elements used by at least one of its vertices. Its vertices are the bases that maximize the sum of two element weights. There are two possible shapes.

- If the highest weight occurs in at least three classes, take all pairs of highest-weight elements from different classes. On a support of size $s$, the face has dimension $s-1$.
- Otherwise, the maximizing pairs form a complete bipartite graph. One side lies in one class, and the other lies outside it. On a support of size $s$, the face has dimension $s-2$.

These descriptions also run in reverse. To expose the first shape, give its support weight one and the other elements weight zero. For the second shape, give its two sides weights two and one, and the other elements weight zero. The dimension counts follow by taking differences of indicator vectors. In the first shape, fix one element as an anchor. Given any two support elements, a third class supplies a common partner, so their coordinate difference is an edge direction. In the second shape, fix one anchor on each side. The differences from the other elements to their own anchors form a basis for the directions of the face.

A $k$-face therefore uses at most $k+2$ elements. If $k<c$, there is a label $r$ absent from every marked position $j$ on its support. Choose the least such label and change each class $S$ to $`S\mathbin{\triangle}\{r\}`$. This keeps $j$ in its class, reverses parity and preserves all equalities and inequalities between class labels. The image has the same shape and dimension. Its marked positions stay the same, so toggling again gives the original face. Thus the two polytopes have equal $f_k$.

## Where the counts separate

Write $n$ for the common ground-set size. Each polytope has dimension $n-1$. A facet of the first shape omits one element. All classes have at least two elements, so each of the $n$ choices gives a facet. A facet of the second shape uses all elements and separates one whole class from the rest. Since there are at least three classes, each choice of a class gives a distinct facet. Consequently

```math
f_{n-2}=n+\#\{\text{classes}\}.
```

Toggling a fixed label pairs all even and odd subsets. The empty subset supplies no elements, so the even matroid has exactly one fewer class and one fewer facet.

## Source and verification

Ferroni and Schröter give a general rank-two face formula in Corollary 2.12. Their Problem 3.5 asks how much of the resulting sequence determines the rest. Searches of the paper's citations and subsequent work on face and flag counts found no earlier answer to this question. OpenAI Codex derived the parity construction and formalized the proof. [Original paper](https://arxiv.org/abs/2310.05487) · [Subsequent work on flag counts](https://arxiv.org/abs/2512.05250)

The Lean statement uses the basis-exchange axiom. It defines faces by maximizing real linear functionals and measures their affine dimension in the real coordinate space of the indicator vectors. From the repository root, run

```sh
# Run at the merge commit for PR #30.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

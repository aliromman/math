# Solution to Faustini and Vargas’s Problem 6.7 on flag vectors of connected split matroids

Two connected rank-three matroids on 11 elements have the same number of faces in every dimension. Their base polytopes have **75,887** and **75,888** incidences between a vertex and a four-dimensional face. This answers the question of Faustini and Vargas in the negative. They proved that the ordinary face counts do determine all flag counts for connected sparse paving matroids. [Problem 6.7 in the revised preprint](https://arxiv.org/html/2512.05250v2#S6.SS4) · [Problem 6.5 in the original paper](https://arxiv.org/html/2512.05250v1#S6.SS2)

## The two matroids

Use the ground set $`\{0,1,\ldots,10\}`$. The bases are the triples that lie in none of the six specified lines. A vertex of the base polytope is the indicator vector of a basis.

| Matroid | Lines of size 3 | Lines of size 4 | Line of size 5 |
| --- | --- | --- | --- |
| $A$ | $`\{0,1,5\},\ \{0,2,6\},\ \{0,3,4\}`$ | $`\{1,3,7,8\},\ \{2,4,7,9\}`$ | $`\{5,6,8,9,10\}`$ |
| $B$ | $`\{0,1,2\},\ \{3,4,5\},\ \{6,7,8\}`$ | $`\{0,3,6,9\},\ \{1,4,7,10\}`$ | $`\{2,5,8,9,10\}`$ |

In each row, two distinct lines have at most one point in common. The six inequalities that bound each line's rank by two give a split matroid. Any two ground elements can replace one another in a suitable basis, so each matroid is connected. Both face vectors, starting with vertices and ending with the whole polytope, are

$$
(144,1518,5146,9224,10368,7802,3970,1324,268,28,1).
$$

## Why one incidence survives

The cd-index $\Psi$ records the numbers of nested faces of every choice of dimensions. In the formula of Faustini and Vargas, the individual line contributions cancel between $A$ and $B$ since their line sizes agree. Only the counts of intersecting line pairs can differ. For the size pairs $(3,3),(3,4),(3,5),(4,4),(4,5)$, the counts in $A$ minus those in $B$ are respectively $3,-2,-1,1,0$. [Theorem 5.5 and Lemma 5.4](https://arxiv.org/html/2512.05250v2#S5.SS2)

For a pair of intersecting lines of sizes $r,s$, the coefficient for choosing $i,j\ge2$ of their other points is $\binom{r-1}{i}\binom{s-1}{j}$. In the difference of the two formulas, the coefficients for $i+j=4$ and $5$ cancel after exchanging the two factors when needed. At $i+j=6$ only $(3,3)$ and $(2,4)$ survive, with opposite signs. Write $\Delta_m$ for an $m$-dimensional simplex. The formula reduces to

```math
\Psi(B)-\Psi(A)=
  \bigl(\Psi(\Delta_2\times\Delta_2)-\Psi(\Delta_1\times\Delta_3)\bigr)
  \,d\,\Psi(\Delta_4).
```

Both products in parentheses have dimension four, so their $c^4$ coefficients are both one. Every surviving monomial in the full difference therefore contains at least two copies of $d$. Under $c=a+b$ and $d=ab+ba$, every term contains at least two copies of $b$. This proves equality of all ordinary face counts. A vertex–four-face flag takes its first $b$ at position 0 and its second at position 4. Its difference is the difference in vertex counts of the two products, $3\cdot3-2\cdot4=1$.

## Independent verification

The Lean proof counts the faces from their definition as maximizers of real linear functionals. At each basis it lists the exchanges that can be tight. Their vectors span the direction space of the face. The exchange graph gives its real dimension. Counting a face at its least basis gives the ordinary face counts. Counting it at every incident basis gives the vertex–face counts. The kernel checks all finite counts.

The revised preprint reports an affirmative computational check through 12 elements. Alejandro Vargas independently ran the authors’ own code on these two 11-element matroids and confirmed that the reported check was incorrect. The authors intend to correct it. The current public source is the revised preprint. The public supplement includes selected cases and a sample six-element database loop. It does not give the input list for the reported 12-element check. A search of the revised preprint, its supplement, and subsequent references found no earlier counterexample. OpenAI Codex constructed the pair and wrote the formal proof. An independent agent checked the formal statement against the paper and recovered both face vectors and both incidence counts by intersecting the 28 facet inequalities. [Published calculator, revision 3cbf521](https://github.com/AV-2/cd-index-matroid-base-polytope/blob/3cbf5219623200cca156bcbfc735f34432f8d6e4/CDcalculate.sage)

From the repository root, run

```sh
# Run at the merge commit for PR #40.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

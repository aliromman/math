# Four added cells allow 589 permutations instead of 584

Start with the eight-by-eight board whose cells on or below the main diagonal are allowed. Add four cells above the diagonal. Hwang proposed the antidiagonal cells $(1,8),(2,7),(3,6),(4,5)$. They allow 584 permutations. The four cells

$$
(1,8),\quad(2,6),\quad(2,7),\quad(3,7)
$$

allow 589. Coordinates start at one. A permutation is allowed if each of its eight occupied cells is allowed.

## Original conjecture

Suk-Geun Hwang conjectured that for every $n\ge1$ and $2d\le n$, the lower triangular board gains the most allowed permutations when its $d$ additional cells are $(i,n+1-i)$ for $1\le i\le d$. The number of allowed permutations is the permanent of the board's zero-one matrix. Hwang proved the construction is optimal when $n$ is sufficiently large relative to fixed $d$. The example above has $n=2d$. [Hwang, *Permutations with partially forbidden positions*, Journal of the Korean Mathematical Society 38 (2001), pp. 793–808, Section 3, p. 803](https://mathnet.or.kr/mathnet/kms_tex/977985.pdf)

## Counting the permutations

Group the allowed permutations by how many of their entries lie above the diagonal.

| Added cells used | 0 | 1 | 2 | 3 | 4 | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Antidiagonal | 1 | 85 | 294 | 180 | 24 | 584 |
| Counterexample | 1 | 96 | 396 | 96 | 0 | 589 |

To reproduce a column of this table, choose the indicated number of added cells with distinct rows and columns. Delete their rows and columns. Fill the remaining rows in increasing order, using only columns on or below the diagonal. In each row, multiply by the number of eligible surviving columns minus the number of rows already filled. The eligible sets are nested, so this count is independent of the earlier choices. Sum over the selections of added cells. Hwang's Equation (1) gives the same product for a Ferrers matrix.

## Verification and attribution

`Statement.lean` defines Hwang's conjecture with Mathlib's matrix permanent. `Solution.lean` proves Ryser's inclusion-exclusion formula from the permutation sum and evaluates both permanents in the Lean kernel. From the repository root, run

```sh
lake build conjectures.HwangPermanent.Solution
lake env leanchecker conjectures.HwangPermanent.Solution
```

An OpenAI Codex agent found the counterexample and wrote the proof. A direct enumeration of all $8!$ permutations confirmed the table. Searches for the paper, its title, Hwang's construction and prior counterexamples found no earlier disproof.

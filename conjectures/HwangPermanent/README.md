# Disproof of Hwang’s conjecture on adding cells to a triangular permutation board

Start with the eight-by-eight board whose cells on or below the main diagonal are allowed. Add four cells above the diagonal. Hwang proposed the antidiagonal cells $(1,8),(2,7),(3,6),(4,5)$. They allow 584 permutations. The four cells

$$
(1,8),\quad(2,6),\quad(2,7),\quad(3,7)
$$

allow 589. The same change in the middle eight rows and columns defeats the proposed construction in every even order $n=2d\ge 8$. Coordinates start at one. A permutation is allowed if all its occupied cells are allowed.

## Original conjecture

Suk-Geun Hwang conjectured that for every $n\ge1$ and $2d\le n$, the lower triangular board gains the most allowed permutations when its $d$ additional cells are $(i,n+1-i)$ for $1\le i\le d$. The number of allowed permutations is the permanent of the board's zero-one matrix. Hwang proved the construction is optimal when $n$ is sufficiently large relative to fixed $d$. The example above has $n=2d$. [Hwang, *Permutations with partially forbidden positions*, Journal of the Korean Mathematical Society 38 (2001), pp. 793–808, Section 3, p. 803](https://mathnet.or.kr/mathnet/kms_tex/977985.pdf#page=11)

## Counting the permutations

Group the allowed permutations by how many of their entries lie above the diagonal.

| Added cells used | 0 | 1 | 2 | 3 | 4 | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Antidiagonal | 1 | 85 | 294 | 180 | 24 | 584 |
| Counterexample | 1 | 96 | 396 | 96 | 0 | 589 |

To reproduce a column of this table, choose the indicated number of added cells with distinct rows and columns. Delete their rows and columns. Fill the remaining rows in increasing order, using only columns on or below the diagonal. In each row, multiply by the number of eligible surviving columns minus the number of rows already filled. The eligible sets are nested, so this count is independent of the earlier choices. Sum over the selections of added cells. Hwang's Equation (1) gives the same product for a Ferrers matrix.

## Why the counterexample persists

Let $r_k(B)$ count placements of $k$ rooks on allowed cells of $B$, with at most one rook in each row and column. Write $A$ for the eight-by-eight antidiagonal board and $B$ for the counterexample. Their differences, in order from $k=0$ to $8$, are

$$
r_k(B)-r_k(A)=(0,0,2,44,314,875,909,269,5).
$$

These nine numbers can be checked one row at a time. For each row, either leave it empty or place a rook in one of its allowed columns that is still unused.

For $n=2d$, leave the $d-4$ outer antidiagonal cells in place. Replace the pattern in the central eight-by-eight block. All eight central rows have the same allowed columns outside the block. All eight central columns also have the same allowed rows outside it. Fix the rooks placed wholly outside. If $t$ outside rows and $t$ outside columns remain, any central placement of $8-t$ rooks has exactly $(t!)^2$ completions whenever all the required connections are allowed. Otherwise it has none. Thus each central rook number has a nonnegative weight. The outside identity placement gives positive weight to $r_8$, so the total increases strictly.

## Verification and attribution

`Statement.lean` defines Hwang's conjecture with Mathlib's matrix permanent. The formal proof counts the eight-by-eight boards by inclusion-exclusion. To extend them, it uses the polynomial $P_A(x)=\mathop{\mathrm{per}}(A+xJ)$, where $J$ is the all-ones matrix. Its coefficient of $x^{8-k}$ on the initial board is $(8-k)!r_k(A)$. Adding two outer indices acts on this polynomial by differentiation, addition, and multiplication by polynomials with nonnegative coefficients. The proof verifies every coefficient of the initial difference and its positive constant term at every later order. From the repository root, run

```sh
# Run at the merge commit for PR #44.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

An OpenAI Codex agent found the counterexample and wrote the proof. A direct enumeration of all $8!$ permutations confirmed the table. Searches for the paper, its title, Hwang's construction and prior counterexamples found no earlier disproof.

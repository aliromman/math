# Disproof of Bajnok’s Conjecture 9 on the minimum size of restricted double sumsets in cyclic groups

Nineteen residues modulo 444 have only 34 sums of two distinct elements.
Béla Bajnok’s formula predicts 35. This disproves the formula for cyclic
groups and its later general form at two summands. The example gives an
upper bound of 34 for the restricted minimum. [Bajnok, Conjecture 9](https://doi.org/10.1007/s10474-015-0546-1)

## Counterexample

Let `H = {37j | 0 ≤ j < 12}` in ℤ/444ℤ. In ℤ/12ℤ, take Bajnok’s seven-element
set `C = {0, 1, 4, 5, 6, 9, 10}`, called `C₁` in his paper. Form the
19-element set `A = H ∪ {1 + 37c | c ∈ C}`. [Original construction of C₁, p. 4](https://arxiv.org/pdf/1305.2141#page=4)

Distinct pairs from `H` give every element of `H`, including zero from
`37 + 407`. Pairs with one element in each part give all of `1 + H`.
Distinct pairs from `C` give every residue modulo 12 except 0 and 8, so the
last part gives ten sums in `2 + H`. The three cosets are disjoint. The
restricted sumset therefore has size `12 + 12 + 10 = 34`.

## Why the formula predicts 35

Since 19 is odd and 36 does not divide 444, the formula takes the smaller of
35 and the minimum size of an ordinary double sumset of 19 residues. The
following argument bounds every such ordinary sumset from below by 35.

Use the Chinese remainder theorem to write the group as ℤ/12ℤ × ℤ/37ℤ.
Project a 19-element set onto the first coordinate. Let `S` be its support,
`r = |S|`, and `M` its largest fibre size. Fix an index `x` with a fibre
of size `M`. For each occupied index `y`, Cauchy–Davenport gives at least
`M + |Aᵧ| − 1` sums in the fibre at `x + y`. This number is at most 37.
Summing over the distinct indices and adding one for each remaining index
of `S + S` gives the lower bound

```text
19 + r(M − 1) + |S + S| − r.
```

If `r(M − 1) < 16`, the inequalities `r ≤ 12` and `rM ≥ 19` leave three cases.

- If `M = 2`, at least seven fibres have two elements. Their indices sum to
  all of ℤ/12ℤ, since two sets of size seven in this group intersect. Each
  sum fibre has at least three elements, giving at least 36 sums.
- If `r = 7` and `M = 3`, then `S + S` is all of ℤ/12ℤ. The bound is 38.
- If `r = 5` and `M = 4`, then `|S + S| ≥ 6`. Otherwise every translate
  `x + S` for `x ∈ S` would equal `S + S`. The sum of its elements is
  `5x + ∑ S`, which differs for different `x` because 5 is a unit modulo
  12. The bound is at least 35.

## Sources and verification

Bajnok restated the same twofold formula after Conjecture 5 in his 2017
survey and as Problem 9 in his 2024 chapter. A search of later papers citing
these sources found no earlier refutation. The new construction uses
Bajnok’s set as the partly filled coset in a larger cyclic group.
[2017 survey, pp. 5–6](https://arxiv.org/pdf/1512.03038v2#page=5) · [2024 chapter](https://doi.org/10.1007/978-3-031-62166-6_2)

OpenAI Codex assisted with the construction, mathematical review, and Lean
formalization. The Lean statement takes both minima over actual finite sets.
The proof checks the witness and the ordinary lower bound. To build and
replay the proofs from a clean checkout, run `python3 scripts/verify.py --fetch-cache`
from the repository root. [Verification instructions](../../README.md#verification)

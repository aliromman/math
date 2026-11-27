# Disproof of Bevan and Threlfall’s Conjecture 22 on unimodality of consecutive pattern counts

In a random permutation of seven letters, the expected number of consecutive copies of **51234** falls and then rises as the inversion count increases from 7 to 9.

| Inversions | Permutations | Total occurrences | Expected occurrences |
| ---: | ---: | ---: | ---: |
| 7 | 359 | 12 | $12/359$ |
| 8 | 455 | 15 | $3/91$ |
| 9 | 531 | 18 | $2/59$ |

Both outside entries in the last column exceed $3/91$. The number of occurrences increases across all three layers, but the number of permutations in each layer grows at a different rate.

Bevan and Threlfall conjectured that for every consecutive pattern $\pi$ and $n\ge |\pi|+2$, its expected number of occurrences in a uniformly random permutation with exactly $m$ inversions is unimodal as $m$ runs from zero to $\binom n2$. An occurrence of 51234 consists of five consecutive entries with the largest first and the other four increasing. Here $n=7$ and $|\pi|=5$, so the example satisfies the length condition. [Conjecture 22, *The Electronic Journal of Combinatorics* 31 (2024), #P4.6](https://doi.org/10.37236/12601)

## A calculation without enumeration

Write $[j]_q=1+q+\cdots+q^{j-1}$. Inserting the largest letter of a permutation in each possible position adds every inversion count from 0 to $j-1$ once. Thus the coefficient of $q^m$ in $`[7]_q!=\prod_{j=1}^7[j]_q`$ counts the permutations in layer $m$. The coefficients at $m=7,8,9$ are 359, 455 and 531.

Fix one of the three five-entry windows. Sorting the entries inside the window leaves every inversion involving a position outside it unchanged. Each sorted window has $5!$ reorderings, and their internal inversion enumerator is $[5]_q!$. Exactly one reordering has pattern 51234, with four internal inversions. Across all three windows the occurrence enumerator is therefore

$$
3q^4\frac{[7]_q!}{[5]_q!}=3q^4[6]_q[7]_q.
$$

The coefficients at degrees 7, 8 and 9 are $3\cdot4$, $3\cdot5$ and $3\cdot6$. Division by the three layer sizes gives the strict valley in the table. This one local valley rules out every possible peak.

## Verification and attribution

From a clean checkout, run

```sh
# Run at the merge commit for PR #69.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The formal statement defines the uniform average on each inversion layer and weak unimodality on the full range. The proof checks the three counts directly on permutations and rules out a peak on either side of 8. A separate AI researcher checked the statement against the journal paper and independently computed both generating functions. The final theorem’s guarded axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

Bevan and Threlfall posed the conjecture. OpenAI Codex found the example and developed the proof and formalization. A search by authors, conjecture number, and pattern-count unimodality found no earlier counterexample.

Bevan and Threlfall, “Thresholds for Patterns in Random Permutations with a Given Number of Inversions,” Electronic Journal of Combinatorics 31 (2024), P4.6, Conjecture 22, p. 20. The printed bound is n ≥ |π| + 2. [Publication](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p6/pdf/#page=20)

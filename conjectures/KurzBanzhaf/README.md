# Proof of Kurz and Napel’s conjecture on a voter with half the Banzhaf power of each other voter

For every committee of $n\geq 6$ voters, there is a voting rule under which each of the first $n-1$ voters can change the outcome exactly twice as often as the last voter. Its normalized Banzhaf power vector is

$$
\frac{(2,\ldots,2,1)}{2n-1}.
$$

Sascha Kurz and Stefan Napel verified the cases $6\leq n\leq18$ and conjectured the result for every $n\geq19$. Kurz restated the conjecture in *Ready for the design of voting rules?*, *Homo Oeconomicus* 32 (2015), 117–129. A simple game is a yes-or-no rule under which the empty coalition loses, the full coalition wins, and adding voters to a winning coalition preserves the win. The normalized Banzhaf index divides each voter's count of decisive switches from no to yes by the total count for all voters. [Kurz and Napel, Section 5.3, p. 15](https://arxiv.org/pdf/1202.6245#page=15) · [Conjecture 9 in the author's revised text](https://www.researchgate.net/publication/262992098_Ready_for_the_Design_of_Voting_Rules) · [Conjecture 16 in the 2014 preprint](https://arxiv.org/pdf/1405.0823#page=7)

## Proof

Let $L$ be the number of losing coalitions. Let $b_i$ be voter $i$'s number of decisive switches. Add two voters who can pass the proposal together. The enlarged committee passes the proposal if the old committee passes it or both new voters vote yes.

There are three losing vote combinations for the new pair. Each old decisive switch therefore has three extensions. For each new voter, a switch is decisive precisely when the other new voter votes yes and the old committee loses. The new counts are

$$
L'=3L,\qquad b'_i=3b_i\quad(i\text{ old}),\qquad b'_i=L\quad(i\text{ new}).
$$

Thus a rule with ordinary count $2t$, exceptional count $t$, and $L=6t$ gives another such rule with two more voters and parameter $3t$. Two starting rules cover both parities. The first three rows below cover the smaller committees.

| Voters | Losing coalitions | Decisive switches per ordinary voter | Decisive switches for the last voter |
|---:|---:|---:|---:|
| 6 | 14 | 8 | 4 |
| 7 | 20 | 12 | 6 |
| 8 | 88 | 32 | 16 |
| 9 | 204 | 68 | 34 |
| 10 | 372 | 124 | 62 |

Each starting rule specifies maximal losing vote totals for three groups of ordinary voters and the last voter. A coalition loses if its four vote totals are at most the four entries of one listed tuple. For example, with seven voters, divide the ordinary voters into two groups of three. Without the last voter, a coalition loses when it contains at most two voters from one group and none from the other. With the last voter, it loses when it contains at most one ordinary voter. There are $13+7=20$ losing coalitions. Each ordinary voter belongs to four, and the last voter belongs to seven. A voter belonging to $d$ losing coalitions has $L-2d$ decisive switches, since each such coalition pairs with the losing coalition obtained by removing that voter. This gives the counts $12$ and $6$. All five rules and the checks of every entry are in [Seeds.lean](Seeds.lean).

## Prior work and verification

The construction above extends the finite computations to every $n\geq6$. A search for the conjecture, its target vector, and later work on the inverse Banzhaf problem found the published finite computations and no earlier general proof. [Kurz and Napel](https://arxiv.org/pdf/1202.6245#page=15)

From the repository root, run

```sh
# Run at the merge commit for PR #55.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The project pins Lean 4.36.0 and Mathlib. [Statement.lean](Statement.lean) defines the exact power-vector claim. [Solution.lean](Solution.lean) proves it and checks its axioms. OpenAI Codex developed the construction, found the finite rules, and wrote the Lean proof.

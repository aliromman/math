# Three fair dice that neither of the proposed moves can change

Roll any two of these eight-sided dice. Each wins exactly 32 of the 64 possible rolls.

| Die | Face labels |
|---|---|
| A | 1, 2, 7, 12, 18, 19, 20, 21 |
| B | 3, 8, 9, 13, 14, 15, 16, 22 |
| C | 4, 5, 6, 10, 11, 17, 23, 24 |

Injo Hur and Yeansu Kim conjectured that two operations suffice to turn every fair triple into repetitions of a six-letter palindrome such as `ABCCBA`. For these dice, neither operation can even make a first change. This disproves Conjecture 1 of their journal article, numbered 3.5 in the preprint. [Journal article, §3](https://doi.org/10.1155/2021/6648248) · [Preprint](https://arxiv.org/abs/2006.12866)

## Why the word is isolated

Read the die names in order of increasing face label.

```text
AABCCCABBCCABBBBCAAAABCC
```

The first operation exchanges a neighboring pair `xy` and a neighboring pair `yx` elsewhere. The only transitions between different letters in this word are `AB`, `BC`, and `CA`. None occurs in reverse.

The second operation slides a permutation of `ABC` across an adjacent segment containing equal numbers of all three letters. To check all possible slides, record the two differences $(\#A-\#C,\#B-\#C)$ after each prefix. A segment has equal counts exactly when the differences are the same at its two ends.

| Three-letter block | Number of letters before the block | Prefix differences there | All prefix lengths with those differences |
|---|---:|---:|---|
| ABC | 1 | $(1,0)$ | 1, 4 |
| CAB | 5 | $(0,-1)$ | 5, 8 |
| CAB | 10 | $(-1,-1)$ | 10, 13 |
| BCA | 15 | $(-1,1)$ | 15, 18 |
| ABC | 20 | $(1,1)$ | 20, 23 |

These are all the three-letter permutations in the word. Each row gives just the two ends of its block. A slide across a nonempty segment needs a third occurrence of the same differences. The word therefore stays fixed. It starts with two equal letters, whereas every proposed block starts with two different letters. The same obstruction works even if the order of the letters can change from block to block.

## Source and verification

Related work gives algorithms for listing words with the same scattered pair counts. Hur and Kim ask whether their two particular moves can connect fair triples. Searches for the conjecture, its moves, and this example found no prior refutation. OpenAI Codex found the word by searching cyclic sequences of letter runs and formalized the proof. [Lejeune, Rigo and Rosenfeld on pair-count equivalence](https://www.lirmm.fr/~mrosenfeld/LejeuneRigoRosenfeld.pdf)

From the repository root, run

```sh
lake exe cache get
lake build conjectures.HurKimFairDice.Solution
lake env leanchecker conjectures.HurKimFairDice.Solution
```

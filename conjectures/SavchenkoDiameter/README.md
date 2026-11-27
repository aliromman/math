# Disproof of Savchenko’s conjecture on minimum cycle counts in tournaments of bounded diameter

Two tournaments on 22 vertices have diameter eight. Savchenko’s proposed minimizer has **68 directed four-cycles**. Moving one vertex from an end block to the middle gives **67**. A second example on 18 vertices reduces the number of five-cycles from 44 to 42.

In 2012, Sergey Savchenko conjectured that a single tournament $T_{d,n}$ minimizes the number of directed cycles of every length among all strongly connected tournaments on $n$ vertices with diameter at most $d$. The conjecture holds when $d=n-1,n-2,n-3$. His later paper states the full inequality and an equality condition as Conjecture 1. [Original paper, *Journal of Graph Theory* 70 (2012), 361–383](https://doi.org/10.1002/jgt.20615) · [Conjecture 1, pp. 2–3](https://arxiv.org/pdf/2311.13377#page=3)

## The counterexample

Line up nine blocks. Every block beats the next block. Between blocks farther apart, all arcs point back toward the earlier block. Inside each block, an earlier vertex beats each later vertex.

| Tournament | Block sizes from left to right | Four-cycles |
| --- | --- | ---: |
| $T_{8,22}$ | 7, 1, 1, 1, 1, 1, 1, 1, 8 | 68 |
| Competitor | 7, 1, 1, 1, 2, 1, 1, 1, 7 | 67 |

Going from the first block to the last takes eight arcs. Every other ordered pair is reachable within eight arcs. In particular, two vertices in the same block can travel in either direction through a directed triangle of blocks.

Each four-cycle passes through either four consecutive blocks or three consecutive blocks with two vertices in one of them. For four blocks, choose one vertex in each. For three, choose the pair in its required internal order and one vertex in each other block. These cases exhaust the cycles because a step forward advances at most one block, and two separated visits to the same block would require two directed circuits of blocks, each of length at least three.

Start with one vertex per block. There are six four-cycles, one for each run of four consecutive blocks. Enlarging an end block to size $t$ adds $\binom{t}{2}+t-1$ cycles. Enlarging the middle block to size $t$ adds $3\binom{t}{2}+4(t-1)$. No run of four blocks includes two of the three enlarged blocks. Shrinking the last block from eight vertices to seven therefore removes eight cycles, while doubling the middle block adds seven.

The five-cycle example uses eleven blocks. The proposed model has end sizes 4 and 5. The competitor has end sizes 4 and 4 and doubles the middle block. The distance from end to end is ten. In the proposed model each five-cycle passes through three, four or five consecutive blocks. Shrinking the last block removes $1+4+\binom{4}{2}=11$ cycles. Doubling the middle block adds $5+4=9$.

## Verification and attribution

The proof enumerates each directed cycle once, starting at its least vertex. It also computes the vertices reachable from each starting point to check the diameter exactly in both counterexamples. Searches for the original article, the later paper and results on the minimum number of short cycles at fixed diameter located the known special cases and no earlier counterexample. OpenAI Codex found the examples and formalized the disproof.

```sh
# Run at the merge commit for PR #91.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines the proposed extremal tournament and the full conjecture. `Solution.lean` proves `resolution` and verifies both examples.

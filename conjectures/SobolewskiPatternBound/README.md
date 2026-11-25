# A predicted bound below 17 allows arbitrarily long binary progressions

Color each nonnegative integer by the parity of the number of occurrences of the binary pattern `100000` in its expansion. The 32 multiples
$0,d,2d,\ldots,31d$ with $d=2^{14}-1=16383$ all have color zero. Sobolewski’s proposed bound on their number is less than 17.

For every $j\ge5$, the same construction gives at least $2^j$ terms where the proposed bound stays below 17. This refutes Conjecture 2 of *On monochromatic arithmetic progressions in binary words associated with pattern sequences*. The pattern varies with $j$. The question concerning the optimal asymptotic intercept for each fixed pattern remains open. [Journal article, Proposition 5.3 and Conjecture 2](https://doi.org/10.1016/j.tcs.2024.114815) · [Preprint, Proposition 5.4 and Conjecture 2](https://arxiv.org/pdf/2204.05287#page=25)

## Why the progression is monochromatic

Use the pattern $v=10^j$, a one followed by $j$ zeros, and set $K=2j+4$ and $d=2^K-1$. For $1\le n<2^j$,

$$nd=(n-1)2^K+(2^K-1-(n-1)).$$

The binary expansion therefore joins $n-1$ to its complement in a block of $K$ bits. The upper part has at most $j$ bits. The lower part starts with ones and its last $j$ bits cannot all be zero, since $n-1<2^j-1$. Neither part contains a one followed by $j$ zeros, and the intervening ones prevent a match across the boundary. Zero has no occurrence either.

## The proposed bound

Write $A_v(0,d)$ for the maximal length of a monochromatic progression of step $d$ starting at zero. Sobolewski predicted $A_v(0,d)\le C_vd+B_v$ for every $d\ge2^{2|v|+1}$, with a precise equality condition. The constants come from the lexicographically first pair of binary blocks satisfying the parity condition of Proposition 5.3 in the journal version.

For $v=10^j$, that pair has values $(1,1)$. When the first block is zero, the two potentially nonzero occurrence counts agree and cancel modulo two. The pair $(1,0)$ also gives zero. For $(1,1)$, the word of value $2^j+1$ misses the pattern and the word of value $2^j$ contains it once. Hence

$$C_v=2^{-2j},\qquad B_v=1-2^{-j},\qquad C_vd+B_v=17-2^{-j}-2^{-2j}.$$

The step $d$ exceeds the conjecture’s threshold. A remark after Proposition 5.6 gives zero as the second block in this case. The calculation above uses the defining parity condition. The disproof holds with its larger, corrected intercept.

## Verification and prior work

The author's computations reported in the supplement cover patterns of length at most four. Searches using the conjecture number, the general pattern sequence, and the runs of zeros found no previous refutation of this bound. The Thue–Morse and Rudin–Shapiro conjectures concern different patterns. OpenAI Codex derived the construction and wrote the Lean proof. [Author’s computation files](https://github.com/BartoszSobolewski/Monochromatic-arithmetic-progressions)

The proof checks overlapping occurrences, the leading-zero convention, the extremal pair of blocks, the step threshold and the full family of progressions. The conjecture statement also includes the proposed asymptotic intercept and the equality condition.

```sh
lake exe cache get
lake build conjectures.SobolewskiPatternBound.Solution
lake env leanchecker conjectures.SobolewskiPatternBound.Solution
```

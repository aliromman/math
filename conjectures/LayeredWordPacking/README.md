# Disproof of the finite layered-maximizer assertion in Burstein, Hästö and Mansour’s Conjecture 2.8

The nine-letter word `111342222` contains **61** subsequences of type `11123`, `13222`, or `11322`. Every layered nine-letter word on the same four-letter alphabet contains at most **60**. The layered word `113322222` attains 60.

In a layered word, the letters within each layer decrease weakly, and every letter in one layer is smaller than every letter in the next. For example, `11|3222` is layered. The three patterns in this example are layered. A subsequence has the same type as a pattern if every comparison of letters, including equality, agrees.

Burstein, Hästö and Mansour conjectured that for every set of layered patterns of one length, some layered word maximizes their total number of occurrences at each fixed word length and alphabet size. This extends a theorem for permutations to words with repeated letters. The counterexample refutes the finite assertion in their Conjecture 2.8. Barton proved the equality of limits also stated there, restated the finite assertion as Conjecture 5, and proved it in special cases. Searches for the conjecture under both attributions found no earlier counterexample. [Burstein, Hästö and Mansour, §2](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_9/PDF/v9i2r20.pdf) · [Barton, §3](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v11i1r80/pdf/)

## Count

In `111342222`, `11123` occurs once, using the initial three ones and the letters `34`. The high letter in either other pattern can be `3` or `4`. Their contributions are respectively $3\cdot2\binom43=24$ and $\binom32\cdot2\binom42=36$.

To check the layered bound by hand or by a short enumeration, choose which of the three gaps in the alphabet `1234` separate layers. Within each layer put the letters in descending order. Give each letter a nonnegative multiplicity, with the four multiplicities summing to nine. Zero multiplicities also cover words with missing letters. The table gives the maximum over the $\binom{12}{3}=220$ assignments for each row.

| Order of the letter blocks | Maximum |
| --- | ---: |
| `4321` | 0 |
| `1·432` | 60 |
| `21·43` | 60 |
| `1·2·43` | 60 |
| `321·4` | 0 |
| `1·32·4` | 60 |
| `21·3·4` | 40 |
| `1·2·3·4` | 60 |

## Verification

`Statement.lean` defines layering by cuts at strict rises. It states both published formulations. `Proof.lean` uses a separate enumeration. It prepends one letter at a time, proves that the list includes every layered word, and checks the counts in the Lean kernel. Run from the repository root.

```sh
# Run at the merge commit for PR #17.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

OpenAI Codex found the pattern set and witness by a search over words with consecutive repeated letters. Codex wrote the proof and its Lean formalization.

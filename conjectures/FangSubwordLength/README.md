# Disproof of Fang’s Conjecture 5.7 on the length of a most frequent subsequence

The ten-letter word `ababacdcdc` has a unique most frequent subsequence, `abacdc`. Its six letters occur in 16 ways.

Fang conjectured that every word of length $n\ge 2$ has a most frequent subsequence with at most $\lceil n/2\rceil$ letters. An occurrence is a set of positions. The selected positions can have gaps. The conjecture would have allowed a search for a most frequent subsequence to discard all longer candidates. [Wenjie Fang, *Maximal number of subword occurrences in a word*, Journal of Experimental Mathematics 1 (2025), 218–238, Conjecture 5.7 on p. 236](https://doi.org/10.56994/JXM.001.002.002)

## Proof

In `ababa`, the subsequence `aba` occurs at positions 123, 125, 145 and 345. Every other subsequence occurs at most three times. The second block `cdcdc` has the same property after relabeling its two letters.

The two blocks have disjoint alphabets. Every subsequence that occurs can therefore be split in exactly one way into its part from each block. The numbers of choices of positions multiply. This gives the unique maximum $4\cdot4=16$.

More generally, concatenate $r$ copies of `ababa`, each on its own pair of letters. The resulting word has length $5r$. Its unique most frequent subsequence has length $3r$ and occurs $4^r$ times. The difference from the proposed bound grows without limit.

## A binary counterexample

| Word | Length | Unique most frequent subsequence | Occurrences |
|---|---:|---|---:|
| `ababaaabbbabab` | 14 | `abaabbab` | 144 |

Among subsequences of length at most seven, the largest frequency is 136, attained by `ababab`. To reproduce the counts, split the occurrences according to whether they use the first input position. For letters $a,b$ and words $w,v$, this gives

$$
\operatorname{occ}(aw,bv)=\operatorname{occ}(w,bv)+[a=b]\operatorname{occ}(w,v).
$$

An empty pattern occurs once. A nonempty pattern occurs zero times in an empty input. The Lean proof checks the binary counts against all subsequences of this word.

## Verification and attribution

`Statement.lean` states the conjecture for every finite alphabet. `Solution.lean` proves the product formula, the family of counterexamples, and the binary optimum.

```sh
lake exe cache get
python3 scripts/verify.py
```

Fang proposed the length cutoff. Bukh and Saatashvili later studied the growth of the smallest possible maximum frequency. A search by conjecture number, title, witness and subsequence terminology found no earlier resolution of the length conjecture. AI researchers derived the construction, found the binary example, and wrote the Lean proof. [Bukh and Saatashvili, *Most frequent subsequences in a word*](https://arxiv.org/abs/2509.22619)

Wenjie Fang, Maximal number of subword occurrences in a word, Conjecture 5.7, p. 236. [Publication](https://jexpmath.org/index.php/jem/article/view/Vol-1Issue-2Paper-2)

# Infinite four-letter counterexamples to Brauner et al.’s Conjecture 4.1 on balanced words

For each $k\ge2$, repeat $\mathtt C(\mathtt{AB})^{k-1}\mathtt D(\mathtt{AB})^k$. These balanced words all escape binary congruence expansion. Their distinct least periods $4k$ give infinitely many different words, even up to translation. This refutes the fixed-alphabet finiteness prediction of Brauner, Crama, Delaporte, Jost and Libralesso. [Author manuscript, abstract](https://orbi.uliege.be/bitstream/2268/230109/1/Balanced%20words%20Dec%202018.pdf)

At $k=4$ the 16-letter block

$$
\mathtt{C\,ABABAB\,D\,ABABABAB}
$$

repeats to give a balanced word of least period 16 that cannot arise from a balanced binary word by congruence substitutions. Brauner, Crama, Delaporte, Jost and Libralesso conjectured that every balanced word on $N$ letters is such an expansion or has period at most $2^N-1$. At four letters their bound is 15. [Conjecture 4.1, *Theoretical Computer Science* 793 (2019), 169–180](https://doi.org/10.1016/j.tcs.2019.06.017) · [Author manuscript](https://orbi.uliege.be/bitstream/2268/230109/1/Balanced%20words%20Dec%202018.pdf)

The letter C occurs once per block, so the least period is $4k$.

## Why the word is balanced

A word is balanced when two intervals of equal length differ by at most one in their count of each individual letter. Put $p=4k$ and $a=2k-1$. At position $j$, take the residue $r=ja\bmod p$. Give the residues $0,\ldots,a-1$ to A, $a,\ldots,2a-1$ to B, $2a$ to C, and $2a+1$ to D. Reading from position 2 gives the displayed block. Moving two positions advances the residue by $2a\equiv-2\pmod p$.

An A occurs exactly when the rotation by $a$ crosses zero. Thus an interval of length $L$ contains either $\lfloor La/p\rfloor$ or $\lceil La/p\rceil$ copies of A. B is the same indicator shifted by one position. C and D each occupy a single residue class of positions since $a^2\equiv1\pmod p$. Each of the four indicators is balanced.

## Why the word has no binary expansion

A congruence substitution replaces the successive occurrences of one letter by a word in which each new letter occupies one arithmetic progression of occurrence indices. After any finite sequence of substitutions, a final letter still occupies one arithmetic progression among the occurrences of its binary ancestor. Its number of occurrences per period therefore divides that ancestor's count. For a progression of stride $s$, count across $s$ full periods to see this directly.

A and B each occur $a$ times, and C and D each occur once. The group of descendants containing A has total count divisible by $a$. Its common letters contribute a multiple of $a$, and its rare letters can contribute only 0, 1, or 2. As $a\ge3$, it contains neither rare letter. The same argument applies to B. A binary ancestor must therefore put C and D together and A and B together.

The interval from C through D has length $2k$ and contains both rare letters. The following $2k$ positions contain neither. Their binary ancestor would have two equal-length intervals whose counts differ by two.

## Scope and verification

The authors describe their four-letter analysis as a proof of that case in the introduction. Theorem 5.4 and its appendix classify **density vectors**. The vector here also has a Graham expansion realization. For example, begin with the binary block $X^{2k-1}Y$, then alternate A and B on the X occurrences and C and D on the Y occurrences. Conjecture 4.1 quantifies over individual words. Its two alternatives both fail for the ordering displayed above.

Restivo and Rosone had already printed a different period-16 balanced word, $\mathtt{ABDACBADBACBADBC}$, in a study of coordinatewise products. In retrospect it also contradicts the numerical bound. Its counts $(5,5,3,3)$ force the same binary grouping by divisibility. Two length-eight factors, $\mathtt{BADBACBA}$ and $\mathtt{DBCABDAC}$, contain six and four common letters. The additional result here is an explicit infinite family with unbounded least periods. This settles the fixed-alphabet finiteness prediction in the 2019 abstract. Searches for this prediction, congruence expansions and indecomposable balanced sequences located no earlier unbounded family. [Restivo and Rosone, *On the product of balanced sequences*, p. 144 (2012)](https://www.numdam.org/item/10.1051/ita/2011116.pdf)

From the repository root, run

```sh
# Run at the merge commit for PR #49.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` defines two-sided words, balance, and the finite sequence of substitutions in Definitions 2.7 and 2.8. `Expansion.lean` proves the divisibility condition for every such sequence. `Construction.lean` identifies the displayed word and counts its letters on every interval. `Solution.lean` proves the unbounded family and refutes the original conjecture using $k=4$. The theorem `infinitely_many_exceptions` rules out every finite list of representatives up to translation. Axiom guards cover all three conclusions.

OpenAI Codex searched periodic words with balanced letter indicators, found the divisibility obstruction, derived the infinite family, and wrote the proof.

# Fair words have a monic counting polynomial

For each length $n\ge 1$, the number of fair words on $k$ letters is a monic integer polynomial in $k$ of degree $d=\lceil n/2\rceil$. This proves Conjecture 34 in Anton Černý’s *On Fair Words*, Journal of Automata, Languages and Combinatorics 14 (2009), 163–174. [Original paper](https://doi.org/10.25596/JALC-2009-163)

A word is fair if, for any two distinct letters $a,b$, it contains as many scattered pairs $ab$ as $ba$. The conjecture predicts that its counting function has the form

$$F(k,n)=k\bigl(k^{d-1}+p_n(k)\bigr),$$

where $p_n$ has integer coefficients, vanishes at 1, and is either zero or has degree at most $d-2$. For example, Černý found $F(k,7)=k^4+2k(k-1)$. The first term counts palindromes. The other term counts the two ways, up to renaming letters, to form a fair word of length seven that is not a palindrome.

## Proof

Suppose that each letter occurs at most twice in a fair word. If its first letter $a$ and last letter $b$ differ, delete every other letter. The remaining word is one of $ab$, $aab$, $abb$, $aabb$, or $abab$. Each contains more $ab$ pairs than $ba$ pairs. The endpoints therefore agree. Removing them preserves fairness, since each occurrence of another letter loses one pair in each direction. Repeating this argument proves that the word is a palindrome.

Write $c_a$ for the positive multiplicities of the letters in a fair word. For distinct letters $a,b$, the product $c_ac_b$ is twice the number of $ab$ pairs. Thus at most one multiplicity is odd, and $\sum_a\lceil c_a/2\rceil=d$. A fair word that is not a palindrome has some $c_a\ge3$, so it uses strictly fewer than $d$ distinct letters.

A palindrome is determined by its first $d$ positions, giving $k^d$ possibilities. Group the other fair words by the partition of positions into equal letters. A partition with $r$ classes has exactly $k(k-1)\cdots(k-r+1)$ labelings on the alphabet. Each such partition has $2\le r<d$. Summing these products proves the formula, since each product has a factor $k$ and the remaining factor vanishes at 1.

Černý established the parity restriction and the upper bound of $d$ distinct letters. The proof above identifies what happens at that bound. A search of later work on fair words, precedence matrices, and fair dice found no earlier proof of Conjecture 34.

## Verification

From the repository root, run the following commands.

```sh
lake exe cache get
lake build conjectures.CernyFairWords.Solution
lake env leanchecker conjectures.CernyFairWords.Solution
```

The statement counts actual words and requires one integral polynomial for all positive alphabet sizes. The proof checks the transitive axioms of `CernyFairWords.resolution`. OpenAI Codex developed the argument and Lean formalization.

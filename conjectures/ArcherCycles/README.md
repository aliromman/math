# Proof of Archer et al.’s conjecture on cycles avoiding 3412 in one-line form and 213 in cycle form

Let $a_n$ count the permutations of $1,\ldots,n$ that consist of a single cycle, avoid 3412 in one-line notation, and avoid 213 when the cycle is written starting with 1. Their first seven counts are $1,1,2,5,13,36,104$. Their generating function is

$$
F(x)=\sum_{n\ge2}a_n x^{n-1}
=\frac{2x}{1-2x+\sqrt{1-4x+4x^3}}.
$$

Archer, Borsh, Bridges, Graves and Jeske conjectured this radical and associated it with OEIS A087626. They did not specify the index shift. With the usual exponent $n$, the full series is $\sum_{n\ge1}a_nx^n=x(1+F(x))$. [Original conjecture, §7, p. 91](https://ajc.maths.uq.edu.au/pdf/94/ajc_v94_p050.pdf#page=42) · [OEIS A087626](https://oeis.org/A087626)

## Proof

Write a nonsingleton cycle as $(1,L,2,R)$. Every label of $L$ exceeds every label of $R$. Otherwise some $u\in L$ and $v\in R$ give the pattern $u,2,v$ of type 213. Thus the cut at 2 gives two uniquely determined smaller cycles $Q=(1,L)$ and $P=(1,R)$, after relabeling each in increasing order. Conversely, any two cycles that avoid 213 in this notation can be joined this way. The empty blocks give singleton cycles. This separation at 2 also appears in earlier work. [Pan, Fact 2.1](https://arxiv.org/pdf/2505.02045)

One-line notation lists the successor of each label in its cycle. After the join, the successor list consists of the first entry of $Q$, all entries of $P$, and the remaining entries of $Q$, with labels changed as follows. If $P$ has $p$ labels, its values become $1,3,\ldots,p+1$. The values of $Q$ become $2,p+2,\ldots$.

These two orders leave just one way for a 3412 pattern to cross the cut. Its first three values come from $P$ and have the form $u,v,1$ with $u<v$. Its last value is the 2 from $Q$, which comes after $P$ precisely when $Q$ has at least two labels. For example, the cycle $(1,5,2,3,4)$ has successor list $5,3,4,1,2$. The last four entries exhibit the crossing.

Let $B(x)$ count the admissible cycles whose one-line entries before 1 decrease. Give a cycle of size $n$ weight $x^{n-1}$, so the singleton contributes 1 to $B$. If $Q$ is a singleton, any admissible $P$ gives an admissible join. If $Q$ is larger, $P$ must belong to $B$. Hence

$$
F=x(1+F+FB).
$$

For the join itself to belong to $B$, a singleton $Q$ requires a singleton $P$. Otherwise the initial 2 and the first value from $P$ form an ascent before 1. For a larger $Q$, its first value exceeds all values from $P$, so membership in $B$ again requires precisely that $P$ belongs to $B$. Including the singleton gives $B=1+x(1+FB)$.

Subtract the two equations to get $B=1+(1-x)F$. Substitution gives

$$
F=x+2xF+x(1-x)F^2.
$$

The solution with constant term zero is the displayed radical.

## Prior work and verification

Pan proved the other two conjectures in the same paragraph of the original paper. Pan's Theorem 3.8 gives Pell numbers when the one-line permutation must also avoid 4321. A search for the single forbidden pattern together with the cycle condition and A087626 found no earlier proof of the displayed formula. [Pan's paper](https://arxiv.org/abs/2505.02045)

The formal statement starts from all permutations of the cycle suffix. It reads the successors directly from the cycle. The proof checks the split in both directions, counts its disjoint products, and solves the resulting formal power series equations over the rationals. The theorem `ArcherCycles.ordinary_series` records the index shift.

```sh
# Run at the merge commit for PR #46.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

The axiom check for `ArcherCycles.resolved` permits `propext`, `Classical.choice`, and `Quot.sound`. OpenAI Codex derived the proof and wrote the Lean formalization.

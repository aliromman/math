# Disproof of Bajnok’s Conjecture 7 on extremizers for restricted sumsets in finite abelian groups

The eight nonzero squares modulo 17 form the set

```math
Q=\{1,2,4,8,9,13,15,16\}.
```

Sums of three distinct elements of $Q$ attain **every nonzero residue and omit zero**. Their number is $16=3(8-3)+1$, the minimum permitted by the Dias da Silva–Hamidoune theorem. Yet $Q$ is not an arithmetic progression. In fact, precisely two families of eight-element subsets of $\mathbb F_{17}$ have 16 distinct triple sums. They are the invertible affine images of an eight-term interval and of $Q$. The families contain 136 and 34 sets, respectively.

Béla Bajnok conjectured that for an $m$-subset of a finite abelian group whose least prime divisor of the order exceeds $h(m-h)+1$, equality in the restricted $h$-sum bound characterizes arithmetic progressions, with one parallelogram exception at $(h,m)=(2,4)$. The statement assumes $2\le h\le m-2$. Both numerical hypotheses hold here. [Bajnok, Conjecture 7, p. 6](https://arxiv.org/pdf/1512.03038#page=6)

## Why the squares work

Multiplying a triple of squares by the inverse of one entry gives a triple containing 1. If its sum were zero, its other entries would sum to 16 modulo 17. The only unordered pairs from $Q$ with that sum are $(1,15)$ and $(8,8)$. Each repeats an entry of the resulting triple.

The sums $1+2+15\equiv1$ and $1+4+15\equiv3$ represent a square and a nonsquare. Multiplication by the eight nonzero squares gives all 16 nonzero residues.

If $Q$ were a progression with step $d\ne0$, at least seven elements of $Q$ would remain in $Q$ after adding $d$. For $d=1$ there are three such elements, and for $d=3$ there are four. Multiplication by a nonzero square sends these two steps to all possible nonzero steps.

A smaller witness over $\mathbb F_{11}$ is $`\{0,1,3,4,5,9\}`$. It has ten distinct triple sums and is not an arithmetic progression. The correspondence with Bajnok's inverse problem and the classification over $\mathbb F_{17}$ are the contributions here.

## Classification over the field of order 17

A set with 16 triple sums has a unique missing residue $y$. Translating the set by $-y/3$ makes the missing residue zero. For that normalized problem, the allowed eight-element sets are precisely the nonzero dilations of $Q$ and of $`\{5,6,7,8,9,10,11,12\}`$.

Lean checks this finite classification by building the set one residue at a time. After choosing $x$, it discards any remaining $y$ for which $-x-y$ is a previously chosen point and all three residues are distinct. A branch stops when the number of remaining candidates is too small. The proof shows that this procedure keeps every solution, then checks its finite output in the kernel. Translation gives the classification above.

## Prior work

Xiao and Li listed the zero-sum triples of nonzero squares modulo 17 when repetitions are allowed. In their Example 2.5 and Corollary 3.9 every such triple has a repeated entry. Zhang and coauthors also list the set over $\mathbb F_{11}$ and its restricted triple sumset in a partition problem. A search by conjecture number, the equality, and the two sets found no earlier refutation of this inverse statement or classification of the eight-element extremizers. [Xiao and Li (2021)](https://doi.org/10.1515/math-2021-0032) · [Zhang et al., Table 1](https://arxiv.org/html/2606.13764v1#S3.T1)

Cavalcante's Theorem 1.1 addresses Bajnok's adjacent Conjecture 8. It assumes $m\le p<h(m-h)+1$ and classifies equality at $p$. Here $p=17>16$, and equality holds at 16. [Cavalcante, Theorem 1.1, p. 2](https://zenodo.org/records/21724408)

## Verification

From the repository root, run the following commands.

```sh
# Run at the merge commit for PR #28.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

`Statement.lean` gives the original conjecture for all finite abelian groups. `Solution.lean` proves its negation, classifies the extremizers at $(p,m,h)=(17,8,3)$ and checks their orbit sizes. The axiom guards on the disproof and classification permit propositional extensionality, classical choice and quotient soundness. OpenAI Codex found the connection, derived the classification and wrote the Lean proofs.

Béla Bajnok, “Open Problems About Sumsets in Finite Abelian Groups: Minimum Sizes and Critical Numbers,” in Combinatorial and Additive Number Theory II (2017), 9–23, DOI 10.1007/978-3-319-68032-3_2. The author’s version arXiv:1512.03038v2 gives Conjecture 7 on p. 6. [Publication](https://arxiv.org/pdf/1512.03038v2#page=6)

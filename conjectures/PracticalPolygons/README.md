# Every positive integer is a practical number plus two polygonal numbers

For each $s\in\{4,5,6,7,8,10\}$, every positive integer has a representation

$$n=p+P_s(x)+P_s(y),\qquad P_s(x)=(s-2)\binom{x}{2}+x,$$

where $x,y\ge0$ and $p$ is practical. This means every integer from $1$ through $p$ is a sum of distinct positive divisors of $p$. For example, $43=6+10+27$ uses two decagonal numbers.

This proves Conjecture 14 of Sai Teja Somu and Duc Van Khanh Tran. Their Theorem 2 proves eventual representation for every order $s>3$. They also tested the six conjectured orders below $10^8$. Their counterexamples at the other orders, together with this proof, classify every order $s>3$. Searches by title, authors, conjecture number, and the corresponding OEIS sequences found their paper and computations. We found no earlier proof covering every positive integer for these six orders. [Original paper, §§4–5](https://cs.uwaterloo.ca/journals/JIS/VOL27/Somu/somu5.pdf)

## Proof

Choose a modulus $M$ whose small positive multiples are practical. If two polygonal numbers have sum $z<n$ with $z\equiv n\pmod M$, then $n-z=Mt$. For $M=6d5^a$, $a\ge1$, and $d\in\{1,7,11,17\}$, every such multiple with $5t\le12M$ is practical. This follows by forming divisor sums in successive powers of five. To represent an integer $tb+r$ using divisors of $Mt$, the divisors used for $r<t$ are smaller than every divisor used for the scaled sum $tb$.

For $a\ge4$, put $L=M/25$. Write $Q(u)=P_s(u)$ for even $s$ and $Q(u)=P_s(2u)$ for odd $s$, and let $A$ be its leading coefficient. For each target modulo 25, a finite table supplies a root pair whose derivatives can correct every residue modulo 25 with nonnegative increments $h,l$ satisfying $A((h+1)^2+(l+1)^2)\le520$. The Chinese remainder theorem and successive lifts by five give $0\le x,y<L$ with the required sum modulo $L$ and the same derivative residues. Replacing $x,y$ by $x+Lh,y+Ll$ corrects the sum modulo $M$, since $25\mid L$. Its new value is at most $520L^2<5M^2/6$.

This covers $5M^2/6\le n\le12M^2/5$. The successive scale factors $5,7,11,17,25$ give overlapping intervals. A finite check covers $1\le n\le400{,}000$ directly. Residue checks at $M=750,3750,18750$ extend this through $843{,}750{,}000$, where the infinite family applies. Lean checks each finite calculation and proves that every set bit gives actual summands.

## Verification

Run these commands from the repository root with the pinned Lean and Mathlib versions.

```sh
lake exe cache get
lake build conjectures.PracticalPolygons.Solution
lake env leanchecker conjectures.PracticalPolygons.Solution
```

OpenAI Codex developed the congruence argument, finite certificates, and Lean formalization. Somu and Tran posed the conjecture and established the preceding eventual theorem. [Statement](Statement.lean) · [Proof](Solution.lean)

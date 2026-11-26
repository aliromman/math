# A cyclotomic factor can occur with unequal residue counts

The cyclotomic factor predicted by Chidambaram, Mináč, Nguyen and Tân can occur even when the exponents have unequal residue counts. An odd-index example is

$$
n=3\cdot37\cdot67\cdot151=1{,}122{,}987,\qquad d=63,
$$

Here $\Phi_{63}$ divides $F_n$, although classes $1$ and $4$ contain $16{,}972$ and $16{,}971$ exponents, respectively.

## The conjecture

For a positive squarefree integer $n$, let $F_n(x)$ be the sum of $x^a$ over $0\le a<n$ coprime to $n$. The conjecture counts representatives from $1$ through $n$. These ranges give the same exponents for $n>1$. For $d>1$ with $d\nmid n$, Chidambaram, Mináč, Nguyen and Tân conjectured that $\Phi_d$ divides $F_n$ exactly when these exponents are equally frequent among the residue classes coprime to $\gcd(d,n)$. Their Proposition 2.9 proves that equal frequencies imply divisibility. The examples disprove the converse. The paper also uses the conjecture as a hypothesis in its study of products of two odd primes. [Conjecture 2.11, *Journal of Experimental Mathematics* 1 (2025), 51–93](https://arxiv.org/abs/2307.14896)

## The odd example

Let $c(r)$ count the exponents in class $r$ modulo $63$. The entire frequency vector has period $21$. The counts depend on $r\bmod21$ as follows.

| Residue modulo 21 | Count |
|---|---:|
| A multiple of 3 | 0 |
| $1,2,5,7,10,11$ | 16,972 |
| Any other residue | 16,971 |

For a primitive $63$rd root $z$, the factor $z^{21}$ is a nontrivial cube root of unity. Hence

$$
F_n(z)=\left(1+z^{21}+z^{42}\right)\sum_{r=0}^{20}c(r)z^r=0.
$$

The cancellation comes from equal counts within each triple $r,r+21,r+42$. The counts can differ between triples.

The table can be checked by inclusion–exclusion with sixteen divisors of $n$. For each divisor $m$, count the integers $1\le j\le n/m$ with $mj\equiv r\pmod{63}$ and use the sign $(-1)^{\omega(m)}$. Each block of 63 consecutive indices gives the same count. The formal proof implements this sieve and verifies the period and the two unequal counts by integer arithmetic.

## Prior work and verification

The authors already give the full factorization of $F_{2p}$ in Example 2.5. In particular, $F_6=x+x^5=x\Phi_8$ occupies only two of the four odd classes modulo eight. The odd example gives an independent obstruction. A 2026 follow-up studies sufficient conditions for cyclotomic factors of rational necklace functions, including the Fekete polynomials. Searches using the conjecture number, the authors, equidistribution, counterexamples, and the two indices found no prior disproof of Conjecture 2.11. OpenAI Codex found the odd example by a character calculation and wrote the proof and Lean formalization. [Original paper](https://arxiv.org/abs/2307.14896) · [Follow-up](https://arxiv.org/abs/2606.02324)

Run these commands from the repository root with the pinned toolchain.

```sh
lake exe cache get
lake build conjectures.FeketeEquidistribution.Solution
lake env leanchecker conjectures.FeketeEquidistribution.Solution
```

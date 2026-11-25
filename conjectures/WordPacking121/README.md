# Two letters suffice to pack the pattern $12\!-\!1$

In a word of length $n$ on any ordered alphabet with at least two letters, the largest possible number of occurrences of $12\!-\!1$ is

$$
\left\lfloor\frac{n(n-1)}6\right\rfloor.
$$

An occurrence consists of positions $i,i+1,j$ with $j>i+1$ and $w_i=w_j<w_{i+1}$. For example, the word `121211` has five occurrences. Three start at the first position and two at the third.

Burstein, Hästö and Mansour gave the optimal construction on two letters. They conjectured that the packing density is $1/3$ when the alphabet can grow. The formula above proves that extra letters cannot improve the count even at a fixed length. Dividing by $\binom{n-1}{2}$, the number of allowed position triples, gives the conjectured density in both orders of the limits in word length and alphabet size. [Original paper, §3.2, immediately after Proposition 3.7](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_9/PDF/v9i2r20.pdf)

## Proof

Split a word at every adjacent pair that fails to increase. Each resulting run is strictly increasing. Let $d$ count the runs of length at least two, let $s$ count the singleton runs, and let $e$ count the letters beyond the first two in the long runs. Thus $n=2d+s+e$.

Each occurrence starts in a long run and ends in a later run. A later singleton can complete at most one occurrence from each earlier long run. For two long runs, the earlier run of length $a$ can start at most $a-1$ occurrences ending in the later run, since the later run has distinct letters. Sum one per pair of long runs and charge the remaining $a-2$ to the extra letters of the earlier run. Each extra letter is charged at most $d$ times. The total count is at most

$$
\binom d2+d(s+e)=\binom d2+d(n-2d)=F_n(d).
$$

The word $(12)^d1^{n-2d}$ attains this bound. To maximize it, observe that

$$
n(n-1)-6F_n(d)=(n-3d)(n-3d-1).
$$

The right side is a product of consecutive integers and is nonnegative. For $d=\lfloor n/3\rfloor$ it equals $0$ or $2$, which proves the formula.

## Prior work and verification

The authors' early draft states the density and assumes the binary extremal form. Their journal article explicitly leaves the upper bound for general alphabets open. Searches for the pattern and its reversal and complement found no later proof of this word bound. Barton treats classical subsequence patterns. Freij and Mansour give a different density for integer compositions, where the sum of the letters determines size. [Early draft, Proposition 4.7](https://citeseerx.ist.psu.edu/document?doi=5f392d5108197f3b3fe013bb083985c9c350e79b&repid=rep1&type=pdf) · [Journal article](https://doi.org/10.37236/1692) · [Barton](https://doi.org/10.37236/1833) · [Freij and Mansour, Proposition 5.5](https://intlpress.com/api/bgcloud-front/resource/pdf/volume/1805864981797220354-1805864981797220354-431550d94a03c68a3edb5247d2ca1027.pdf)

`Statement.lean` defines the occurrences, the finite maximum, and both iterated limits. `Proof.lean` verifies the finite formula and the conjecture. From the repository root, run

```sh
lake exe cache get
lake build conjectures.WordPacking121.Proof
lake env leanchecker conjectures.WordPacking121.Proof
```

OpenAI Codex derived the run bound and wrote the Lean proof. Burstein, Hästö and Mansour supplied the pattern, the conjectured density, and the binary construction.

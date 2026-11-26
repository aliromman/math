# The longest interval in a random sumset starts at half the hole count

When exactly $k$ sums are missing, the limiting mean left endpoint of the longest interval of consecutive sums is $k/2+O(1)$. Every way of breaking ties has the same limit. This gives the slope in Conjecture 8.2.

Choose a uniformly random subset $A$ of $\{0,\ldots,n-1\}$. Its sumset consists of all $a+b$ with $a,b\in A$, including $a=b$. Let $K$ count the missing integers in $[0,2n-2]$. Choose any longest interval contained in $A+A$, and call its left endpoint $W$. The authors conjectured that $e(k)=\lim_{n\to\infty}\mathbb E[W\mid K=k]$ is asymptotically linear as $k\to\infty$. Ties can change the finite mean. For each $k$ the limit exists, is independent of those choices, and differs from $k/2$ by a bounded amount. The limit in $n$ comes first. For fixed $k$, the conditioning event has positive probability for all sufficiently large $n$.

Lazarev, Miller and O’Bryant, *Distribution of missing sums in sumsets*, §8, p. 34 of the accepted manuscript. [Authors’ manuscript](https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/DistrMissingSums95.pdf) · [Journal article](https://doi.org/10.1080/10586458.2013.743304)

## Proof

Write $u$ and $v$ for the numbers of unused sites at the left and right ends of $A$. Remove those sites and call the remaining set the core. Both endpoints of the core are occupied. If the core misses $j$ sums, then $k=2a+j$, where $a=u+v$. For each of the $a+1$ allocations of the margins, the probability of a given core event is its original probability times $2^{-a}$. The first possible sum is $2u$. Its average over the allocations is $a$.

Here is the estimate that controls the holes inside the core. In an infinite sequence of fair bits, let $p(m,t)$ be the probability that the first bit is occupied, that there are exactly $m$ missing sums, and that the last one is $t-1$. Use $t=0$ if there are no holes. A missing sum $x$ requires that no pair of distinct nonnegative integers summing to $x$ has both sites occupied. The disjoint pairs give a geometric tail in $x$. Thus fixed windows at opposite ends of a long core have independent limits. If $D_j$ is the limiting probability that the endpoints are occupied and the core has $j$ holes, it equals the convolution of the two copies of $p$, summed over their last-hole locations.

The proof in Lean gives the following bound uniformly even for finite prefixes. For any $m,t$, the probability that a length-$t$ prefix starts occupied, misses $m$ sums below $t$, and ends at a missing sum is at most

$$
C\,2^{-m/2-t/256}.
$$

To see the two ingredients, first omit the condition at zero. Partition the possible hole locations into short bands of length about $t/q$, for large fixed $q$. If $m$ exceeds a band length, pigeonholing the holes above $m-t/q$ gives a band ending at $s$ with many forbidden sums $S$. In $[0,s)$, join sites whose sum lies in $S$. Keep choosing occupied sites that forbid more than $t/q^3$ new neighbors. At most $q^3$ choices suffice. The sites still available have at most $t/q^3$ new neighbors each. Counting the reflected pairs for each member of $S$ leaves a set of at most $t-m/2+O(t/q+q^2)$ available sites in the full prefix. The band, its subset $S$, and the chosen sites have at most $2^{t/q+O(q^2)}t^{O(q^3)}$ descriptions. When $m$ is smaller than one band the same size bound allows the whole prefix.

Inside each such set $C'$, the missing sum $t-1$ forbids both endpoints of at least $|C'|-(t+1)/2$ disjoint pairs. Each of these pairs has three possible states. Summing the resulting counts gives an upper bound $C_\epsilon 2^{-m/2-(t-m)/8+\epsilon t}$ for any $\epsilon>0$. Now restore the occupied site at zero. Each occupied site gives a present sum, so at most $t-m$ sites are occupied. Weighting subsets by $8^{-|A|}$ gives the second bound $8^{t-m}(9/16)^t$. Use the first bound for $t-m\ge t/16$ and the second below that threshold.

In particular $\sum_j 2^{j/2}(j+1)D_j$ is finite. Both $D_0$ and $D_1$ are positive. Force a long initial block to be full, or full except at site 1. The disjoint-pair bound on later holes, together with monotonicity under adding sites, leaves positive probability in either case. Apply this at both ends.

Let $t$ and $s$ be one plus the distances of the last holes from each end of the core sum interval, with zero for an empty fringe. For a core of length $N$, the middle interval starts at $t$ and ends just before $2N-1-s$. If $3(t+s)<2N-1$, it is the unique longest run. In all cases a longest run starts at most $3(t+s)$ sites from zero. The finite-window bound therefore permits passage to the limit in this expectation, including every tie rule. Write $H_j$ for the same convolution that defines $D_j$, with each summand multiplied by $t$. Then $\sum_j2^{j/2}H_j$ is finite.

Set $w_a=(a+1)2^{-a}$. The sumset shifts by $2u$ when its core shifts by $u$, so averaging over the margins gives

$$
e(k)=\frac{\sum_{2a+j=k} w_a(aD_j+H_j)}{\sum_{2a+j=k} w_aD_j}.
$$

Divide numerator and denominator by $(\lfloor k/2\rfloor+1)2^{-k/2}$. Each rescaled weight is at most $2^{j/2}$. The term of matching parity with $j=0$ or $1$ bounds the denominator below by $\min(D_0,D_1)>0$. Substitute $a=k/2-j/2$. The weighted sums of $jD_j$ and $H_j$ bound the error uniformly in $k$.

## Earlier work

Green and Morris obtained the critical exponential rate for the one-sided number of holes. Mazur’s Proposition 6.1 gives faster decay when zero is occupied. These earlier results explain why a positive margin consumes most of a large hole count. Our argument gives a finite-window estimate and uses it to compute the conditional location in the authors’ two-sided model. A search for the conjecture, its authors, and later work on missing sums found no earlier proof of this location formula. [Green and Morris](https://ora.ox.ac.uk/objects/uuid%3Ab86abc16-fe93-43b0-9c20-9593ab538229) · [Mazur](https://doi.org/10.4064/aa171-3-2)

## Verification

From a clean checkout of this draft, run

```sh
lake exe cache get
lake build conjectures.MissingSumFringes.Longest.Solution
lake env leanchecker conjectures.MissingSumFringes.Longest.Solution
```

The statement and solution are separate modules. The toolchain and Mathlib revision are pinned. An independent AI reviewer checked the source, the limiting argument, and the formal statements, enumerated all nonempty subsets through $n=21$, and replayed the exported theorems in the Nanoda kernel. The guarded axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

OpenAI Codex developed the proof and formalization for this repository. Lazarev, Miller and O’Bryant posed the conjecture.

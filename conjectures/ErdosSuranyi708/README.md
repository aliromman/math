# The sharp asymptotic bound for Erdős–Surányi interval products

Let $A$ consist of $n$ distinct integers at least 2, and let $M=\max A$. From **any** run of $M$ consecutive integers, one can choose at most $(2+o(1))n$ numbers whose product is divisible by the product of $A$. The error is uniform in $A$, $M$, and the starting point of the run.

Erdős and Surányi constructed examples requiring $(2-o(1))n$ choices. Together the bounds determine the limiting worst-case ratio, $\lim_{n\to\infty}g(n)/n=2$. The new theorem supplies the upper bound. The stronger question $g(n)\le 2n$ for **every** $n$ remains open. [1959 construction, §9](https://users.renyi.hu/~p_erdos/1959-07.pdf) · [Erdős’s 1992 question, pp. 34–35](https://hrj.episciences.org/125/pdf) · [Problem 708](https://www.erdosproblems.com/708)

## A three-number example

Erdős and Surányi used the inputs $77=7\cdot11$, $91=7\cdot13$, and $143=11\cdot13$ with the run from 5935 through 6077. Its only multiple of any pair of the three primes is $6006=6\cdot7\cdot11\cdot13$, and it contains no multiple of $13^2$. Three selections cannot supply two copies of each prime. Four suffice, for example $5950,5951,5954,6006$. The asymptotic theorem determines how far this need for extra positions can grow. [Original example, §1](https://users.renyi.hu/~p_erdos/1959-07.pdf)

## Why the factor two appears

Divisibility asks how many copies of each prime the chosen numbers contain. Each selected number can pay for several primes at once. The hard case is a shifted interval in which these useful combinations have moved to different numbers.

Give each prime a price. This makes the value of any integer the sum of the prices of its prime factors, counted with multiplicity. The proof compares the total price demanded by the inputs with the value available above one unit per interval element. Its new step is to retain each prime label independently with probability $s<1/2$. For each input, a lower sieve preserves the contribution of every crossing of the one-unit threshold except possibly the one involving its **two largest prime labels**. The spare credit in the random selection pays for that last pair. The cost per input is $1/s$, which tends to two. A uniform estimate for counts of divisors allows the comparison to survive every translation of the interval. [Mathematical proof](Argument.md)

## The lower bound of Erdős and Surányi

Erdős and Surányi used products of pairs of nearby primes. In §9 they take every unordered pair, including equal primes. With $l$ primes there are $l(l+1)/2$ inputs. Their interval needs at least $l(l-1)+1$ selections. This gives the historical asymptotic lower bound. [Primary paper, §9, p. 44](https://users.renyi.hu/~p_erdos/1959-07.pdf#page=6)

The Lean proof uses two disjoint sets of nearby primes so that it can prescribe the input size $n$ exactly. Put $r=\lfloor\sqrt n\rfloor+1$. Choose two sets of $r$ primes in $[a,9a/8]$. The $r^2$ cross products are distinct. Choose any $n$ of them as the inputs. Each input contributes two prime factors, counted with multiplicity. The existence of the prime sets follows from Chebyshev’s lower bound for the prime-counting function and the pigeonhole principle. [Prime sets](HistoricalPrimes.lean) · [Choice of the inputs](HistoricalLower.lean)

Write $R=a^2-2a$. The Chinese remainder theorem gives a center $c$ such that $c\equiv p+p^2\pmod {p^3}$ for every chosen prime $p$. In the interval $(c-R,c-R+\max A]$, only $c$ can be divisible by two distinct chosen primes. For each $p$, only $c-p$ can be divisible by $p^2$, and its exponent there is exactly two. Indeed, $\max A\le2R$, and $R+p<p^2$ and $R<pq$ throughout the prime range. Consequently, the chosen primes contribute at most $|B|+4r$ factors to the product of any selection $B$. A selection that covers the input must supply all $2n$ factors. For every sufficiently large $n$, some interval therefore needs more than $(2-\varepsilon)n$ selections. [Centered interval and factor counts](HistoricalWindow.lean) · [Historical lower bound](HistoricalLower.lean)

The formal function $g(n)$ is the least number that suffices for all sets of $n$ inputs and all signed integer intervals of the required length. Its defining set of budgets is nonempty at every $n$. The theorem `tendsto_g_div` combines the two bounds and proves $g(n)/n\to 2$. [Least sufficient budget and limit](Limit.lean)

## Statement and verification

For every $\varepsilon>0$, the formal theorem gives a threshold $N(\varepsilon)$ such that every admissible set of size $n\ge N(\varepsilon)$ and every run $I$ admit a subset $B$ with

$$
\lvert B\rvert\le(2+\varepsilon)n,\qquad
\prod_{a\in A}a\ \bigm|\ \prod_{b\in B}b.
$$

Here $g(n)$ is the least **upper bound** on the number of selections. Some listings say to choose exactly $g(n)$ elements. For $A=\{2,\ldots,n+1\}$ there are only $n+1$ available positions, whereas other inputs require nearly $2n$. The historical problem asks how many selections suffice. The formalization includes Erdős’s strict inequality for nonnegative shifts, arbitrary signed shifts, and the extension allowing 1 among the inputs. [Statement](Statement.lean) · [Upper-bound theorems](Proof.lean) · [Limit theorem](Limit.lean) · [Source comparison](https://erdosproblems.ai/problems/708)

With this branch checked out, run the repository verifier from the root. It builds the affected modules, replays them in the kernel, and checks their transitive axioms against the contract. The pins are Lean 4.36.0 and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The three upper-bound theorems, the finite and asymptotic lower bounds, the characterization of the least budget, and the limit theorem each use `propext`, `Classical.choice`, and `Quot.sound`. [Axiom contract](axioms)

```sh
python3 scripts/verify.py --base 7f6a005afe96173301f80cf6b50539aa1502550c --fetch-cache
```

## Prior work and attribution

- **Tibor Gallai** posed the selection question in 1948, according to the first page of **Erdős and Surányi**’s 1959 paper. Their paper gave the lower bound. Erdős distinguished the sharp asymptotic question from the stronger pointwise question in 1992. [Original paper](https://users.renyi.hu/~p_erdos/1959-07.pdf) · [1992 restatement](https://hrj.episciences.org/125/pdf)
- **Haoyu Chen** proved the cubic-height $2n$ bound and gave a formal $12n$ bound for every $n$. Our finite linear separation and rounding lemmas adapt Chen’s CC0 Lean code. The primewise transport and cubic reduction also use his arguments. [Paper](https://doi.org/10.5281/zenodo.22660853) · [Exact source revision](https://github.com/chy4pro/erdos-708-explicit-upper-bounds/tree/dc150fd723184cc4e6f367aac6e7a8c9c7890f34)
- **Ziming Wang** combined a transfer theorem with Chen’s written atom inequality to obtain $10n$ and the asymptotic coefficient $56501/6400$. Wang also proved $2n$ for $M\ge16n^2$. **C. Bergström** subsequently used whole-cofactor peeling, rank rounding, and inequalities for weighted prime valuations to obtain $(56501/6400+o(1))n$. A second preprint studied telescoping and restricted prime weights. These are precursors of the reduction. The new argument is the thinned first-crossing sieve and its uniform error estimate for arbitrary real prime weights. [Wang’s manuscript](https://github.com/science-prince/erdos-708-interval-divisor-covers/blob/main/papers/main-paper/main.tex) · [Bergström’s linear bound](https://doi.org/10.5281/zenodo.24342718) · [Bergström’s telescoping estimates](https://doi.org/10.5281/zenodo.24366998)
- The prior-art search covered the three requested repositories, their linked problem and claim records, recent preprints, and the papers above. We found no earlier proof of the uniform asymptotic upper bound. OpenAI Codex developed the argument and Lean formalization for this repository. Other AI agents challenged the mathematical argument and checked its translation against the sources. [Erdős Problems catalogue](https://github.com/teorth/erdosproblems) · [Plasma research record](https://github.com/plasma-ai/erdos/tree/main/wiki/problems/integer_sequences/E0708) · [Formal Conjectures statement proposal](https://github.com/google-deepmind/formal-conjectures/pull/4388)

# Proof of the asymptotic interval-product bound

Write $[M]=\{1,\ldots,M\}$ and $I=\{x+1,\ldots,x+M\}$, first with $x\ge0$. For a prime $p$, let $v_p(a)$ be its exponent in $a$. Write $h(t)=(t-1)_+$ and $u_+=\max(u,0)$.

## 1. The selection problem reduces to an interval estimate

Suppose $A\subseteq[M]$ has $n$ elements. Delete each input that has a prime divisor greater than $5n$ and call the remaining set $A_0$. Put $m=\lvert A_0\rvert$. For a finite set $P$ of primes at most $\min(M,5n)$, put $W(b)=\sum_{p\in P}w_pv_p(b)$. The estimate we need is

$$
\sum_{a\in A_0} W(a)-\sum_{b\in I}h(W(b))\le 2m+o(n).
\tag{1}
$$

We prove (1) for every subset $A_0\subseteq[M]$ of size $m\le n$, every $0\le w_p\le1$, and $n\le M\le(2n)^3$. The error is uniform in all these data and in $x$.

To see how it gives the result, take all prime divisors of the smooth inputs as $P$. Give each position $b\in I$ a fractional selection $0\le y_b\le1$. Impose the constraints $\sum_b y_bv_p(b)\ge\sum_{a\in A_0}v_p(a)$. The all-ones vector is feasible, since each prime power has at least as many multiples in $I$ as in $[M]$. The linear-program dual for the minimum of $\sum_b y_b$ is the supremum of the left side of (1) over nonnegative prices $w$. When one price exceeds 1, every target position divisible by that prime stays on the linear part of $h$ as the price decreases to 1. Total supply dominates demand in that row. Thus cutting the price to 1 can only increase the dual objective. With linear dependencies among fractional columns one can move to a solution of no greater cost with at most $\lvert P\rvert$ fractional positions. Rounding these up costs at most $\pi(5n)=o(n)$. [Separation and rounding](FiniteLP.lean) · [Boxed dual](Selection.lean)

Each deleted input $a$ supplies a prime $p>5n$ and a cofactor $a/p$. Assign the prime to the position $a+p\lfloor x/p\rfloor$. This lies in $I$. Equal primes get distinct positions because their inputs are distinct. Different primes can share a position, and these primes are coprime to the smooth input product. Each cofactor has at least $p>5n$ multiples in $I$, so it can use a fresh position. For all sufficiently large $n$, fewer than $5n$ positions are needed during these assignments. The combined count is at most $2m+o(n)+2(n-m)$.

When $M\ge(2n)^3$, use the same construction with cutoff $2n$. Each input with all prime factors at most $2n$ splits into two factors at most $M/(2n)$. If the input already satisfies that bound, use 1 as the other factor. Otherwise multiply its prime factors until the partial product first reaches $2n$. This factor is at most $(2n)^2\le M/(2n)$ and its complement is at most $M/(2n)$. Each factor has at least $2n$ available multiples. The same assignment and peeling give $2n$ positions. A signed interval containing 0 needs only that position. Reflect an entirely negative interval to obtain a positive one. [Large primes and large height](Reduction.lean) · [Integer intervals](Signed.lean)

## 2. Cap the prime scores

Put $z_p(b)=\min(1,w_pv_p(b))$ and $Z(b)=\sum_p z_p(b)$. The excess $W-Z=\sum_p(w_pv_p-1)_+$ satisfies $h(W)=W-Z+h(Z)$. Each excess is an increasing function of a single valuation. Its successive increments give a nonnegative combination of prime-power divisibility indicators. Counts of multiples in $I$ dominate their initial counts. It suffices to prove (1) with $Z$ in place of $W$. [Capping](Scores.lean)

Let $\mu=\sum_{p\in P}w_p/p$. For uniform $a\in[M]$, set $Y(a)=\sum_{p\mid a}w_p$ over these primes. Counting multiples of $p$ and of $pq$ gives $\mathbb EY\ge\mu-1$ and $\mathbb EY^2\le\mu^2+\mu$. The first inequality uses $\sum_p w_p\le M$. Consequently $\mathbb E(Y-\mu)^2\le3\mu$. If $\mu\ge20$, at least half the interval has $Z\ge Y\ge2$, by Chebyshev's inequality. Hence $\sum_{[M]}\min(2,Z)\ge M$. After deleting $m$ sites the remaining score is at least $M-2m$. The entire target has $\sum_I Z\ge\sum_{[M]}Z$ by the same prime-power count, and $\sum_I h(Z)\ge\sum_I Z-M$. This proves (1) with zero error in this case. Assume $\mu<20$ below. [Large prime mean](Dense.lean)

Choose $0<s<1/2$ and write $u=1-s$. Fix a cutoff $Y_0$ and a positive integer $K$. For each prime $p\le Y_0$, group consecutive positive valuations into buckets according to the integer part of $Kz_p$. Give a bucket the score at its smallest exponent. For $p>Y_0$, use the individual exponents. Only exponents through $\lfloor\log_p M\rfloor$ need be considered, and the final bucket extends to infinity. Scores decrease by at most $(Y_0+1)/K$ per source site. They can only decrease the target hinge. Write $Z$ also for the sum of the bucket scores. A dividing prime stays present even when its score is zero. [Buckets](Buckets.lean) · [Comparison at a site](Site.lean)

## 3. Thin the prime labels and expand the hinge

At a fixed integer, let $T$ be its set of present prime labels, with scores $0\le z_p\le1$. Independently retain each label with probability $s$, giving a subset $R$. For $U\subseteq T$ write $Z(U)=\sum_{r\in U}z_r$. Define

$$
f(T)=s^{-1}\mathbb E h(Z(R)).
$$

Jensen's inequality gives $(Z(T)-1/s)_+\le f(T)$. The chord from 0 to $Z(T)$ gives $f(T)\le h(Z(T))$. Let $\Delta_a h(t)=h(t+a)-h(t)$. Telescope once in increasing prime order to insert a retained $p$, then again to identify the earlier label $q<p$ that makes a nonzero increment. For each set $V$ of retained labels below $q$, the term is

$$
\alpha\,u^{\lvert T_{<q}\setminus V\rvert},\qquad
\alpha=s^{\lvert V\rvert+1}\Delta_{z_p}\Delta_{z_q}h(Z(V)).
$$

Indeed the first telescoping sum has increments $\mathbb E\Delta_{z_p}h(Z(R_{<p}))$. Its value at an empty predecessor set is zero because $z_p\le1$. The second telescoping sum gives the displayed coefficients. Convexity and the unit slope bound give $0\le\alpha\le s^{\lvert V\rvert+1}$, and $\alpha>0$ requires $Z(V)<1$. [Finite expansion](Crossing.lean)

Fix $p,q,V$ and the buckets on these labels. Multiply their lower prime powers to form $d$ and set $L=\lfloor M/d\rfloor$. An upper endpoint $b_r$ of a bucket with lower endpoint $a_r$ requires the quotient by $d$ to avoid $r^{b_r-a_r}$. Let $D$ be these forbidden prime powers. Their bases are distinct. The remaining primes $S=P_{<q}\setminus V$ give the factor $u^{\lvert T\cap S\rvert}$.

## 4. A lower sieve loses at most the last pair

Omit the term if $dq>M$. Otherwise approximate $u^{\lvert U\rvert}$ for $U=T\cap S$ by a divisor polynomial $B_L(U)$. Expand the product in decreasing prime order. A descending prefix $E$ of length $j$ has remainder

$$
(-s)^j {\bf1}_{E\subseteq U}\,
u^{\lvert\{r\in U:r<\min E\}\rvert}.
$$

At an expanded node record its constant term and append each smaller label as a child. These child remainders telescope to the original remainder minus the constant. At a nonempty even prefix stop and discard the entire remainder if $(\prod E)\min E>L$. All discarded remainders are nonnegative, so $B_L(U)\le u^{\lvert U\rvert}$. Each retained monomial has squarefree modulus $e=\prod E\le L$ and coefficient $(-s)^{\lvert E\rvert}$. An odd child fits because its even parent passed the stopping test. An oversized even child stops.

On a source with $\prod U\le L$, any active discarded prefix contains every member of $U$ larger than its smallest element. A missed larger prime would make $\prod U>L$. Such prefixes are nested, so at most the first is reached. Its ratio to the exact exponential is $(s/u)^{\lvert E\rvert}\le(s/u)^2$. Thus

$$
c_s u^{\lvert U\rvert}\le B_L(U)\le u^{\lvert U\rvert},
\qquad c_s=1-(s/u)^2>0.
$$

If another present prime $\ell>q$, distinct from $p$, divides the source input $a$, then for every active prefix $E$, $d(\prod E)q\le d(\prod E)\ell\le a\le M$. The whole term is exact. The only loss possible on a source comes from $p,q$ its two largest labels. [Lower sieve](Sieve.lean)

For that pair put $a=z_p$, $b=z_q$, and let $X$ be the random score below $q$. Its full contribution is $s\mathbb E\Delta_a\Delta_bh(X)$. Put $g(x)=(1-x)_+$. Since $h-g=x-1$,

$$
\Delta_a\Delta_b h(X)=\Delta_a\Delta_b g(X)\le g(X)+g(X+a+b).
$$

In $s^{-1}\mathbb E g(Z(R))$, conditional on $X$, the coefficients of these last two quantities are $u^2/s$ and $s$. Both are at least $s$. Thus the possible loss is at most $s^{-1}\mathbb E g(Z(R))=f(T)-Z(T)+1/s$. Together with source nonnegativity, this bounds the source approximation from below by $(Z(T)-1/s)_+$.

For $q>Y_0$ omit terms with $J=\lvert V\rvert>(\log L)^2$. On a source with $k$ active primes, the other $k-J-2$ primes outside the required set divide the quotient, so $k-J-2\le\log_2 L$. For sufficiently large $Y_0$, every omitted set has $J\ge 4k/5-O(1)$. The sum of its possible weights is exponentially small in $k$. For example, for fixed $p,q$,
$\sum_{\lvert V\rvert\ge j}s^{\lvert V\rvert}\le 4^{-j}(1+4s)^k\le4^{-j}3^k$, and $3^5<4^4$. There are at most $k^2$ ordered pairs, and $k>(\log Y_0)^2$ whenever a term is lost. The retained polynomial, summed over all terms, is denoted by $F$. For a function $\delta_s(Y_0)\to0$ we have

$$
F(b)\le h(Z(b))\quad(b\ge1),\qquad
0\le F(a),\quad Z(a)\le 1/s+F(a)+\delta_s(Y_0)\quad(a\in[M]).
$$

Omitting a whole term on a target remains valid even if its lower sieve is negative. Each retained estimate is below the corresponding nonnegative exact term. [Truncation](CrossingTrim.lean) · [Sum over the buckets](Terms.lean)

## 5. Translate one term

Write $\omega(e)$ for the number of distinct prime factors. For a retained set of buckets, count multiples of $d e$ in the interval whose quotient avoids $D$. The sieve coefficients in $e$ have absolute value at most $s^{\omega(e)}$. Every unconditioned count of multiples in the two intervals differs by at most 1. A full inclusion-exclusion on $D$ thus gives error at most $2^{\lvert D\rvert}$ for a fixed $e$. This suffices when $q\le Y_0$, since the number of possible sieve subsets is at most $2^{\lvert S\rvert}$ and $\lvert D\rvert+\lvert S\rvert\le Y_0+2$.

For the other terms, $\lvert D\rvert\le(\log L)^2+2$. Let $A=\log L$ in this paragraph and $t=\lceil\log_2 A\rceil$. For $e\le L/2^{100t^2}$ truncate inclusion-exclusion after consecutive orders at $r=16t$ and $r-1$. If $J'=\lvert D\rvert$, the error in the normalized count is bounded by a constant times

$$
2^{-r}(J'+1)^2+
\frac{(r+2)(J'+1)^r}{2^{100t^2}}
\ll A^{-3}.
$$

Here $\sum_{\lvert E\rvert=r}1/\prod E\le2^{-r}\prod_{v\in D}(1+2/v)\le2^{-r}(J'+1)^2$. The last bound follows by ordering the distinct integers $v\ge2$ and telescoping. The second term accounts for the unit errors in all retained counts of multiples. In the remaining $100t^2$ dyadic blocks use the trivial bound $O(L/e)$. The mean estimates below give $\sum_{e\le y}s^{\omega(e)}\ll_s y(\log y)^{s-1}$ and $\sum_{e\le y}s^{\omega(e)}/e\ll_s(\log y)^s$ for $y\ge2$. Each dyadic block contributes $O_s(L A^{s-1})$. Consequently, for every fixed small $\nu>0$, the absolute translation error of this term is

$$
O_{s,\nu}\bigl(\alpha L(\log L)^{s-1+\nu}\bigr).
\tag{2}
$$

All bounds are independent of the shift, even if it is much larger than $M$. [Interval counting](Discrepancy.lean)

For the relative error, use the multiplicative weight
$G(b)={\bf1}_{b\ {\rm avoids}\ D}\,u^{\lvert\{r\in S:r\mid b\}\rvert}$ and let $P_G(y)=\prod_{p\le y}(1+G(p)/p)$. The initial contribution of the term lies between $c_s\alpha\sum_{b\le L}G(b)$ and $\alpha\sum_{b\le L}G(b)$. The sums here and below start at 1. Uniformly when $\lvert V\rvert\le(\log L)^2$,

$$
\sum_{b\le L}G(b)\asymp_s \frac{L}{\log L}P_G(L),\qquad
P_G(L)\gg_s \frac{(\log L)^{1-s}}{1+\log(\lvert V\rvert+5)}.
\tag{3}
$$

For the upper mean, expanding the harmonic Euler product gives $\sum_{b\le L}G(b)/b\ll P_G(L)$. Prime powers beyond the first cost a convergent product since $G(p^j)\le G(p)\le1$. Insert $\log b=\sum_{d\mid b}\Lambda(d)$, where $\Lambda$ is the von Mangoldt function. The elementary Chebyshev bound $\sum_{j\le y}\Lambda(j)\ll y$ and $G(dj)\le G(d)$ give $\sum_{b\le L}G(b)\log b\ll L\sum_{d\le L}G(d)/d$. Finally $\log(L/b)\le L/b$ proves the upper estimate in (3).

For the reverse bound, let $R=\lfloor L^{1/16}\rfloor$. The Euler product on primes at most $R$ is a fixed fraction of $P_G(L)$, since $\sum_{R<p\le L}1/p\ll1$ by the logarithmic prime sum. In its squarefree expansion the mean of the logarithm of the product is at most $\sum_{p\le R}(\log p)/p\le2\log R$. Hence at least half the mass lies on products $a\le R^4$. For each such $a$, take primes $R^4<p\le L/a$ outside the at most $(\log L)^2+2$ exceptional bases. Chebyshev's lower bound gives $\gg L/(a\log L)$ choices, since at most $R^4+(\log L)^2+2$ primes were excluded. The products $ap$ are distinct and $G(ap)\ge uG(a)$. This proves the lower mean.

The harmonic Euler comparison for the constant weight 1 gives $\prod_{p\le L}(1+1/p)\asymp\log L$. For all unexceptional primes, $1+G(p)/p\ge(1+1/p)^u$. Removing $J'$ primes costs at most $O(1+\log(J'+3))$ in the product, by bounding primes up to $J'$ with the harmonic estimate and larger primes by $\exp(J'/(J'+1))$. This proves the second bound in (3). The same upper-mean argument applied to $s^{\omega(b)}$ gives the two bounds used in (2), since its Euler product is $O_s((\log L)^s)$ by comparison of logarithms. [Euler sums](PrimeEstimates.lean) · [Mean estimates](Mean.lean)

Divide (2) by the positive lower bound for the term. Since $(s-1)-(-s)=2s-1<0$, choosing $\nu$ small gives a relative translation error tending to zero as $L\to\infty$. Retained terms have $L\ge q$. Thus for $q>Y_0$ a single relative error $\rho_s(Y_0)\to0$ works for every term. [Arithmetic identity](SeedArithmetic.lean) · [Relative comparison](TermComparison.lean)

## 6. Sum the errors on a set of only $n$ inputs

Under weights proportional to $G(b)$ for $1\le b\le L$, an event $p^j\mid b$ with $p^j\le\sqrt L$ has probability $O_s(1/p^j)$. Indeed its numerator is at most $\sum_{t\le L/p^j}G(t)$, and (3) applies its upper bound there and its lower bound at $L$. At most one distinct prime can divide $b$ to a power greater than $\sqrt L$. It contributes at most one capped unit. Hence the expected capped score is $O_s(1+\mu)$ by $\sum_{p,j\ge1} w_p/p^j\le2\mu$, where the sum in $p$ is over the chosen primes. On the exact buckets the required bases add at most three more units, since a positive crossing has $Z(V)<1$. All other valuations at $db$ equal their valuations at $b$. The pointwise sieve comparison and Markov's inequality now bound the part of an initial term's mass at score greater than $H$ by $O_s(1+\mu)/H$ times its mass. Fix $H=H(s)$ so that this fraction is at most $1/4$. [Conditional score](WeightedTail.lean) · [Tail bound](SeedTail.lean)

The terms with $q\le Y_0$ have only finitely many choices for $q,V$ and their buckets, depending on $Y_0,K$. The total number of choices for the top prime and its bucket is
$\sum_{p\le5n}\lfloor\log_p M\rfloor=o(n)$. For $p>n^{1/4}$ the logarithm is bounded since $M\le(2n)^3$. The remaining sum is $O(n^{1/4}\log M)$. Thus the bounded absolute translation errors for small $q$ sum to $o(n)$. For large enough $L$, depending on $Y_0$, the mean and tail estimates apply to these terms too. The ones with smaller $L$ have bounded mass apiece and total $o(n)$. [Counting the small-prime terms](SeedCount.lean) · [Uniform tail](TermTail.lean)

Let $T_0=\sum_{a\in[M]}F(a)$. Summing the comparisons and using $F\le h(Z)\le Z$ gives

$$
\begin{aligned}
\sum_{b\in I}h(Z(b))&\ge(1-\rho_s(Y_0))T_0-o(n),\\
\sum_{a\in A_0}F(a)&\le \min\{T_0,\ Hm+T_0/4+o(n)\}.
\end{aligned}
$$

The first upper bound in the minimum uses source nonnegativity. The second splits at score $H$. If $T_0>2Hn$ and $\rho_s(Y_0)\le1/4$, the target pays for the source up to $o(n)$. If $T_0\le2Hn$, the loss is at most $2H\rho_s(Y_0)n+o(n)$. Restoring the bucket error and the source crossing bound proves

$$
\sum_{a\in A_0}Z_{\rm original}(a)-\sum_{b\in I}h(Z_{\rm original}(b))
\le \frac{m}{s}
+\left(\frac{Y_0+1}{K}+\delta_s(Y_0)+2H\rho_s(Y_0)\right)n+o(n).
$$

Given the desired tolerance, first choose $s<1/2$ with $1/s$ sufficiently close to 2. This fixes $H$. Next increase $Y_0$, then $K$. Finally let $n$ grow, keeping all those choices fixed. This proves (1) and therefore the stated selection bound. [Final estimate](Transfer.lean) · [Theorems](Proof.lean)

# When a partition can gain one more part

Let $\rho(f,n)$ be the maximum number of parts in a partition of $n$ into positive integers in which no selection of parts sums to $f$. Let $L$ be the smallest positive integer that does not divide $f$. For every $1\le f\le r$, the recurrence

$$
\rho(f,f+r+L)=\rho(f,f+r)+1
$$

holds whenever $r>2(f-1)L$. Its threshold has order $fL$. For every $f\ge1152$, the recurrence fails for some $r\ge fL/2$. When $f$ is odd, the optimum has a closed formula for every $r\ge f$.

$$
\rho(f,f+r)=
\begin{cases}
(f+r)/2 & r\text{ odd},\\
\max(f,r/2) & r\text{ even}.
\end{cases}
$$

The first line is due to Tan, Wu and Hon. The second gives the exact last failure $r=2f-2$ for every odd $f\ge3$. For example, at $f=5$ the partition maximum at totals $13,15,17$ is $5,5,6$.

Te-Sheng Tan, Dai-Yang Wu and Wing-Kai Hon proved the recurrence beyond $L((L+1)(f-1)+\lceil f/L\rceil)$ and proposed the smaller threshold above in §5, problem 1, p. 1403. Their Corollary 3.1 identifies $f+r-\rho(f,f+r)$ with the minimum number of comparisons in their tiny-pan coin-weighing problem. Thus the new threshold also gives the range where each additional group of $L$ genuine coins costs exactly $L-1$ extra comparisons. [Original paper, *Discrete Mathematics* 340 (2017), 1397–1404](https://doi.org/10.1016/j.disc.2016.09.034)

## Why the recurrence holds

It suffices to find at least $\max(1,\lfloor f/L\rfloor)$ copies of $L$ in each optimal partition at both totals. One can then add a copy at the smaller total and remove a copy at the larger one. Indeed, any newly forbidden sum would use the extra $L$ and fewer than $\lfloor f/L\rfloor$ old copies, so an unused old copy would already give the same sum.

The main counting observation concerns a partition whose parts are all at most $M$. If it avoids $f$ and contains $M$ copies of some divisor $s$ of $f$, it has fewer than $f$ parts. Reserve these copies. Among any $s$ further parts, two of the $s+1$ partial sums agree modulo $s$. Remove the intervening block. Its sum is $js$ with $1\le j\le M$. The reserve realizes every multiple of $s$ from $0$ to $Ms$. Adding each block extends this interval through the total of all the parts used. That total is at most $f-s$, since otherwise the interval includes $f$. Fewer than $s$ parts remain.

Write $k$ for the size of an optimal partition. A partition with copies of $L$ and one large part gives $r\le Lk$. Above the proposed threshold, $k\ge2f-1$. If a part $s<L$ occurred at least $2L-1$ times, the observation with $M=2L-1$ would bound the number of parts below $2L$ by $f-1$. The others each weigh at least $2L$, which would give total weight greater than $Lk+f$.

Thus every $s<L$ occurs at most $2L-2$ times. Comparing all parts with $L+1$ bounds their total deficit from parts below $L$ by $D=(L-1)^2(L+2)$. This forces enough copies of $L$ whenever $L\le f$ and $D+\lfloor f/L\rfloor<f$. Since $\operatorname{lcm}(1,\ldots,L-1)$ divides $f$, only 36 pairs $(f,L)$ remain, the largest with $f=420$. The proof checks these pairs by branching on the multiplicity of each small part and tracking the attainable subset sums. For $f=1,2,4,6$ it also checks the short initial intervals directly. Lean proves the validity of each pruning rule and checks all finite cases in its kernel.

## The exact answer for odd $f$

Suppose both $f$ and the total $n$ are odd. A partition that avoids $f$ and has $k>f$ parts must satisfy $n\ge2k+f$. If it contains a one, start with that one and grow a collection whose subset sums cover every integer from $0$ to its total $S$. Any unused part at most $S+1$ extends the interval. At the end $1\le S<f$, and every unused part is at least $S+2$. Since the collection uses at most $S$ parts, this gives $n-2k\ge S(f-S)\ge f-1$. Parity gives $n-2k\ge f$.

Otherwise all parts are at least two. If $n<2k+f<3k$, there is a two and, since $n$ is odd, some $b>2$. Replace $2,b$ by $b-2$. A selection of sum $f-2$ in the new partition lifts to one of sum $f$ in the original. Use $b$ if it selected the replacement, and add the two otherwise. This reduces $f$ by two, $k$ by one and $n$ by four, contradicting induction. At $f=1$ the minimum odd total of $k$ parts greater than one is $2k+1$.

The two lower bounds are attained by simple candidate partitions. Use $f-1$ ones and $r+1$ for the bound $f$, or use twos and one large part for the bound $r/2$.

## Why the scale is necessary

For general $L$, the proof locates a failure at $r\ge (f-L-2L^2)L$ whenever $f\ge8L^2$. Put $m=2f-1$ and take an optimal partition of $f+mL$. Reserve $\lfloor f/L\rfloor$ copies of $L$. Remove blocks of weight divisible by $L$ from the rest until fewer than $L$ parts remain. Their total is congruent to $f$ modulo $L$ and must exceed $f$, since otherwise the reserved copies could complete it to $f$. Compare the other parts with $L$, using the bounds on parts smaller than $L$. This gives $\rho(f,f+mL)<m+L+2L^2$. At $t=f-L-2L^2$, the $f-1$ ones and one part $tL+1$ show $\rho(f,f+tL)\ge f$. If every step between these totals succeeded, the two bounds would contradict each other.

## Verification and prior work

From the repository root, run

```sh
lake exe cache get
lake build conjectures.TanWuHon.Solution
for module in Statement Partitions Bounds Certificate Cases Lower Odd Solution
do
  lake env leanchecker "conjectures.TanWuHon.$module" || exit 1
done
```

The statement is in [Statement.lean](Statement.lean). The upper bound is in [Solution.lean](Solution.lean), with the lower bounds in [Lower.lean](Lower.lean) and the exact odd case in [Odd.lean](Odd.lean). The proofs depend only on propositional extensionality, classical choice and quotient soundness.

The original paper gives exact thresholds through $f=10$. Searches by title, authors, the proposed threshold and subset-sum avoidance found no earlier proof of the general bound. Hon's 2019 talk reports the earlier eventual-periodicity result. OpenAI’s Codex developed the arguments and the Lean formalization. [Taiwanese Mathematical Society conference program](https://amath2.nchu.edu.tw/tms2019/file_session/06%E9%9B%A2%E6%95%A3%E6%95%B8.pdf)

An independent AI reviewer checked the source and the general proof. A separate calculation of exact subset-sum states verified the recurrence for every forbidden weight from 1 through 14 over at least three full periods past the proposed threshold. It also recovered the odd-weight formula on those ranges.

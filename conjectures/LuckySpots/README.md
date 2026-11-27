# Proof of Butler, Hadaway, Lenius, Martens and Moats’s Conjecture 13 on lucky spots in parking functions

For $n$ cars and $n$ spots, let $G(n,j)$ count the parking functions for which the car in spot $j$ asked for that spot. Put $r=n+1-j$. For every $1\le j\le n$,

$$
2jG(n,j)=(j+1)(n+1)^{n-1}
-\sum_{h=0}^{j-2}\binom nh j^h r^{n-1-h}.
$$

Cars arrive in the order of their preference list. Each takes the first free spot at or after its preference. A list is a parking function if all cars park. There are $(n+1)^{n-1}$ such lists.

Butler, Hadaway, Lenius, Martens and Moats found the counts for the first five spots. Their Conjecture 13 predicts a polynomial correction for each fixed spot and a limiting probability. The formula above gives both. For $j\ge2$, factoring $r^r$ out of the sum gives the polynomial

$$
f_j(n)=\frac1{2j}\sum_{h=0}^{j-2}\binom nh j^h (n+1-j)^{j-2-h}.
$$

Every summand has degree $j-2$ and positive leading coefficient. The resulting limiting probability is

$$
\frac{j+1}{2j}-\frac{e^{-j}}{2j}\sum_{h=0}^{j-2}\frac{j^h}{h!}.
$$

The first spot is always lucky. The formula also answers the authors' Question 15 about the next-to-last spot. Completing the binomial sum leaves just its last three terms and gives $4G(n,n-1)=(n+1)^{n-1}+(5n-1)(n-1)^{n-2}$ for $n\ge2$. The first four counts are $3,11,74,708$. [Original paper, pp. 10–11](https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.pdf#page=10) · [OEIS A374533](https://oeis.org/A374533)

## Proof

Run any $l\ge j$ preferences on a circle of $j$ spots. The first $j$ cars fill it. At arrival $s$ there are $j-s+1$ free spots, so the expected number of lucky cars is $(j+1)/2$. Rotation makes the chance of luck at any one site $K_j=(j+1)/(2j)$. The last site's luck agrees with its luck on a line because the first wrap can occur only after this site fills.

Let $A_j(l)$ count the $l$-letter words that fill the first $j$ spots and make the last one lucky. Write $F_i$ for the number of parking functions on $i$ spots, including $F_0=1$. If the first empty spot is $i+1<j$, exactly $i$ preferences lie to its left. They form a parking function there. The other preferences alone determine the luck of $j$. Thus $A_j(l)=E_j(l)$ for $l\ge j$, where

$$
E_j(l)=K_j j^l-\sum_{\substack{0\le i\le j-2\\i\le l}}
\binom li F_i K_{j-i-1}(j-i-1)^{l-i}.
$$

For $l<j-1$, there are at least two vacancies. The same first-empty cases partition all $j^l$ words. Write $t_i=\binom li F_i(j-i-1)^{l-i}$ for the size of each case. Counting occurrences of the letter $j$ yields $\sum_i t_i(l-i)/(j-i-1)=lj^l/j$. Substituting this and $\sum_i t_i=j^l$ into the expression for $E_j(l)$ gives $(l-j+1)E_j(l)=j^l/(2j)$.

Now let $l$ of the $n$ preferences lie in the first $j$ spots. These must fill that block. The remaining $n-l$ preferences must all park in the $r-1$ higher spots. On a circle of $r$ spots there are $l-j+1$ vacancies after those cars park. Rotation therefore gives $(l-j+1)r^{n-l}/r$ valid higher words. The two subwords can interleave in any order. Multiply this count by $\binom nl E_j(l)$ and sum over $l\ge j$.

Extend this sum to $0\le l\le n$. Each fixed $i$ term cancels. After the $i$ left preferences are chosen, the other $n-i$ cars have $n-i$ possible letters each, of which $j-i-1$ are lower letters. The mean of $l$ is therefore $i+(j-i-1)=j-1$. The binomial theorem gives $K_j(n+1)^{n-1}$ for the remaining term. Removing the terms with $l<j-1$ gives the stated formula.

## Sources and verification

Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens and Marshall Moats, “Lucky Cars and Lucky Spots in Parking Functions,” *Journal of Integer Sequences* **29** (2026), Article 26.1.1. The preprint labels this claim Conjecture 3.1. The authors use Pollak's rotation argument for lucky cars. Searches by title, conjecture, authors, statistic, and OEIS entries found no prior formula for every lucky spot. OpenAI Codex derived the count and formalized the proof. [Published article](https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.pdf#page=10) · [Preprint](https://arxiv.org/abs/2412.07873) · [Lucky-spot count table](https://oeis.org/A374756)

Lean checks the original parking process, the finite count, the polynomial degree, and the probability limit. [Statement](Statement.lean) · [Final theorems](Solution.lean)

```sh
# Run at the merge commit for PR #80.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

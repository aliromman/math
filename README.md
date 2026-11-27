# Mathematical conjectures

Proofs, counterexamples, and partial results on published mathematical conjectures. Ali Romman created and maintains the collection. OpenAI Codex assisted with the research and Lean 4 formalizations.

[Research ledger and cumulative statistics](research/ledger.md) · [Verification](#verification)

## Results

Each row links to the research note, its proof or search code, and the pull request. Open drafts link to a fixed revision. **Partial** marks an investigation with an open main question. **Extension** marks work that extends an earlier counterexample.

[Additive combinatorics](#additive-combinatorics) · [Algebra and number theory](#algebra-and-number-theory) · [Dice and games](#dice-and-games) · [Euclidean and discrete geometry](#euclidean-and-discrete-geometry) · [Graphs and tournaments](#graphs-and-tournaments) · [Matroids, polytopes and posets](#matroids-polytopes-and-posets) · [Probability and stochastic processes](#probability-and-stochastic-processes) · [Trees](#trees) · [Voting and apportionment](#voting-and-apportionment) · [Words and permutations](#words-and-permutations)

### Additive combinatorics

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Proof of Ascoli et al.’s Conjecture 1.6 on product-dominant subsets of generalized dihedral groups][note-52] | Subsets with more products than quotients outnumber those with more quotients than products in every finite nonabelian generalized dihedral group. | [Lean][proof-52] · [#52][pr-52] (open draft) |
| [Disproof of Bajnok’s Conjecture 7 on extremizers for restricted sumsets in finite abelian groups][note-28] | Up to affine equivalence, exactly two eight-element sets modulo 17 have only 16 sums of three distinct elements. One is an interval. The other consists of the nonzero squares. | [Lean][proof-28] · [#28][pr-28] |
| [Proof of Cilleruelo, Serra and Wötzel’s conjecture on the maximum size of Sidon set systems][note-61] | For every fixed set size $k\ge2$, the largest Sidon system attains the known upper bound asymptotically. The previously open sizes were $k\ge4$. | [Lean][proof-61] · [#61][pr-61] |
| [Proof of Conlon, Fox and Pham’s Conjecture 10 on the logarithmic density of monochromatic subset sums][note-59] | For every $r\ge3$, an explicit sharp upper logarithmic density of monochromatic subset sums is guaranteed and attained. The source settled the two-color case. | [Lean][proof-59] · [#59][pr-59] |
| [Proof of Lazarev, Miller and O’Bryant’s Conjecture 8.1 on the first present sum][note-66] | Given $k$ missing sums, the limiting mean position of the first present sum is $k/2+O(1)$. | [Lean][proof-66] · [#66][pr-66] |
| [Proof of Lazarev, Miller and O’Bryant’s Conjecture 8.2 on the start of the longest sumset interval][note-67] | With $k$ missing sums, every tie rule gives the same limiting mean left endpoint, $k/2+O(1)$. | [Lean][proof-67] · [#67][pr-67] |
| [Disproof of the pointwise bound in Sobolewski’s Conjecture 2 on monochromatic progressions in binary pattern sequences][note-27] | For every integer $j\ge5$, the binary pattern `1` followed by $j$ zeros gives a monochromatic arithmetic progression of at least $2^j$ terms where the predicted bound is below 17. | [Lean][proof-27] · [#27][pr-27] |
| [Solution to Questions 4.1 and 4.2 of Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio on Buchweitz sets][note-24] | A numerical semigroup has obstructions precisely at orders 2 and 4. Its excess counts at orders 2, 3, and 4 also disprove the proposed unimodality. | [Lean][proof-24] · [#24][pr-24] |
| [Disproof of Sun’s Conjecture 3.10(ii) on simultaneous distinct differences and products in a circular order][note-19] | Every circular order of four distinct positive numbers repeats a directed difference or adjacent product exactly when the middle two are the harmonic and arithmetic means of the extremes. | [Lean][proof-19] · [#19][pr-19] |
| [Disproof of Sun’s Conjecture 3.3(ii) on distinct cyclic differences in finite abelian groups of odd order][note-18] | Remove any two elements from an abelian group of odd order $N\ge5$. Every circular ordering of the rest repeats a directed difference between neighbors. | [Lean][proof-18] · [#18][pr-18] |

### Algebra and number theory

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Proof of Bagchi and Zhou-Zheng’s Conjecture 12 on sporadic shifts without triangular Diophantine pairs][note-23] | For every integer $k\ge0$, adding $2\cdot7^{6k+2}$ to a product of two positive triangular numbers gives a nonsquare. | [Lean][proof-23] · [#23][pr-23] |
| [Disproof of the Chidambaram–Mináč–Nguyen–Tân equidistribution conjecture for cyclotomic factors of Fekete polynomials][note-88] | At odd index $1{,}122{,}987$, the 63rd cyclotomic polynomial divides the Fekete polynomial, although the relevant residue counts differ by one. | [Lean][proof-88] · [#88][pr-88] |
| [Proof of the Evans–Veselov–Winn Factor 4 Conjecture for Markov polynomials][note-85] | In every Markov numerator, every coefficient strictly inside the critical triangle is divisible by four. The proof establishes divisibility throughout the surrounding lower rectangle. | [Lean][proof-85] · [#85][pr-85] |
| [Proof of the Evans–Veselov–Winn Location of 4 conjecture for Markov polynomials][note-86] | For every reduced slope $1<a<b$, the unique monomial on $bi+aj=ab+1$ has coefficient exactly $4$. | [Lean][proof-86] · [#86][pr-86] |
| [Four-factor counterexamples to Gatzweiler and Krattenthaler’s Conjecture 4][note-36] | **Extension.** A four-factor family gives a negative coefficient. Earlier counterexamples had already disproved the conjecture. | [Lean][proof-36] · [#36][pr-36] |
| [Proof of Karlovsky’s Conjecture 2 on the sum bound for distinct positive factors][note-77] | For $n=k+2\ge4$ distinct positive factors whose product is $F$ times their sum, the sum is at most $(F+1)(F+1+k!k(k+1)/2)/k!$. | [Lean][proof-77] · [#77][pr-77] |
| [Proof of Karlovsky’s Conjecture 3 on attainment of the distinct-factor sum bound][note-78] | For $k=n-2\ge2$, equality occurs precisely at $F=k!y-1$ with $y>k$. The maximizing tuple is then unique up to order. | [Lean][proof-78] · [#78][pr-78] |
| [Disproof of the Lucas-sequence assertion in Sun’s Conjecture 3.1 on successive root ratios][note-11] | For the Lucas sequence with parameters $(A,B)=(3,-26)$, the ratio $u_{n+1}^{1/(n+1)}/u_n^{1/n}$ increases from $n=5$ to $n=6$. | [Lean][proof-11] · [#11][pr-11] |
| [Proof of Mabilat’s conjecture on irreducible golden-ratio quiddities][note-38] | The irreducible quiddities over $\mathbb Z\lambda$ are classified for $\lambda=2\cos(\pi/q)$ and every integer $q\ge4$, including the conjectured golden-ratio case. | [Lean][proof-38] · [#38][pr-38] |
| [Disproof of Mascia, Rinaldo and Romeo’s Conjecture 1.2 on zig-zag walks and prime polyomino ideals][note-64] | A thirteen-cell polyomino has no zigzag walk in the source’s sense, and its coordinate ring has zero divisors over every field. | [Lean][proof-64] · [#64][pr-64] |
| [Proof of Somu and Tran’s Conjecture 14 on sums of a practical number and two polygonal numbers][note-73] | For each order 4, 5, 6, 7, 8, and 10, every positive integer is a practical number plus two polygonal numbers of that order. | [Lean][proof-73] · [#73][pr-73] (open draft) |
| [Disproof of Sun’s Conjecture 2.1 on a real-power extension of Mandl’s inequality using Panaitopol’s nine-prime example][note-16] | The first nine primes at exponent $1/2000$ violate the proposed real-power extension of Mandl’s inequality. | [Lean][proof-16] · [#16][pr-16] |
| [Solution to Tan, Wu and Hon’s Problem 1 on the periodicity threshold for partitions avoiding a prescribed sum][note-71] | The period begins by $2(f-1)L$, where $L$ is the least nondivisor of the forbidden sum $f$. For every odd $f\ge3$, the last failure is exactly $2f-2$. | [Lean][proof-71] · [#71][pr-71] (open draft) |
| [Proof of Tengely and Ulas’s Conjecture 4.6 on equal values of restricted partition functions][note-97] | For all $3\le a<b$, the numbers of partitions using parts $1,2,a$ and $1,2,b$ agree at infinitely many pairs of positive arguments. | [Lean][proof-97] · [#97][pr-97] |
| [Proof of Ulas’s Conjecture 4.4 on real zeros of Stern polynomials][note-70] | Every real value in Ulas’s family is positive. Its possible prime divisors at integer arguments are exactly the primes congruent to one modulo three. | [Positivity][proof-70] · [Prime divisors][arith-70] · [#70][pr-70] |

### Dice and games

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Solution to Beideman, Bowen and Müyesser’s Question 3 for finite-depth impartial games][note-50] | For any impartial game of finite depth $d$, a selective compound with a Nim heap of size $k$ has Grundy value $k+d$ when $k\ge\lfloor d^2/4\rfloor$. The cutoff is sharp at every depth. | [Lean][proof-50] · [#50][pr-50] |
| [Solution to Bellec and Fritz’s attainment question for the Beat the Average game][note-90] | With $m\ge3$ independent rolls, the first roll falls below their mean with any probability strictly between $1/m$ and $(m-1)/m$. Both endpoints are unattainable. | [Lean][proof-90] · [#90][pr-90] |
| [Proof of Conjecture 1.11 of Garcia-Fernandezsesma and coauthors on the mean length of the accelerated Zeckendorf game][note-92] | Starting from $n$ ones, the mean number of turns is $O((\log n)^3)$, proving the proposed sublinear bound. | [Lean][proof-92] · [#92][pr-92] |
| [Disproof of Drexel, Peng and Richey’s Conjecture 1 on bias monotonicity in Penney’s ante][note-74] | At the same head probability near $0.451$, the count of favored longer words increases immediately to the right, for every length cap $n\ge4$. | [Lean][proof-74] · [#74][pr-74] |
| [Proof of Gallian and Rusin’s conjecture on the maximum game-size of 30-sided dice][note-63] | Exactly 44 different 30-sided dice occur in games with standard sum frequencies. Forty-three can occur in three-dice games, and the remaining die needs four. | [Lean][proof-63] · [#63][pr-63] (open draft) |
| [Proof of Gallian and Rusin’s conjecture on the number of 105-sided solution dice][note-62] | Exactly 40 different 105-sided dice occur in games with standard sum frequencies, and all 40 occur in three-dice games. | [Lean][proof-62] · [#62][pr-62] (open draft) |
| [Proof of Gallian and Rusin’s conjecture on the number of solution dice with p²q sides][note-65] | For every pair of distinct primes $p,q$, exactly 22 different $p^2q$-sided dice occur in games with standard sum frequencies. Each occurs in a three-dice game. | [Lean][proof-65] · [#65][pr-65] (open draft) |
| [Disproof of Hur and Kim’s fair dice conjecture (Conjecture 1)][note-32] | Three fair eight-sided dice stay fixed under both Hur–Kim moves, and their word cannot start with the proposed six-letter palindrome. | [Lean][proof-32] · [#32][pr-32] |

### Euclidean and discrete geometry

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Disproof of Aichholzer et al.’s wheel-set conjecture for perfect matchings with prescribed crossings][note-68] | At ten crossings, twelve convex points admit 252 perfect matchings, a set with one interior point admits 248, and the regular wheel admits 176. | [Lean][proof-68] · [#68][pr-68] |
| [Solution to the Barequet–Madras–Peters problem on nonsquare minimum-area totally concave polyominoes][note-47] | Minimum-area $t$-fold totally concave polyominoes can have nonsquare bounding boxes for every $t\ge4$. | [Lean][proof-47] · [#47][pr-47] (open draft) |
| [Proof of Edelsbrunner, Garber and Saghafian’s Conjecture C on maximal planar hypertriangulations][note-87] | At every level, every maximal hypertriangulation has the same maximum number of triangles. Any smaller one admits a single insertion that splits a triangle into three. | [Lean][proof-87] · [#87][pr-87] |
| [Solution to Erdős–Purdy–Straus Problem 3.4 on the sharp area ratio for a largest inscribed triangle with a boundary side.][note-81] | The sharp ratio of the area of a convex body to that of its triangle is $\pi-4\arctan(t)-t^2=2.3075689464\ldots$, where $(1+t)^4=2(1+t^2)$ and $0<t<1/4$. | [Lean][proof-81] · [#81][pr-81] |
| [Disproof of Liu’s Conjecture 1 on the median refinement of the Erdős–Mordell inequality][note-15] | At an interior point of a thin obtuse triangle, the sum of vertex distances divided by the sum of side distances is below $45.84$. The proposed lower bound exceeds $45.89$. | [Lean][proof-15] · [#15][pr-15] |
| [Proof of Liu’s Conjecture 1 on Walker’s inequality with side-power weights][note-2] | The cyclic inequality with side weight $a^k$ holds on every nonobtuse triangle for all real $k\le4$. | [Lean][proof-2] · [#2][pr-2] |
| [Proof of Liu’s Conjecture 2 on Walker’s inequality with side-sum weights][note-3] | The cyclic inequality with side-sum weight $(b+c)^k$ holds on every nonobtuse triangle for all real $k\ge-10$. | [Lean][proof-3] · [#3][pr-3] |
| [Proof of Liu’s Conjecture 3 on Walker’s inequality with triangle-excess weights][note-4] | The cyclic inequality with weight $(b+c-a)^k$ holds on every nonobtuse triangle for all real $k\ge-3$. | [Lean][proof-4] · [#4][pr-4] |
| [Disproof of Liu’s Conjecture 6.4 on weighted Erdős–Mordell bounds for an interior point][note-14] | An isosceles triangle and an interior point violate the proposed upper bound at $k=3999/1000$. | [Lean][proof-14] · [#14][pr-14] |
| [Proof of Palsson and Yu’s Conjecture 10 on planar point sets with four triangle congruence classes][note-41] | Seven planar points with at most four triangle shapes form a regular heptagon. The maximum size for four shapes is seven. | [Lean][proof-41] · [#41][pr-41] (open draft) |
| [Partial result on Erdős Problem 107 for 33-point extensions of specified 27- and 30-point order types][note-9] | **Partial.** Checked SAT certificates rule out heptagon-free 33-point extensions of one specified 27-point order type and all 496 two-point deletions from the classical 32-point example. The general question remains open. | [Search][proof-9] · [#9][pr-9] |
| [The sharp lattice-square bound in Bárány and Füredi’s covering-radius conjecture][note-48] | **Extension.** The sharp covering ratio for lattice squares is $3/2$. Counterexamples exist at unbounded lattice diameter. The source already contained a counterexample among convex polygons. | [Lean][proof-48] · [#48][pr-48] |
| [Disproof of Straus’s Conjecture 1 on largest inscribed polygons with a boundary side][note-75] | A nine-vertex polygon has a largest quadrilateral with exactly one shared side and area fraction $2/3$. A quadrilateral in the regular heptagon occupies more. | [Lean][proof-75] · [#75][pr-75] |

### Graphs and tournaments

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Proof of Alikhani’s Conjecture 5 on the minimum degree and the number of distinct edge-cover roots][note-20] | A finite simple graph of minimum degree $d$ has at least $d$ distinct complex roots in its edge-cover polynomial. | [Lean][proof-20] · [#20][pr-20] |
| [Proof of Brown and Cameron’s Conjecture 4.2 on the maximum modulus of independence roots of graphs][note-29] | For a graph on $n\ge3$ vertices, every independence root has modulus at most $\max(p_1\cdots p_r+r)$ over all partitions $p_1+\cdots+p_r=n-1$ into positive integers. | [Lean][proof-29] · [#29][pr-29] |
| [Disproof of Brown and Mol’s conjecture on uniqueness of node-reliability fixed points in graphs with two or more cut vertices][note-101] | Even with two cut vertices, node reliability can cross the diagonal arbitrarily many times. A 36-vertex example has at least three crossings. | [Lean][proof-101] · [#101][pr-101] (open draft) |
| [Solution to George’s problem on the rational degree roots of graphs of a given order][note-12] | For coprime positive integers $p,q$, some simple graph on $n\ge1$ vertices has root $-p/q$ exactly when $p+q$ divides odd $n$ or $2(p+q)$ divides even $n$. | [Lean][proof-12] · [#12][pr-12] |
| [Solution to Haslegrave’s Question 1 on difference and sum indices of bipartite graphs][note-53] | For every positive integer $d$, a finite connected bipartite graph has difference index $d$ and sum index $d+1$. | [Lean][proof-53] · [#53][pr-53] |
| [Solution to Haslegrave’s Question 3 on exclusive sum numbers and bounded sum index][note-56] | A finite graph with sum index $s$ has exclusive sum number at most $s3^{s-1}$. | [Lean][proof-56] · [#56][pr-56] |
| [Disproof of Leander and Linusson’s Conjecture 2 on path correlation in randomly oriented fixed-edge graphs][note-94] | With four vertices and three randomly oriented edges the path covariance is $-9/400$. For every fixed positive edge count $m$, multiplying it by $n^4$ gives limit $-m$. | [Lean][proof-94] · [#94][pr-94] |
| [Disproof of Li’s Odd Biconnected Graphs Conjecture on sandpile identities][note-39] | An infinite family of biconnected graphs of odd order has the maximal stable sandpile identity for every sink. These graphs are neither cycles nor complete. | [Lean][proof-39] · [#39][pr-39] |
| [Disproof of Ma and Tang’s Conjecture 5.2 on even-cycle homomorphism densities in tournaments][note-89] | Three equal transitive groups oriented in a cycle have triangle density $1/9$ and limiting six-cycle density $5/486$, below the proposed minimum by $775/1889568$. | [Lean][proof-89] · [#89][pr-89] |
| [Proof of Pirzada, Naikoo and Chishti’s Conjecture 2.1 on bipartite score sets][note-60] | Every nonempty finite set of positive integers is the full set of scores of an oriented bipartite graph. | [Lean][proof-60] · [#60][pr-60] |
| [Disproof of Savchenko’s conjecture on minimum cycle counts in tournaments of bounded diameter][note-91] | Moving one vertex within a 22-vertex tournament of diameter eight lowers the proposed minimum of 68 directed four-cycles to 67. At diameter ten a move lowers 44 five-cycles to 42. | [Lean][proof-91] · [#91][pr-91] |
| [Proof of Savchenko’s conjecture on the minimum number of directed six-cycles in a regular tournament][note-95] | Among all regular tournaments of every odd order, the circular tournament minimizes simple directed six-cycles. A seven-vertex determinant inequality gives a quantitative gap. | [Lean][proof-95] · [#95][pr-95] |
| [Proof of Yang, Yerger and Zhou’s Conjecture 2 on pebbling weights for pendant hypercubes][note-57] | Reciprocal distance gives a valid pebbling weight at a pendant root attached to a hypercube of every dimension $m\ge2$. | [Lean][proof-57] · [#57][pr-57] |

### Matroids, polytopes and posets

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Disproof of Defant and Lin’s Conjecture 10.2 on down-degree homometry in ν-Tamari lattices][note-54] | Two six-element rowmotion orbits in the same $\nu$-Tamari lattice have down-degree sums 18 and 17. | [Lean][proof-54] · [#54][pr-54] |
| [Disproof of Elizalde et al.’s Conjecture 5.4(b) on order-ideal sizes under fence rowmotion][note-51] | A 32-element fence has a 237-ideal rowmotion orbit with mean size $16-6/79$, below the predicted 16. | [Lean][proof-51] · [#51][pr-51] (open draft) |
| [Solution to Faustini and Vargas’s Problem 6.7 on flag vectors of connected split matroids][note-40] | Two connected rank-three matroid base polytopes have identical face counts and differ by one incidence between a vertex and a four-dimensional face. | [Lean][proof-40] · [#40][pr-40] (open draft) |
| [Solution to Ferroni and Schröter’s Problem 3.5 on the initial entries of matroid base polytope f-vectors][note-30] | For every prefix length, two connected rank-two matroid base polytopes on equally many elements have the same initial face counts and differ by one facet. | [Lean][proof-30] · [#30][pr-30] |
| [Solution to the generalized-permutohedron part of Defant’s Question 6.1 on real-rooted Narayana sums][note-22] | A translated Fano matroid base polytope has 28 lattice points and a Narayana sum with four nonreal roots. | [Lean][proof-22] · [#22][pr-22] |
| [Proof of Kölbl’s Conjecture 3 on canonical-line Ehrhart roots of reflexive polytopes with unimodal numerators][note-21] | Among reflexive lattice polytopes with unimodal Ehrhart numerator, the standard reflexive simplex attains the greatest root height on $\operatorname{Re}z=-1/2$ in every positive dimension. | [Lean][proof-21] · [#21][pr-21] |
| [Solution to Lundström and Saud Maia Leite’s Question 6.4 on Ehrhart nonnegativity of order polytopes of polygon face lattices][note-93] | For a 13-gon the order polytope of its full face lattice has linear Ehrhart coefficient $-298495711/35302608$. | [Lean][proof-93] · [#93][pr-93] |

### Probability and stochastic processes

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Disproof of Berend, Ernst, Kontorovich and Kumar’s Conjecture 5.2 as stated and proof of the corrected interior interval tiling][note-96] | A deterministic endpoint disproves the literal ordering. The closures of the nondegenerate interior intervals tile in lexicographic order for every even order of independence. | [Lean][proof-96] · [#96][pr-96] |
| [Disproof of Campbell’s coupon-collection conjecture in “Games of chance with multiple objectives”][note-82] | In four draws the two probabilities are $3/8<4/9$. The reversal factor grows like $\sqrt{e k/(2\pi)}$ at the earliest square deadline. For fixed goals the proposed order eventually holds. | [Lean][proof-82] · [#82][pr-82] |
| [Correction to the Aldous–Fill hitting-time heuristic for random cyclic adjacent transpositions (Example 7.22)][note-102] | The mean divided by $m!$ is $1+2/m+O(m^{-2})$, correcting the predicted coefficient of one. | [Lean][proof-102] · [#102][pr-102] (open draft) |
| [Proof of the Jacob–Beer–Henze–Hartenstein positive-recurrence conjecture for Matrix event graph width when k > d > 1][note-99] | The width is positive recurrent and its stationary tail has exact exponent $d(k-1)/(k-d)$. | [Lean][proof-99] · [#99][pr-99] |
| [Proof of Khovanova and Wang’s Conjecture 7.1 on uniform final shadows in two-sided chip dispersion][note-100] | All $N-1$ positions of the final double gap have equal probability. | [Lean][proof-100] · [#100][pr-100] |
| [Proof of the Nagaev–Chebotarev conjecture on the exact binomial–Poisson distance at mean one][note-79] | At every mean $0\le\lambda\le1$ and every positive sample size, the largest difference between the two cumulative distributions occurs at zero. | [Lean][proof-79] · [#79][pr-79] |
| [Disproof of Weinberger and Shayevitz’s Conjecture 1 on greedy dictatorship for the binary erasure channel][note-98] | A twelve-bit majority beats the first surviving bit for every message length at least twelve. | [Lean][proof-98] · [#98][pr-98] |

### Trees

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Disproof of the Aliste-Prieto–de Mier–Zamora conjecture on the smallest trees with the same restricted U-polynomial][note-7] | Two 32-vertex trees agree through five cuts. The predicted minimum fails at every depth $m\ge5$, and the minimum is at most $3(m+1)^2$ for $m\ge1$. | [Bound][bound-7] · [Threshold][proof-7] · [#7][pr-7] |
| [Disproof of the Brosch–Puges double-caterpillar conjecture on tree profiles (Conjecture 1)][note-34] | For every $k\ge7$, joining three caterpillars beats the proposed two-caterpillar boundary. The cases $k=4,5,6$ remain open. | [Lean][proof-34] · [#34][pr-34] |
| [Proof of Brown and Cameron’s Conjecture 4.4 on the maximum modulus of independence roots of even-order trees][note-25] | For a tree on $2k$ vertices with $k\ge3$, every root of the independence polynomial has modulus at most $2^{k-2}+k+1$. | [Lean][proof-25] · [#25][pr-25] |
| [Proof of Chauve, Ponty and Wallner’s Conjecture 4.5 on extremal duplication–loss histories][note-43] | For every terminal count of at least two, caterpillars uniquely maximize and balanced trees uniquely minimize ordered, unranked histories at fixed leaf count, up to swaps of children. | [Lean][proof-43] · [#43][pr-43] |
| [Disproof of Clow and van Bommel’s Conjecture 8.2 on eternal distance domination in trees][note-83] | For every positive integer $t$, a tree needs $t$ guards at range three, even under repeated attacks. It needs $2t$ stationary guards at range one. | [Lean][proof-83] · [#83][pr-83] |
| [Disproof of Dossou-Olory and Wagner’s conjecture on four-branch extremizers for the inducibility of the five-leaf tree A₅][note-31] | A root rotation increases the limiting density of the five-leaf tree in every proposed four-branch sequence. Its exact inducibility remains open. | [Lean][proof-31] · [#31][pr-31] |
| [Disproof of the Engbers–Erey conjecture on maximum average maximal-matching size in trees of fixed order and diameter][note-1] | Moving one leaf in a 15-vertex tree preserves diameter 11 and raises the mean size of a maximal matching from $6$ to $259/43$, disproving the proposed maximum. | [Lean][proof-1] · [#1][pr-1] |
| [Proof of George’s Conjecture 1 on nonreal degree roots of trees in the unit disk][note-10] | Every nonreal root of a finite tree’s degree polynomial has modulus greater than one. | [Lean][proof-10] · [#10][pr-10] |
| [Two-site branch exchanges and a finite three-site search in Stanley’s tree isomorphism question][note-6] | **Partial.** An informal proof shows that a two-site branch exchange cannot produce nonisomorphic trees with the same chromatic symmetric function. A separate search distinguished 111,144 trees in a three-site family. | [Search][proof-6] · [#6][pr-6] |
| [Disproof of the universal reading of Wang’s Conjecture 20 on leaves in local-density maximizers][note-76] | A leafless singleton in a 17-vertex tree maximizes local density at $31/52$. In every finite tree, each maximizer extends to one containing a leaf. | [Lean][proof-76] · [#76][pr-76] |

### Voting and apportionment

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Proof of Janson and Linusson’s conjecture on the probability of the Alabama paradox under Hamilton’s method][note-33] | With fixed rationally independent population shares, the limiting frequency of house sizes at which any state loses a seat is at most $1-2/e$. The source gives examples approaching the bound. | [Lean][proof-33] · [#33][pr-33] |
| [Proof of Kurz and Napel’s conjecture on a voter with half the Banzhaf power of each other voter][note-55] | Every committee of at least six voters admits a voting rule that gives one voter half the normalized Banzhaf power of each other voter. | [Lean][proof-55] · [#55][pr-55] |
| [Proof of Kurz’s Conjecture 8 on Banzhaf approximation in weighted voting games][note-58] | Every weighted rule on $n\ge2$ voters has normalized Banzhaf vector at $\ell_1$ distance at least $1/(18n)$ from $(2,\ldots,2,1)/(2n-1)$. | [Lean][proof-58] · [#58][pr-58] |
| [Disproof of McCune’s Conjecture 1 on Alabama-paradox probabilities][note-37] | Exact probabilities for every positive house size and seat increase under the uniform three-state model refute both conjectured monotonicity rules. | [Lean][proof-37] · [#37][pr-37] |

### Words and permutations

| Research note | Finding | Proof or search · PR |
| --- | --- | --- |
| [Proof of Archer et al.’s conjecture on cycles avoiding 3412 in one-line form and 213 in cycle form][note-46] | A two-class decomposition gives the conjectured generating function for cycles avoiding 3412 in one-line notation and 213 in cycle notation starting at 1. | [Lean][proof-46] · [#46][pr-46] |
| [Proof of Bevan and Threlfall’s Conjecture 21 on consecutive patterns between inversion thresholds][note-72] | Every fixed consecutive pattern occurs with probability tending to one throughout the interval between its two inversion thresholds. | [Lean][proof-72] · [#72][pr-72] |
| [Disproof of Bevan and Threlfall’s Conjecture 22 on unimodality of consecutive pattern counts][note-69] | The expected count of 51234 falls and then rises across the 7-, 8-, and 9-inversion layers in seven letters. | [Lean][proof-69] · [#69][pr-69] |
| [Proof of the Burstein–Hästö–Mansour conjecture on the packing density of the vincular pattern 12-1][note-13] | Two letters attain the exact maximum of $\lfloor n(n-1)/6\rfloor$ occurrences at every word length $n$. The packing density is $1/3$. | [Lean][proof-13] · [#13][pr-13] |
| [Proof of Butler, Hadaway, Lenius, Martens and Moats’s Conjecture 13 on lucky spots in parking functions][note-80] | An exact finite binomial sum counts parking functions in which any prescribed spot receives the car that preferred it. The same formula gives the limiting probability. | [Lean][proof-80] · [#80][pr-80] |
| [Proof of Černý’s Conjecture 34 on counting fair words][note-35] | At each positive length $n$, the fair-word count is a monic integer polynomial of degree $\lceil n/2\rceil$ in the alphabet size. | [Lean][proof-35] · [#35][pr-35] |
| [Disproof of Fang’s Conjecture 5.7 on the length of a most frequent subsequence][note-42] | A word of length ten has a unique most frequent subsequence of length six. A binary example also violates the proposed length bound. | [Lean][proof-42] · [#42][pr-42] |
| [Disproof of the finite layered-maximizer assertion in Burstein, Hästö and Mansour’s Conjecture 2.8][note-17] | The word `111342222` contains 61 occurrences of `11123`, `13222`, and `11322` in total. Every layered word of the same length on the same four-letter alphabet has at most 60. | [Lean][proof-17] · [#17][pr-17] |
| [Disproof of Hwang’s conjecture on adding cells to a triangular permutation board][note-44] | Four added cells in an eight-by-eight board allow 589 permutations against the proposed 584. The construction extends to $d$ added cells in every even order $2d\ge8$. | [Lean][proof-44] · [#44][pr-44] |
| [Infinite four-letter counterexamples to Brauner et al.’s Conjecture 4.1 on balanced words][note-49] | **Extension.** Four letters give infinitely many periodic balanced words outside binary congruence expansion. Restivo and Rosone gave the earlier period-16 example. | [Lean][proof-49] · [#49][pr-49] |
| [Solution to Larson’s Question 2 on optimal power maps of symmetric groups][note-45] | Every power map maximizing the number of weak components on $S_n$ acts nontrivially on cycles of just one length. A finite rule lists every maximizing exponent. | [Lean][proof-45] · [#45][pr-45] |
| [Disproof of Presutti and Stromquist’s Conjecture 10.1 on the proposed packing-density optimizer for 2413][note-84] | A weighted permutation gives density at least $0.1047363701829$, above the proposed $0.1047360252660$. A corner argument rules out every choice of the two bubble sizes. | [Lean][proof-84] · [#84][pr-84] (open draft) |

## Verification

### Full verification

Install Elan, then run the following commands from a clean checkout. The first
command gets the build files for the pinned Mathlib release.

```sh
lake exe cache get
python3 scripts/verify.py
python3 scripts/test_verify.py
python3 scripts/test_selection.py
```

Lake builds the research library with warnings as errors. The verifier calls the pinned
`leanchecker` routine in a separate process for each module in the source tree. It checks
that all required object files exist, replays private proof bodies, and
traces the dependencies of every local declaration. Research proofs need
theorem names so the compiler retains them for replay. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

### Scoped pull request checks

On pull requests, CI compares the tested merge commit with its first parent. It rebuilds changed research modules and their transitive importers, replays their proofs, and checks the full axiom contract in each affected directory. Edits to documentation alone pass after the verifier checks whether research sources use the changed files. Changes to the toolchain, dependencies, or verifier require a full check. Select **Run workflow** in the Lean workflow to audit the entire revision. To reproduce a pull request check locally, run `python3 scripts/verify.py --base BASE --fetch-cache`, where `BASE` is the tested base commit.

Each research directory with Lean sources has an `axioms` file. Each line
gives a result's qualified theorem name followed by its exact transitive
axioms, separated by spaces. A theorem with no axioms has only its name on
the line. A line that starts with `statement` can register the definition
of an open question. The research note identifies what the proof establishes
and cites the original source.

© 2026 Ali Romman · [Apache License 2.0](LICENSE) · [Cite this project](CITATION.cff) · [All pull requests][pulls]

[elan]: https://github.com/leanprover/elan
[pulls]: https://github.com/aliromman/math/pulls?q=is%3Apr+sort%3Acreated-desc
[note-102]: https://github.com/aliromman/math/blob/902ad98160373a53b2c2368e8a5fa85d62514625/conjectures/AldousFillAdjacent/README.md
[proof-102]: https://github.com/aliromman/math/blob/902ad98160373a53b2c2368e8a5fa85d62514625/conjectures/AldousFillAdjacent/Solution.lean
[pr-102]: https://github.com/aliromman/math/pull/102
[note-101]: https://github.com/aliromman/math/blob/f306661116f4f5f001258fb026d26fce484d28f6/conjectures/BrownMolFixed/README.md
[proof-101]: https://github.com/aliromman/math/blob/f306661116f4f5f001258fb026d26fce484d28f6/conjectures/BrownMolFixed/Solution.lean
[pr-101]: https://github.com/aliromman/math/pull/101
[note-97]: conjectures/TengelyPartition/README.md
[proof-97]: conjectures/TengelyPartition/Solution.lean
[pr-97]: https://github.com/aliromman/math/pull/97
[note-84]: https://github.com/aliromman/math/blob/005529e656d15bee60f2b20db39b6da8adddf8fd/conjectures/PresuttiStromquist/README.md
[proof-84]: https://github.com/aliromman/math/blob/005529e656d15bee60f2b20db39b6da8adddf8fd/conjectures/PresuttiStromquist/Solution.lean
[pr-84]: https://github.com/aliromman/math/pull/84
[note-81]: conjectures/ErdosPurdyStraus/README.md
[proof-81]: conjectures/ErdosPurdyStraus/Solution.lean
[pr-81]: https://github.com/aliromman/math/pull/81
[note-75]: conjectures/StrausBoundaryPolygon/README.md
[proof-75]: conjectures/StrausBoundaryPolygon/Solution.lean
[pr-75]: https://github.com/aliromman/math/pull/75
[note-73]: https://github.com/aliromman/math/blob/8bd681627f4936632074973d5b52eb5d4a65d7e9/conjectures/PracticalPolygons/README.md
[proof-73]: https://github.com/aliromman/math/blob/8bd681627f4936632074973d5b52eb5d4a65d7e9/conjectures/PracticalPolygons/Solution.lean
[pr-73]: https://github.com/aliromman/math/pull/73
[note-71]: https://github.com/aliromman/math/blob/a30ef138c3548ceb9e2f7b9f2692ed60e28aaebf/conjectures/TanWuHon/README.md
[proof-71]: https://github.com/aliromman/math/blob/a30ef138c3548ceb9e2f7b9f2692ed60e28aaebf/conjectures/TanWuHon/Solution.lean
[pr-71]: https://github.com/aliromman/math/pull/71
[note-70]: conjectures/UlasStern/README.md
[proof-70]: conjectures/UlasStern/Solution.lean
[arith-70]: conjectures/UlasStern/Arithmetic.lean
[pr-70]: https://github.com/aliromman/math/pull/70
[note-65]: https://github.com/aliromman/math/blob/f53bc59a80ac5378dfc30907749277920d12a41f/conjectures/GallianRusinPrimeSquare/README.md
[proof-65]: https://github.com/aliromman/math/blob/f53bc59a80ac5378dfc30907749277920d12a41f/conjectures/GallianRusinPrimeSquare/Solution.lean
[pr-65]: https://github.com/aliromman/math/pull/65
[note-63]: https://github.com/aliromman/math/blob/6792709c95e3525758cb4c8cba06635ec3fc9705/conjectures/GallianRusinGame/README.md
[proof-63]: https://github.com/aliromman/math/blob/6792709c95e3525758cb4c8cba06635ec3fc9705/conjectures/GallianRusinGame/Solution.lean
[pr-63]: https://github.com/aliromman/math/pull/63
[note-62]: https://github.com/aliromman/math/blob/4a1587e3fd417b4897c5de2402677298e676aed3/conjectures/GallianRusinDice/README.md
[proof-62]: https://github.com/aliromman/math/blob/4a1587e3fd417b4897c5de2402677298e676aed3/conjectures/GallianRusinDice/Solution.lean
[pr-62]: https://github.com/aliromman/math/pull/62
[note-60]: conjectures/BipartiteScoreSets/README.md
[proof-60]: conjectures/BipartiteScoreSets/Solution.lean
[pr-60]: https://github.com/aliromman/math/pull/60
[note-56]: conjectures/ExclusiveSumBound/README.md
[proof-56]: conjectures/ExclusiveSumBound/Solution.lean
[pr-56]: https://github.com/aliromman/math/pull/56
[note-53]: conjectures/HaslegraveBipartite/README.md
[proof-53]: conjectures/HaslegraveBipartite/Solution.lean
[pr-53]: https://github.com/aliromman/math/pull/53
[note-52]: https://github.com/aliromman/math/blob/53cf96dac7d827d3500752546741f5bdf732afd5/conjectures/AscoliDihedralDominance/README.md
[proof-52]: https://github.com/aliromman/math/blob/53cf96dac7d827d3500752546741f5bdf732afd5/conjectures/AscoliDihedralDominance/Solution.lean
[pr-52]: https://github.com/aliromman/math/pull/52
[note-51]: https://github.com/aliromman/math/blob/b78b43bea8713d22237982bb3f45e96d095a0b8c/conjectures/FenceRowmotion/README.md
[proof-51]: https://github.com/aliromman/math/blob/b78b43bea8713d22237982bb3f45e96d095a0b8c/conjectures/FenceRowmotion/Solution.lean
[pr-51]: https://github.com/aliromman/math/pull/51
[note-50]: conjectures/SelectiveCompound/README.md
[proof-50]: conjectures/SelectiveCompound/Solution.lean
[pr-50]: https://github.com/aliromman/math/pull/50
[note-47]: https://github.com/aliromman/math/blob/1f814897835080c1384c4e8f2eb1295fcd1b4c68/conjectures/BarequetRectangularPolyomino/README.md
[proof-47]: https://github.com/aliromman/math/blob/1f814897835080c1384c4e8f2eb1295fcd1b4c68/conjectures/BarequetRectangularPolyomino/Solution.lean
[pr-47]: https://github.com/aliromman/math/pull/47
[note-42]: conjectures/FangSubwordLength/README.md
[proof-42]: conjectures/FangSubwordLength/Solution.lean
[pr-42]: https://github.com/aliromman/math/pull/42
[note-41]: https://github.com/aliromman/math/blob/09b4aa8dac511bc84a44ef0f2b2aee8b9546e6d1/conjectures/PalssonYuTriangles/README.md
[proof-41]: https://github.com/aliromman/math/blob/09b4aa8dac511bc84a44ef0f2b2aee8b9546e6d1/conjectures/PalssonYuTriangles/Solution.lean
[pr-41]: https://github.com/aliromman/math/pull/41
[note-40]: https://github.com/aliromman/math/blob/8c27e3ac6e8e418b3e09101b8958f3e113876acc/conjectures/SplitMatroidFlags/README.md
[proof-40]: https://github.com/aliromman/math/blob/8c27e3ac6e8e418b3e09101b8958f3e113876acc/conjectures/SplitMatroidFlags/Solution.lean
[pr-40]: https://github.com/aliromman/math/pull/40
[note-36]: conjectures/GatzweilerKrattenthalerShift/README.md
[proof-36]: conjectures/GatzweilerKrattenthalerShift/Solution.lean
[pr-36]: https://github.com/aliromman/math/pull/36
[note-35]: conjectures/CernyFairWords/README.md
[proof-35]: conjectures/CernyFairWords/Solution.lean
[pr-35]: https://github.com/aliromman/math/pull/35
[note-34]: conjectures/BroschPugesTreeProfile/README.md
[proof-34]: conjectures/BroschPugesTreeProfile/Solution.lean
[pr-34]: https://github.com/aliromman/math/pull/34
[note-32]: conjectures/HurKimFairDice/README.md
[proof-32]: conjectures/HurKimFairDice/Solution.lean
[pr-32]: https://github.com/aliromman/math/pull/32
[note-31]: conjectures/WagnerTreeInducibility/README.md
[proof-31]: conjectures/WagnerTreeInducibility/Solution.lean
[pr-31]: https://github.com/aliromman/math/pull/31
[note-7]: conjectures/RestrictedUMinimum/README.md
[bound-7]: conjectures/RestrictedUMinimum/Growth.lean
[proof-7]: conjectures/RestrictedUMinimum/Threshold.lean
[pr-7]: https://github.com/aliromman/math/pull/7
[note-21]: conjectures/KolblSimplexRoots/README.md
[proof-21]: conjectures/KolblSimplexRoots/Solution.lean
[pr-21]: https://github.com/aliromman/math/pull/21
[note-27]: conjectures/SobolewskiPatternBound/README.md
[proof-27]: conjectures/SobolewskiPatternBound/Solution.lean
[pr-27]: https://github.com/aliromman/math/pull/27
[note-20]: conjectures/EdgeCoverRootCount/README.md
[proof-20]: conjectures/EdgeCoverRootCount/Solution.lean
[pr-20]: https://github.com/aliromman/math/pull/20
[note-13]: conjectures/WordPacking121/README.md
[proof-13]: conjectures/WordPacking121/Proof.lean
[pr-13]: https://github.com/aliromman/math/pull/13
[note-12]: conjectures/GeorgeRationalDegreeRoots/README.md
[proof-12]: conjectures/GeorgeRationalDegreeRoots/Solution.lean
[pr-12]: https://github.com/aliromman/math/pull/12
[note-23]: conjectures/TriangularSporadic/README.md
[proof-23]: conjectures/TriangularSporadic/Solution.lean
[pr-23]: https://github.com/aliromman/math/pull/23
[note-10]: conjectures/GeorgeTreeDegreeRoots/README.md
[proof-10]: conjectures/GeorgeTreeDegreeRoots/Solution.lean
[pr-10]: https://github.com/aliromman/math/pull/10
[note-18]: conjectures/SunCircularDifferences/README.md
[proof-18]: conjectures/SunCircularDifferences/Solution.lean
[pr-18]: https://github.com/aliromman/math/pull/18
[note-19]: conjectures/SunRealCycles/README.md
[proof-19]: conjectures/SunRealCycles/Solution.lean
[pr-19]: https://github.com/aliromman/math/pull/19
[note-1]: conjectures/EngbersErey/README.md
[proof-1]: conjectures/EngbersErey/Solution.lean
[pr-1]: https://github.com/aliromman/math/pull/1
[note-2]: conjectures/LiuWalkerOne/README.md
[proof-2]: conjectures/LiuWalkerOne/Solution.lean
[pr-2]: https://github.com/aliromman/math/pull/2
[note-3]: conjectures/LiuWalkerTwo/README.md
[proof-3]: conjectures/LiuWalkerTwo/Solution.lean
[pr-3]: https://github.com/aliromman/math/pull/3
[note-4]: conjectures/LiuWalkerThree/README.md
[proof-4]: conjectures/LiuWalkerThree/Solution.lean
[pr-4]: https://github.com/aliromman/math/pull/4
[note-16]: conjectures/SunPrimePowers/README.md
[proof-16]: conjectures/SunPrimePowers/Solution.lean
[pr-16]: https://github.com/aliromman/math/pull/16
[note-11]: conjectures/SunLucasRatios/README.md
[proof-11]: conjectures/SunLucasRatios/Solution.lean
[pr-11]: https://github.com/aliromman/math/pull/11
[note-14]: conjectures/LiuWeightedRadicals/README.md
[proof-14]: conjectures/LiuWeightedRadicals/Solution.lean
[pr-14]: https://github.com/aliromman/math/pull/14
[note-15]: conjectures/LiuMedianRatio/README.md
[proof-15]: conjectures/LiuMedianRatio/Solution.lean
[pr-15]: https://github.com/aliromman/math/pull/15
[note-9]: conjectures/ErdosSzekeres/README.md
[proof-9]: conjectures/ErdosSzekeres/replay.py
[pr-9]: https://github.com/aliromman/math/pull/9
[note-6]: conjectures/StanleyTreeCSF/README.md
[proof-6]: conjectures/StanleyTreeCSF/replay.py
[pr-6]: https://github.com/aliromman/math/pull/6
[note-38]: conjectures/MabilatGoldenQuiddities/README.md
[proof-38]: conjectures/MabilatGoldenQuiddities/Solution.lean
[pr-38]: https://github.com/aliromman/math/pull/38
[note-74]: conjectures/PenneyBias/README.md
[proof-74]: conjectures/PenneyBias/Solution.lean
[pr-74]: https://github.com/aliromman/math/pull/74
[note-49]: conjectures/BraunerBalancedWords/README.md
[proof-49]: conjectures/BraunerBalancedWords/Solution.lean
[pr-49]: https://github.com/aliromman/math/pull/49
[note-77]: conjectures/KarlovskySumBound/README.md
[proof-77]: conjectures/KarlovskySumBound/Solution.lean
[pr-77]: https://github.com/aliromman/math/pull/77
[note-78]: conjectures/KarlovskySumAttainment/README.md
[proof-78]: conjectures/KarlovskySumAttainment/Solution.lean
[pr-78]: https://github.com/aliromman/math/pull/78
[note-54]: conjectures/DefantLinHomometry/README.md
[proof-54]: conjectures/DefantLinHomometry/Solution.lean
[pr-54]: https://github.com/aliromman/math/pull/54
[note-39]: conjectures/GaoLiSandpile/README.md
[proof-39]: conjectures/GaoLiSandpile/Solution.lean
[pr-39]: https://github.com/aliromman/math/pull/39
[note-85]: conjectures/MarkovFactorFour/README.md
[proof-85]: conjectures/MarkovFactorFour/Solution.lean
[pr-85]: https://github.com/aliromman/math/pull/85
[note-57]: conjectures/YangYergerZhouCube/README.md
[proof-57]: conjectures/YangYergerZhouCube/Solution.lean
[pr-57]: https://github.com/aliromman/math/pull/57
[note-83]: conjectures/EternalTreeDomination/README.md
[proof-83]: conjectures/EternalTreeDomination/Solution.lean
[pr-83]: https://github.com/aliromman/math/pull/83
[note-58]: conjectures/KurzWeighted/README.md
[proof-58]: conjectures/KurzWeighted/Solution.lean
[pr-58]: https://github.com/aliromman/math/pull/58
[note-69]: conjectures/ConsecutivePatternValley/README.md
[proof-69]: conjectures/ConsecutivePatternValley/Solution.lean
[pr-69]: https://github.com/aliromman/math/pull/69
[note-92]: conjectures/AcceleratedZeckendorf/README.md
[proof-92]: conjectures/AcceleratedZeckendorf/Solution.lean
[pr-92]: https://github.com/aliromman/math/pull/92
[note-90]: conjectures/BellecFritzDice/README.md
[proof-90]: conjectures/BellecFritzDice/Solution.lean
[pr-90]: https://github.com/aliromman/math/pull/90
[note-46]: conjectures/ArcherCycles/README.md
[proof-46]: conjectures/ArcherCycles/Solution.lean
[pr-46]: https://github.com/aliromman/math/pull/46
[note-22]: conjectures/DefantNarayana/README.md
[proof-22]: conjectures/DefantNarayana/Solution.lean
[pr-22]: https://github.com/aliromman/math/pull/22
[note-82]: conjectures/CampbellCoupons/README.md
[proof-82]: conjectures/CampbellCoupons/Solution.lean
[pr-82]: https://github.com/aliromman/math/pull/82
[note-55]: conjectures/KurzBanzhaf/README.md
[proof-55]: conjectures/KurzBanzhaf/Solution.lean
[pr-55]: https://github.com/aliromman/math/pull/55
[note-25]: conjectures/BrownCameronEvenTrees/README.md
[proof-25]: conjectures/BrownCameronEvenTrees/Solution.lean
[pr-25]: https://github.com/aliromman/math/pull/25
[note-29]: conjectures/BrownCameronGraphModulus/README.md
[proof-29]: conjectures/BrownCameronGraphModulus/Solution.lean
[pr-29]: https://github.com/aliromman/math/pull/29
[note-86]: conjectures/MarkovNearestFour/README.md
[proof-86]: conjectures/MarkovNearestFour/Solution.lean
[pr-86]: https://github.com/aliromman/math/pull/86
[note-24]: conjectures/BuchweitzGapset/README.md
[proof-24]: conjectures/BuchweitzGapset/Solution.lean
[pr-24]: https://github.com/aliromman/math/pull/24
[note-100]: conjectures/ChipShadow/README.md
[proof-100]: conjectures/ChipShadow/Solution.lean
[pr-100]: https://github.com/aliromman/math/pull/100
[note-48]: conjectures/BaranyFurediCover/README.md
[proof-48]: conjectures/BaranyFurediCover/Solution.lean
[pr-48]: https://github.com/aliromman/math/pull/48
[note-96]: conjectures/BekkOrder/README.md
[proof-96]: conjectures/BekkOrder/Solution.lean
[pr-96]: https://github.com/aliromman/math/pull/96
[note-91]: conjectures/SavchenkoDiameter/README.md
[proof-91]: conjectures/SavchenkoDiameter/Solution.lean
[pr-91]: https://github.com/aliromman/math/pull/91
[note-64]: conjectures/PolyominoPrimality/README.md
[proof-64]: conjectures/PolyominoPrimality/Solution.lean
[pr-64]: https://github.com/aliromman/math/pull/64
[note-45]: conjectures/LarsonPowerMap/README.md
[proof-45]: conjectures/LarsonPowerMap/Solution.lean
[pr-45]: https://github.com/aliromman/math/pull/45
[note-79]: conjectures/PoissonApproximation/README.md
[proof-79]: conjectures/PoissonApproximation/Solution.lean
[pr-79]: https://github.com/aliromman/math/pull/79
[note-30]: conjectures/FerroniFacePrefix/README.md
[proof-30]: conjectures/FerroniFacePrefix/Solution.lean
[pr-30]: https://github.com/aliromman/math/pull/30
[note-99]: conjectures/MatrixWidth/README.md
[proof-99]: conjectures/MatrixWidth/Solution.lean
[pr-99]: https://github.com/aliromman/math/pull/99
[note-44]: conjectures/HwangPermanent/README.md
[proof-44]: conjectures/HwangPermanent/Solution.lean
[pr-44]: https://github.com/aliromman/math/pull/44
[note-88]: conjectures/FeketeEquidistribution/README.md
[proof-88]: conjectures/FeketeEquidistribution/Solution.lean
[pr-88]: https://github.com/aliromman/math/pull/88
[note-33]: conjectures/AlabamaParadox/README.md
[proof-33]: conjectures/AlabamaParadox/Solution.lean
[pr-33]: https://github.com/aliromman/math/pull/33
[note-37]: conjectures/McCuneSeatJumps/README.md
[proof-37]: conjectures/McCuneSeatJumps/Solution.lean
[pr-37]: https://github.com/aliromman/math/pull/37
[note-93]: conjectures/PolygonEhrhart/README.md
[proof-93]: conjectures/PolygonEhrhart/Solution.lean
[pr-93]: https://github.com/aliromman/math/pull/93
[note-94]: conjectures/LeanderLinusson/README.md
[proof-94]: conjectures/LeanderLinusson/Solution.lean
[pr-94]: https://github.com/aliromman/math/pull/94
[note-98]: conjectures/WeinbergerShayevitz/README.md
[proof-98]: conjectures/WeinbergerShayevitz/Solution.lean
[pr-98]: https://github.com/aliromman/math/pull/98
[note-43]: conjectures/ChauveHistoryGrowth/README.md
[proof-43]: conjectures/ChauveHistoryGrowth/Solution.lean
[pr-43]: https://github.com/aliromman/math/pull/43
[note-80]: conjectures/LuckySpots/README.md
[proof-80]: conjectures/LuckySpots/Solution.lean
[pr-80]: https://github.com/aliromman/math/pull/80
[note-72]: conjectures/ConsecutiveThreshold/README.md
[proof-72]: conjectures/ConsecutiveThreshold/Solution.lean
[pr-72]: https://github.com/aliromman/math/pull/72
[note-59]: conjectures/CFPLogDensity/README.md
[proof-59]: conjectures/CFPLogDensity/Solution.lean
[pr-59]: https://github.com/aliromman/math/pull/59
[note-28]: conjectures/BajnokRestrictedInverse/README.md
[proof-28]: conjectures/BajnokRestrictedInverse/Solution.lean
[pr-28]: https://github.com/aliromman/math/pull/28
[note-17]: conjectures/LayeredWordPacking/README.md
[proof-17]: conjectures/LayeredWordPacking/Proof.lean
[pr-17]: https://github.com/aliromman/math/pull/17
[note-66]: conjectures/MissingSumFringes/First/README.md
[proof-66]: conjectures/MissingSumFringes/First/Solution.lean
[pr-66]: https://github.com/aliromman/math/pull/66
[note-67]: conjectures/MissingSumFringes/Longest/README.md
[proof-67]: conjectures/MissingSumFringes/Longest/Solution.lean
[pr-67]: https://github.com/aliromman/math/pull/67
[note-61]: conjectures/SidonSetSystems/README.md
[proof-61]: conjectures/SidonSetSystems/Solution.lean
[pr-61]: https://github.com/aliromman/math/pull/61
[note-68]: conjectures/WheelMatchings/README.md
[proof-68]: conjectures/WheelMatchings/Solution.lean
[pr-68]: https://github.com/aliromman/math/pull/68
[note-89]: conjectures/MaTangCarousel/README.md
[proof-89]: conjectures/MaTangCarousel/Solution.lean
[pr-89]: https://github.com/aliromman/math/pull/89
[note-95]: conjectures/SavchenkoSix/README.md
[proof-95]: conjectures/SavchenkoSix/Solution.lean
[pr-95]: https://github.com/aliromman/math/pull/95
[note-76]: conjectures/WangLocalDensity/README.md
[proof-76]: conjectures/WangLocalDensity/Solution.lean
[pr-76]: https://github.com/aliromman/math/pull/76
[note-87]: conjectures/Hypertriangulations/README.md
[proof-87]: conjectures/Hypertriangulations/Solution.lean
[pr-87]: https://github.com/aliromman/math/pull/87

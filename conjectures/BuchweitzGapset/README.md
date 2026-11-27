# Solution to Questions 4.1 and 4.2 of Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio on Buchweitz sets

Let $G$ consist of the integers from 1 through 35 and the six gaps $42,46,65,66,70,71$. Its complement in the nonnegative integers is a numerical semigroup. Its least positive element is 36, so the sum of two positive elements exceeds the largest gap, 71.

For $n\ge2$, the Buchweitz obstruction occurs when the sumset $nG$ of $n$ gaps has more than $(2n-1)(|G|-1)$ elements. Buchweitz proved that this rules out a Weierstrass semigroup. Eliahou, García-García, Marín-Aragón and Vigneron-Tenorio asked in Question 4.1 whether the obstruction orders always form an interval, even for an arbitrary finite set of integers. They also asked the question specifically for numerical semigroups. The same gapset answers both versions. [Original paper, §§1 and 4](https://arxiv.org/pdf/2011.09187) · [Published article](https://doi.org/10.1007/s00574-022-00322-8)

| Order $n$ | Size of the sumset | Buchweitz bound | Excess |
| --- | ---: | ---: | ---: |
| 2 | 121 | 120 | 1 |
| 3 | 200 | 200 | 0 |
| 4 | 281 | 280 | 1 |

The strict inequality fails exactly between two orders where it holds. For $n\ge5$, all sums lie between $n$ and $71n$, so $|nG|\le70n+1\le 40(2n-1)$. Thus the full Buchweitz set is $\{2,4\}$. The excesses $1,0,1$ also contradict the proposed unimodality in the authors’ Question 4.2.

## Checking the counts

Reflect the gaps about $71/2$. The resulting set is $[36,70]\cup P$, where $P=\{0,1,5,6,25,29\}$. Reflection preserves each sumset size. For $n=2,3,4$, the sums containing an entry from $[36,70]$ fill $[36,70n]$. Indeed, $[36,70]$ and $[72,140]$ miss only 71 between them, and $71=70+1$. Further copies of $[36,70]$ then give overlapping intervals. The sums below 36 come entirely from $P$ and have sizes 16, 25 and 36. This gives the three counts in the table.

A 2024 presentation by Marín-Aragón restated the interval question for gapsets. Pontes also listed it as open in her 2024 thesis. Searches for the Buchweitz interval question, disconnected Buchweitz sets, and subsequent work on the original paper found no earlier counterexample. OpenAI Codex derived the construction from the small summands of a reflected gapset and wrote the proof. [2024 presentation](https://imns2024.uca.es/wp-content/uploads/2024/07/Marin_Aragon_Jerez_24.pdf#page=19) · [Pontes, conclusion](https://repositorio.ufjf.br/jspui/bitstream/ufjf/17346/1/letiannealvesvenanciodepontes.pdf)

A UFMT project register also lists a November 2025 presentation on computational tests of the Buchweitz condition. The register gives its title. We could not inspect its proceedings contribution. [UFMT project register](https://sistemas.ufmt.br/sgpp/Publico/Detalhe/15300)

```sh
# Run at the merge commit for PR #24.
python3 scripts/verify.py --base HEAD^ --fetch-cache
```

Shalom Eliahou, Juan Ignacio García-García, Daniel Marín-Aragón and Alberto Vigneron-Tenorio, “The Buchweitz Set of a Numerical Semigroup,” Bulletin of the Brazilian Mathematical Society, New Series 54 (2023), article 4, Questions 4.1 and 4.2, DOI 10.1007/s00574-022-00322-8. [Publication](https://link.springer.com/article/10.1007/s00574-022-00322-8)

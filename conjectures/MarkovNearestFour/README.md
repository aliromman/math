# The first lattice point above the Markov edge has coefficient four

For every reduced slope $1<a<b$, the Markov numerator has coefficient exactly $4$ at the unique lattice point $(i,j)$ with $bi+aj=ab+1$. This proves the Location of 4 conjecture of Evans, Veselov and Winn. For example, at slope $13/18$ the point is $(8,7)$, since $18\cdot8+13\cdot7=235=13\cdot18+1$. [Original paper, Conjecture 8.4 and Example 8.5](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html)

The homogeneous numerator $P_{a/b}(u,v,w)$ has a Newton polygon with an edge on $bi+aj=ab$. The authors predict the value $4$ at a particular vertex of the sail inside its critical triangle. If $p/q$ is the penultimate convergent of $b/a$, their point is $(q,b-p)$ for even continued-fraction length and $(a-q,p)$ for odd length. The determinant identity $bq-ap=\pm1$ puts either point on $bi+aj=ab+1$. This line has only one nonnegative lattice point. Any solution satisfies $i<a$ and $j<b$, and reduction modulo $a$ determines $i$. The source excludes the empty sail at $a=1$. [Equations (7), (11), (32) and §§8–9](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html)

## Proof

Substitute $u=z^b$, $v=z^a$ and $w=1$. For each Farey vector $p=(c,d)$ on the path to $(a,b)$, write $F_p=P_{c/d}(z^b,z^a,1)$, $w_p=bc+ad$ and $h_p=|bc-ad|$. Remove the factor $z^{(w_p-h_p)/2}$ from $F_p$. We claim that the first two coefficients of the resulting series are

| Distance $h_p$ | Constant | Coefficient of $z$ |
| --- | ---: | ---: |
| $h_p>1$ | $1$ | $0$ |
| $h_p=1$ | $1$ | $1$ |
| $h_p=0$ | $2$ | $4$ |

The initial fractions $0/1$, $1/0$ and $1/1$ give the normalized series $1$, $1$ and $1+z^{b-a}$. Consider a Farey step that retains $p$, drops $q$, and forms the new center $2p+q$ from $r=p+q$. The Markov exchange gives

$$
F_qF_{2p+q}=z^{w_q}F_p^2+F_r^2.
$$

Write $d=h_p$ and $e=h_r$. The subtractive Euclidean algorithm gives $h_q=d+e$ and $h_{2p+q}=|d-e|$. Since $d,e>0$, the normalized $F_q$ is $1+O(z^2)$. Divide both sides by their lowest power of $z$. The normalized right side is $A^2+z^{|d-e|}B^2$, where $A$ comes from the larger of $d,e$ and $B$ from the smaller. If $d\ne e$, the larger distance is at least two, so $A$ starts with $1+O(z^2)$. The new coefficient of $z$ is one exactly when $|d-e|=1$. If $d=e$, coprimality forces $d=e=1$. Both squares then start with $1+2z$, so their sum starts with $2+4z$. This proves the table by induction.

At the target $h=0$ and the removed factor is $z^{ab}$. The coefficient of $z^{ab+1}$ is therefore four. The uniqueness of $(i,j)$ identifies it with the required coefficient of the homogeneous numerator.

## Prior work and verification

Evans, Veselov and Winn proved the result at every Pell slope $n/(n+1)$ in Theorem 9.1. A later saturation theorem of Evans proves that every lattice point in the Newton polygon occurs with positive coefficient. Searches for the location conjecture, Markov sails, and formulas for their coefficients found no previous proof of this exact value for every reduced slope. OpenAI Codex developed the proof and Lean formalization. [Pell family, §9](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html) · [Saturation theorem](https://arxiv.org/abs/2604.18333)

[Statement](Statement.lean) · [Euclidean induction](Walk.lean) · [Coefficient extraction](Coefficient.lean) · [Final theorem and axiom check](Solution.lean)

~~~sh
lake exe cache get
lake build conjectures.MarkovNearestFour.Solution
lake env leanchecker conjectures.MarkovNearestFour.Solution
~~~

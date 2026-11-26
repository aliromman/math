# Four divides every coefficient inside the critical triangle

For every Markov polynomial, each coefficient strictly inside its critical triangle is a multiple of four. This proves Conjecture 8.1 of Evans, Veselov and Winn. Four is sharp. At slope $2/3$, the coefficient of $uv^2w$ is exactly $4$. [Original paper, §§3 and 8](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html)

The Markov polynomials are Laurent polynomials obtained from $(x,y,z)$ by repeatedly replacing one entry $Z$ by $(X^2+Y^2)/Z$. The positive rational slopes $a/b$ index their numerators $P_{a/b}(u,v,w)$, with $u=x^2$, $v=y^2$ and $w=z^2$. These numerators are homogeneous of degree $a+b-1$. Write $A_{ij}$ for the coefficient of $u^iv^jw^{a+b-1-i-j}$. The critical triangle consists of the integer points with $i<a$, $j<b$ and $bi+aj>ab$. [Definitions and Newton polygons, equations (7)–(11)](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html)

## Proof

Set $w=1$. Homogeneity preserves the coefficient $A_{ij}$ at $u^iv^j$. We prove that every term in the rectangle $i<a$, $j<b$ vanishes modulo four. Equivalently, we must prove $P_{a/b}=0$ in the ring

$$
R=(\mathbb Z/4\mathbb Z)[u,v]/(u^a,v^b).
$$

Write $L=1+u+v$ and $T_{c,d}=L P_{c/d}$. The numerator recurrence in equation (8) of the paper gives, for adjacent Farey vectors $p=(i,j)$ and $q$,

$$
T_{2p+q}=T_pT_{p+q}-u^iv^jT_q.
$$

Choose nilpotent $s,t$ in $R$ with $s(L-s)=u$ and $t(L-t)=v$. Such roots exist by lifting the root $0$ of each quadratic modulo the nilpotent ideal $(u,v)$. The derivative at $0$ is a unit. Since $L-s$ and $L-t$ are units, $s$ is a multiple of $u$ and $t$ is a multiple of $v$.

In $R$, the trace at every slope satisfies

$$
T_{c,d}=s^c(L-t)^d+(L-s)^c t^d.
$$

The right side satisfies the same recurrence by multiplication. At $(1,0)$ and $(0,1)$ it is $L$. At $(1,1)$ it must equal $L(u+v)$. To check this last value, put $\delta=L-1-s-t$. The two root equations give $(1-s-t)\delta=2st$. The factor $1-s-t$ is a unit, so $\delta$ is a multiple of two. The difference between the initial traces is

$$
L(u+v)-s(L-t)-(L-s)t=\delta(2+\delta)=0
$$

in $R$. Induction on the Farey tree now proves the expression for every positive reduced slope. At $(a,b)$ its two terms vanish because $s^a=t^b=0$. The factor $L$ is a unit, so $P_{a/b}=0$ in $R$.

## Prior work and verification

Evans, Veselov and Winn computed the first Pell sail and identified its coefficient $4$. A subsequent proof established the divisibility in the full Pell family $a/b=n/(n+1)$. Searches for the conjecture, the critical triangle, and coefficient congruences found no earlier proof for all slopes. OpenAI Codex developed the general argument and its Lean formalization. [Evans–Veselov–Winn, §9](https://amj.math.stonybrook.edu/Articles/250708-Winn/index.html) · [Pell-family proof](https://github.com/xzwwwwww/math/blob/93f15f5e04e25384d5eb3661bbfe53bac850f25f/Pell%E7%8C%9C%E6%83%B3/markov_pell_factor_four.pdf)

The formal proof verifies the Euclidean path to every reduced slope, the trace identity, and the integer coefficient statement. [Statement](Statement.lean) · [Trace identity](Characters.lean) · [Proof and axiom check](Solution.lean)

~~~sh
lake exe cache get
lake build conjectures.MarkovFactorFour.Solution
lake env leanchecker conjectures.MarkovFactorFour.Solution
~~~

# A counterexample to MAIS-O71

A Lean-verified counterexample refutes MAIS-O71 as stated: for a one-input, three-hidden-unit ReLU network with zero true regression function and a uniform prior on a closed Euclidean parameter ball, the sublevel-volume law has the unique pair $(\lambda,m)=(11/6,1)$, while $F\_n-nS\_n-(11/6)\log n$ tends to minus infinity in probability.

The question asks whether the same pair of exponents controls two quantities. The first is the prior mass of parameters with small population loss. The second is the cost of learning from a sample, measured by the free energy above the empirical entropy. For the volume pair found here, the conjecture predicts that subtracting $(11/6)\log n$ from the second quantity leaves a tight remainder. The checked proof shows that the remainder escapes below every fixed threshold. [Problem statement](https://github.com/Math-for-AI-Safety/MAIS/blob/1cb9f003d111ca6de056b18ee574204314c00b8e/open-problems/MAIS-O71.md) · [Agenda, Question 9.2](https://github.com/Math-for-AI-Safety/MAIS/blob/1cb9f003d111ca6de056b18ee574204314c00b8e/agendas/A6/MAIS-A6.tex#L545-L560)

## Model and theorem

Write $u\_+=\max(u,0)$. The network is $f\_w(x)=c+\sum\_{j=1}^3 v\_j(a\_j x+b\_j)\_+$. At the true parameter $w^0$, the bias $c$ is zero and each triple $(a\_j,b\_j,v\_j)$ equals $(1,0,0)$. The prior $\pi$ is uniform on the closed Euclidean ball $W$ of radius $1/3$ centered at $w^0$ in $\mathbb R^{10}$. The data are iid with $X$ uniform on $[-1,1]$ and $Y\mid X\sim N(0,1)$. A model parameter $w$ assigns $Y\mid X=x$ the law $N(f\_w(x),1)$.

Let $p\_w$ denote this conditional density. The loss is $K(w)=\frac14\int\_{-1}^1 f\_w(x)^2\\,dx$. The free energy and empirical entropy are

$$
F\_n=-\log\int\_W\prod\_{i=1}^n p\_w(Y\_i\mid X\_i)\\,d\pi(w),
\qquad
S\_n=-\frac1n\sum\_{i=1}^n\log p\_{w^0}(Y\_i\mid X\_i).
$$

For some $c\_0>0$, the prior mass $\pi\\{K\le\varepsilon\\}$ is asymptotic to $c\_0\varepsilon^{11/6}$ as $\varepsilon\downarrow0$. The proposed free-energy expansion at the unique volume pair would make $R\_n=F\_n-nS\_n-\frac{11}{6}\log n$ bounded in probability. Lean proves that $R\_n+\frac13\log\log n$ is bounded **above** in probability. In particular, $\Pr(R\_n\ge T)\to0$ for every fixed real $T$.

## Main Lean declarations

Import `O71`. All declarations below are in the `O71` namespace.

| Declaration | Statement |
| --- | --- |
| [`theorem_A`](TheoremA.lean) | The Lebesgue volume of the loss sublevel in the ball, divided by $\varepsilon^{11/6}$, has a finite positive limit. |
| [`display_one_unique`](Display.lean) | A positive power–log volume asymptotic forces $\lambda=11/6$ and $m=1$. Normalizing by the fixed ball volume preserves the pair. |
| [`freeEnergy_upper`](Conclusion.lean) | $R\_n+\frac13\log\log n$ is bounded above in probability. |
| [`freeEnergy_diverges_to_neg_inf`](Conclusion.lean) | $\Pr(R\_n\ge T)\to0$ for every real $T$. |
| [`centered_freeEnergy_not_tight`](Conclusion.lean) | The remainder $R\_n$ is not tight. |
| [`mais_o71_refutation_integer`](Conclusion.lean) | No shared triple $\lambda>0$, integer $m\ge1$, $c\_0>0$ satisfies both displays. |

## Paper results

The paper proof supplies the matching **upper bound on the evidence** for the same three-unit instance. Combined with the formalized lower bound on the evidence, it gives the two-sided expansion

$$
F\_n=nS\_n+\frac{11}{6}\log n-\frac13\log\log n+O\_p(1).
$$

For every fixed $H\ge3$, the paper also treats the one-input, zero-truth family with all $H$ triples centered at $(1,0,0)$ and the same ball radius and uniform prior. It gives $\lambda=(2H+5)/6$, $m\_{\mathrm{vol}}=1$, and

$$
F\_n=nS\_n+\frac{2H+5}{6}\log n-\frac{H-2}{3}\log\log n+O\_p(1).
$$

Both exact expansions are paper results. The machine-checked counterexample uses only the volume asymptotic and the one-sided probability bound at $H=3$.

## Build and axioms

With elan installed, run the following command from the project root. The toolchain and dependency manifest pin Lean and Mathlib to the versions used for the proof.

```sh
lake exe cache get && lake build
```

The build prints the transitive axiom dependencies of the main theorems. Each uses `propext`, `Classical.choice` and `Quot.sound`. To repeat the axiom check after building, run `lake env lean TheoremA.lean`, `lake env lean Display.lean` and `lake env lean Conclusion.lean`.

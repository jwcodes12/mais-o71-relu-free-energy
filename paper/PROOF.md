# A counterexample to MAIS-O71 for continuous-input ReLU networks

For one input and three hidden units, the sublevel volume has exponent $11/6$ and multiplicity one. At the same parameter and with the same prior, the free energy contains the additional term $-\tfrac13\log\log n$. Thus the leading coefficient agrees in the two asymptotics, but the multiplicity prescribed by the volume gives an incorrect second-order prediction. For each fixed width $H\ge3$ on the zero-truth interior balls defined below, the coefficient of $\log\log n$ is $-(H-2)/3$.

**Claim labels.** (iii) denotes a proved statement and (iv) denotes a conjecture.

**Machine-checked scope.** In the accompanying Lean project, Theorem A at $r=1,H=3$ is `O71.theorem_A` for Lebesgue volume, with `O71.uniform_prior_asymptotic` and `O71.display_one_unique` for normalization and uniqueness. The evidence lower bound of Theorem B is `O71.theorem_B`, with its free-energy form in `O71.freeEnergy_upper`. The escape below every fixed threshold, failure of tightness and paired refutation in Corollary 1 are `O71.freeEnergy_diverges_to_neg_inf`, `O71.centered_freeEnergy_not_tight` and `O71.mais_o71_refutation_integer`. Theorem C, Corollary 2 and the extensions in Theorems D–F have paper proofs. Theorem C supplies the second inequality needed for the exact three-unit expansion.

**Conjectures.** Section 8 lists the open cases involving boundary and dead units, general active truths and higher input dimensions.

## 0. Problem Statement, Setup, and Main Results

### 0.1 The paired asymptotic question

Fix integers $r, H \ge 1$ and the single-hidden-layer ReLU regression network
$$f_w(x) \;=\; c + \sum_{j=1}^{H} v_j \max(a_j \cdot x + b_j,\; 0), \qquad x \in [-1,1]^r,$$
with parameter $w = \bigl(c, (a_j, b_j, v_j)_{j=1}^H\bigr) \in \mathbb{R}^{1 + H(r+2)}$. Inputs $X_1, \dots, X_n$ are i.i.d. $\mathrm{Unif}([-1,1]^r)$, outputs follow $Y_i \mid X_i \sim \mathcal{N}(f_{w^0}(X_i), 1)$ for a fixed true parameter $w^0$, and the model conditional density is $p(y \mid x, w) = (2\pi)^{-1/2} \exp\!\bigl(-\frac{1}{2}(y - f_w(x))^2\bigr)$. Let $W \subset \mathbb{R}^{1 + H(r+2)}$ be a compact semialgebraic parameter domain containing $w^0$ (closure of its interior, per MAIS-A6 Remark 1.1), let $\varphi$ be a $C^\infty$ strictly positive probability density on $W$, and assume the population Kullback–Leibler divergence
$$K(w) \;=\; \frac{1}{2}\,\mathbb{E}_{X \sim \mathrm{Unif}([-1,1]^r)}\!\bigl[\bigl(f_w(X) - f_{w^0}(X)\bigr)^2\bigr]$$
is not identically zero on $W$. Let $F_n := -\log \int_W \prod_{i=1}^n p(Y_i \mid X_i, w)\,\varphi(w)\,dw$ be the Bayesian free energy and $S_n := -\frac{1}{n}\sum_{i=1}^n \log p(Y_i \mid X_i, w^0)$ the empirical entropy of the truth.

MAIS-O71 asks to prove that there exist $\lambda > 0$, an integer $m \ge 1$, and a constant $c_0 > 0$ such that
$$\tag{Display 1}\int_{\{K \le \varepsilon\} \cap W} \varphi(w)\,dw \;=\; c_0\,\varepsilon^{\lambda}\bigl(\log(1/\varepsilon)\bigr)^{m-1}(1 + o(1)) \qquad (\varepsilon \downarrow 0)$$
and
$$\tag{Display 2}F_n \;=\; n S_n + \lambda \log n - (m - 1)\log\log n + O_p(1) \qquad (n \to \infty).$$

Both displays must hold with the same $\lambda$ and $m$. [Problem statement](https://github.com/Math-for-AI-Safety/MAIS/blob/1cb9f003d111ca6de056b18ee574204314c00b8e/open-problems/MAIS-O71.md)

### 0.2 Notation and Exact Evidence Representation

Write $Y_i = f_{w^0}(X_i) + \varepsilon_i$, where $\varepsilon_1, \dots, \varepsilon_n \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$ are independent of $X^n = (X_1, \dots, X_n)$. Setting $\Delta_w(x) := f_w(x) - f_{w^0}(x)$, a direct algebraic cancellation of $\frac{1}{2}\sum_{i=1}^n \varepsilon_i^2$ and $\frac{n}{2}\log(2\pi)$ gives the exact identity
$$F_n - n S_n \;=\; -\log Z_n, \qquad Z_n \;:=\; \int_W \exp\!\left(\langle \varepsilon, \Delta_w\rangle_n - \frac{1}{2}\|\Delta_w\|_n^2\right) \varphi(w)\,dw,$$
where for any functions $g, h : [-1, 1] \to \mathbb{R}$ we write
$$\langle \varepsilon, g\rangle_n \;:=\; \sum_{i=1}^n \varepsilon_i g(X_i), \qquad \langle g, h\rangle_n \;:=\; \sum_{i=1}^n g(X_i) h(X_i), \qquad \|g\|_n^2 \;:=\; \sum_{i=1}^n g(X_i)^2.$$
For an interval $I \subset [-1, 1]$, we write $N(I) := \#\{i \in \{1, \dots, n\} : X_i \in I\}$. Throughout, $r = 1$, so $X_i \stackrel{\text{i.i.d.}}{\sim} \mathrm{Unif}[-1, 1]$ with density $\frac{1}{2}$ on $[-1, 1]$, and $K(w) = \frac{1}{4}\int_{-1}^{1} \Delta_w(x)^2 dx$.

For a closed Euclidean ball $W = \overline{B_R(w^0)} := \{w \in \mathbb{R}^{3H+1} : \|w - w^0\|_2 \le R\}$ ($R > 0$) and the uniform prior $\varphi(w) \equiv 1/\mathrm{vol}(W)$, all hypotheses of MAIS-O71 (and MAIS-A6 Remark 1.1) are satisfied: $W$ is compact, semialgebraic (defined by $\|w - w^0\|_2^2 \le R^2$), the closure of its interior, and contains $w^0$; $\varphi$ is smooth and strictly positive on $W$; and $K \not\equiv 0$ on $W$ (e.g., shifting $c$ by $R$ gives $K = R^2/2 > 0$).

### 0.3 Summary of Theorems Proved in This Document

| Result | Setting ($r = 1$) | Proved Statement | Label |
|---|---|---|---|
| **Theorem A** (§2) | $H = 3$, $w^0 = (0,(1,0,0)^3)$, $W = \overline{B_{1/3}(w^0)}$ | Display 1 holds with $\int_{\{K \le \varepsilon\} \cap W} \varphi\,dw = c_0\,\varepsilon^{11/6}(1+o(1))$, $0 < c_0 < \infty$; uniquely $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = (\frac{11}{6}, 1)$. | **(iii)** Machine-checked |
| **Theorem B** (§3) | Same ($H = 3$) | Part I (evidence lower bound): $F_n - n S_n \le \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$. | **(iii)** Machine-checked |
| **Corollary 1** (§3) | Same ($H = 3$) | **MAIS-O71 is false** (uses only Theorems A and B). | **(iii)** Machine-checked |
| **Theorem C** (§4) | Same ($H = 3$) | Part II (evidence upper bound): $F_n - n S_n \ge \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$. | **(iii)** Paper |
| **Corollary 2** (§4) | Same ($H = 3$) | Exact expansion $F_n = n S_n + \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$; **no pair $(\lambda', m') \in \mathbb{R} \times \mathbb{Z}$ satisfies Display 2 alone.** | **(iii)** Paper |
| **Theorem D** (§5) | **Every $H \ge 3$**, $w^0 = (0,(1,0,0)^H)$, $W = \overline{B_{1/3}(w^0)}$ | General-$H$ law: Display 1 holds with $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = (\frac{2H+5}{6}, 1)$ and the free energy satisfies $F_n = n S_n + \frac{2H+5}{6}\log n - \frac{H-2}{3}\log\log n + O_p(1)$. Hence MAIS-O71 fails on these balls at every $H \ge 3$, and no integer $m'$ works whenever $H \not\equiv 2 \pmod 3$. | **(iii)** Paper |
| **Theorem E** (§6) | **Active truth $H = 4$**, $f_{w^0}(x) = (x + \frac{1}{2})_+$, $W = \overline{B_{1/10}(w^0)}$ | Display 1 holds with $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = (\frac{17}{6}, 1)$ and $F_n = n S_n + \frac{17}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$ (both bounds proved). | **(iii)** Paper |
| **Theorem F** (§7) | **Positive cases $H = 1, 2$**, $w^0 = (0,(1,0,0)^H)$, $W = \overline{B_{1/3}(w^0)}$ | Both Displays 1 and 2 hold with $(\lambda, m) = (1, 1)$ at $H = 1$ and $(\lambda, m) = (\frac{3}{2}, 2)$ at $H = 2$, establishing $H = 3$ as the exact threshold on the interior balls $\overline{B_{1/3}(w^0)}$. | **(iii)** Paper |
| **Conjectures** (§8) | Boundary/dead-cone $H=1,2$ domains; general active truths; $r \ge 2$ | Extensions beyond the proved instances above. | **(iv)** |

### 0.4 Related work

Hartigan and Bickel–Chernoff studied the likelihood-ratio test for normal mixtures. Liu–Shao obtained its asymptotics in a two-component model, and Azaïs–Gassiat–Mercadier analyzed how the parameter domain affects mixture likelihood ratios. For multilayer networks with surplus units, Fukumizu (2003) obtained a logarithmic lower bound on the maximized log likelihood ratio under his assumptions. These results concern maximization over weakly identified directions. [Fukumizu](https://www.ism.ac.jp/~fukumizu/fuku_AS_W01_025.pdf) · [Azaïs–Gassiat–Mercadier](https://doi.org/10.3150/bj/1161614946)

Dümbgen–Spokoiny (2001, Lemma 6.2 and §6.3) placed disjoint triangular bumps of half-width $h\asymp(\log n/n)^{1/3}$ in Gaussian white noise. Each bump has squared signal strength of order $nh^3$. Below the detection threshold the average of their likelihood ratios converges to one in $L^1$. Chan–Walther (2013) used the truncated Gaussian moment in the proof of their Theorem 2 for an average likelihood ratio over intervals. Burnaev–Golubev (2017, Theorem 3) showed that the amplitude-integrated statistic $N^{-1}\sum_{j=1}^N e^{Z_j^2/2}$ for independent standard normal channels is asymptotic in probability to $(2/\sqrt{\pi})\sqrt{\log N}$ in their diffuse-amplitude limit. [Dümbgen–Spokoiny](https://doi.org/10.1214/aos/996986504) · [Chan–Walther](https://arxiv.org/abs/1107.4344) · [Burnaev–Golubev](https://arxiv.org/abs/1712.06335)

Watanabe's analytic theory pairs volume and free energy under regularity assumptions on the statistical family. Nagayasu–Watanabe derived upper bounds on expected free energy for overparameterized deep ReLU networks. Here the prior integrates over tent widths as well as over their locations and shapes inside a fixed compact parameter ball. The contribution is the refutation of the paired MAIS-O71 claim and the coefficient $-(H-2)/3$ for this ReLU family. The likelihood-ratio averaging and truncation arguments have the precedents above. [Nagayasu–Watanabe](https://arxiv.org/abs/2303.15739)

---

## 1. Standard Theorems Invoked and Shared Elementary Lemmas

### 1.1 Standard Theorems Cited

The proofs use the following integration and probability inequalities.

1. **Tonelli's Theorem.** If $(X, \mathcal{A}, \mu)$ and $(Y, \mathcal{B}, \nu)$ are $\sigma$-finite measure spaces and $f : X \times Y \to [0, \infty]$ is jointly measurable, then $\iint f\,d(\mu \times \nu) = \int_X (\int_Y f(x, y)\,d\nu(y))\,d\mu(x) = \int_Y (\int_X f(x, y)\,d\mu(x))\,d\nu(y)$.
2. **Lebesgue's Dominated Convergence Theorem (DCT).** Let $(f_\varepsilon)_{\varepsilon > 0}$ be measurable functions on a measure space $(X, \mathcal{A}, \mu)$ converging $\mu$-a.e. to $f$ as $\varepsilon \downarrow 0$. If there exists $g \in L^1(\mu)$ such that $|f_\varepsilon| \le g$ $\mu$-a.e. for all $\varepsilon > 0$, then $\lim_{\varepsilon \downarrow 0} \int_X f_\varepsilon\,d\mu = \int_X f\,d\mu$.
3. **Change of Variables Formula in $\mathbb{R}^d$.** If $\Phi : U \to V$ is a $C^1$ diffeomorphism between open subsets of $\mathbb{R}^d$ and $f : V \to [0, \infty]$ is measurable, then $\int_V f(y)\,dy = \int_U f(\Phi(u))\,|\det D\Phi(u)|\,du$.
4. **Hoeffding's Inequality (1963).** If $Z_1, \dots, Z_n$ are independent random variables with $Z_i \in [a_i, b_i]$ almost surely and $S = \sum_{i=1}^n (Z_i - \mathbb{E}[Z_i])$, then for every $t > 0$,
   $$\mathbb{P}(S \ge t) \le \exp\!\left(-\frac{2 t^2}{\sum_{i=1}^n (b_i - a_i)^2}\right), \qquad \mathbb{P}(S \le -t) \le \exp\!\left(-\frac{2 t^2}{\sum_{i=1}^n (b_i - a_i)^2}\right).$$
5. **Multiplicative Chernoff Bound.** If $N \sim \mathrm{Bin}(n, p)$ with mean $\mu = np > 0$, then for every $\delta \in (0, 1]$,
   $$\mathbb{P}(N < (1 - \delta)\mu) \le \exp\!\left(-\frac{\delta^2 \mu}{2}\right), \qquad \mathbb{P}(N > (1 + \delta)\mu) \le \exp\!\left(-\frac{\delta^2 \mu}{3}\right).$$
   In particular, $\mathbb{P}(N < \frac{1}{2}\mu) \le e^{-\mu/8}$ and $\mathbb{P}(N > 2\mu) \le e^{-\mu/3}$.
6. **Lévy's Maximal Inequality (1937).** If $\tilde{\varepsilon}_1, \dots, \tilde{\varepsilon}_n$ are independent symmetric real random variables and $S_k := \sum_{j=1}^k \tilde{\varepsilon}_j$, then for every $\lambda > 0$,
   $$\mathbb{P}\!\left(\max_{1 \le k \le n} S_k \ge \lambda\right) \le 2\,\mathbb{P}(S_n \ge \lambda), \qquad \mathbb{P}\!\left(\max_{1 \le k \le n} |S_k| \ge \lambda\right) \le 4\,\mathbb{P}(S_n \ge \lambda).$$
   *(Self-contained 4-line proof: let $\tau := \min\{k : S_k \ge \lambda\}$ on $A := \{\max_{1\le k\le n} S_k \ge \lambda\}$. On $\{\tau = k\}$, $S_n - S_k$ is independent of $(\tilde{\varepsilon}_1, \dots, \tilde{\varepsilon}_k)$ and symmetric, so $\mathbb{P}(S_n \ge \lambda \mid \tau = k) \ge \mathbb{P}(S_n - S_k \ge 0 \mid \tau = k) \ge \frac{1}{2}$. Summing over $k = 1, \dots, n$ yields $\mathbb{P}(S_n \ge \lambda) \ge \frac{1}{2}\mathbb{P}(A)$. Applying the same bound to $-\tilde{\varepsilon}_j$ and taking a union bound gives the second inequality.)*
   When $\tilde{\varepsilon}_j \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$, the Gaussian Chernoff bound $\mathbb{P}(S_n \ge \lambda) \le e^{-\lambda^2/(2n)}$ yields
   $$\mathbb{P}\!\left(\max_{1 \le k \le n} |S_k| \ge \lambda\right) \le 4 \exp\!\left(-\frac{\lambda^2}{2n}\right).$$
7. **Markov's and Chebyshev's Inequalities.** For $X \ge 0$ and $t > 0$, $\mathbb{P}(X \ge t) \le \mathbb{E}[X]/t$. For $Y \in L^2$ and $t > 0$, $\mathbb{P}(|Y - \mathbb{E}[Y]| \ge t) \le \mathrm{Var}(Y)/t^2$.
8. **Exact Gaussian Identities.**
   - If $Z \sim \mathcal{N}(0, \sigma^2)$ ($\sigma \ge 0$) and $a \in \mathbb{R}$, then $\mathbb{E}[\exp(a Z - \frac{1}{2}a^2 \sigma^2)] = 1$.
   - If $G \in \mathbb{R}^{q \times q}$ is symmetric positive definite and $U \in \mathbb{R}^q$, then
     $$\int_{\mathbb{R}^q} \exp\!\left(\theta^\top U - \frac{1}{2}\theta^\top G \theta\right) d\theta \;=\; \frac{(2\pi)^{q/2}}{\sqrt{\det G}}\,\exp\!\left(\frac{1}{2} U^\top G^{-1} U\right).$$
   - If $Z \sim \mathcal{N}(0, I_q)$ and $A > 0$, then with $\omega_q := \mathrm{vol}(\{z \in \mathbb{R}^q : \|z\|_2 \le 1\}) = \pi^{q/2}/\Gamma(\frac{q}{2}+1)$ (in particular $\omega_1 = 2$),
     $$\mathbb{E}\!\left[\exp\!\left(\frac{1}{2}\|Z\|_2^2\right)\mathbf{1}_{\{\|Z\|_2 \le A\}}\right] \;=\; (2\pi)^{-q/2}\int_{\|z\|_2 \le A} e^{-\|z\|_2^2/2}\,e^{\|z\|_2^2/2}\,dz \;=\; \frac{\omega_q A^q}{(2\pi)^{q/2}}.$$

---

### 1.2 Shared Algebraic and Analytic Lemmas

**Lemma 1.1 (Exact Macroscopic–Bump Decomposition, Jacobian, and Slope Bound for All $H \ge 3$).**
Fix $H \ge 3$, $w^0 = (0, (1, 0, 0)^H) \in \mathbb{R}^{3H+1}$, and $W = \overline{B_{1/3}(w^0)}$.
1. *(Interior knots)* Every $w \in W$ satisfies $a_j \in [\frac{2}{3}, \frac{4}{3}]$, $|b_j| \le \frac{1}{3}$, $|v_j| \le \frac{1}{3}$, and $|s_j| \le \frac{4}{9}$ for all $j = 1, \dots, H$, where $t_j := -b_j/a_j \in [-\frac{1}{2}, \frac{1}{2}]$ and $s_j := a_j v_j$. Moreover, $f_w(x) = c + \sum_{j=1}^H s_j (x - t_j)_+$ for all $x \in [-1, 1]$, and for fixed $a = (a_1, \dots, a_H) \in (0, \infty)^H$, the map $(b_j, v_j)_{j=1}^H \mapsto (t_j, s_j)_{j=1}^H$ is a $C^\infty$ diffeomorphism with Jacobian $|\det \frac{\partial(b, v)}{\partial(t, s)}| = \prod_{j=1}^H |-a_j \cdot a_j^{-1}| = 1$.
2. *(Exact decomposition on the ordered sector)* On the open sector $\Omega_< := \{t_1 < t_2 < \cdots < t_H\}$, set $\delta_j := t_{j+1} - t_j > 0$ ($j = 1, \dots, H-1$) and $\Delta := t_H - t_1 = \sum_{j=1}^{H-1} \delta_j$. Define
   $$S := \sum_{j=1}^H s_j, \qquad B := -\sum_{j=1}^H s_j t_j, \qquad m_0 := \frac{S t_H + B}{\Delta},$$
   the macroscopic function $M(x) := c + S \phi_S(x) + B \phi_B(x)$ where
   $$\phi_B(x) := \begin{cases} 0 & x < t_1, \\ \dfrac{x - t_1}{\Delta} & t_1 \le x \le t_H, \\ 1 & x > t_H, \end{cases} \qquad \phi_S(x) := \begin{cases} 0 & x < t_1, \\ t_H \dfrac{x - t_1}{\Delta} & t_1 \le x \le t_H, \\ x & x > t_H, \end{cases}$$
   and the interior nodal heights $h_k := f_w(t_k) - M(t_k)$ for $k = 2, \dots, H-1$ (with $h_1 := h_H := 0$). Then for every $x \in [-1, 1]$,
   $$f_w(x) \;=\; M(x) + b(x), \qquad b(x) \;:=\; \sum_{k=2}^{H-1} h_k \Lambda_k(x),$$
   where $\Lambda_k(x) := \frac{x - t_{k-1}}{\delta_{k-1}}\mathbf{1}_{[t_{k-1}, t_k]}(x) + \frac{t_{k+1} - x}{\delta_k}\mathbf{1}_{(t_k, t_{k+1}]}(x)$ is the unit hat function supported on $[t_{k-1}, t_{k+1}]$.
3. *(Exact inverse and Jacobian)* For fixed $t_1 < \cdots < t_H$, the linear map $(s_1, \dots, s_H) \mapsto (S, B, h_2, \dots, h_{H-1})$ is invertible with exact inverse
   $$s_1 = \frac{B + S t_H}{\Delta} + \frac{h_2}{\delta_1}, \qquad s_k = \frac{h_{k+1} - h_k}{\delta_k} - \frac{h_k - h_{k-1}}{\delta_{k-1}} \quad (2 \le k \le H-1), \qquad s_H = \frac{-B - S t_1}{\Delta} + \frac{h_{H-1}}{\delta_{H-1}},$$
   and exact Jacobian determinant
   $$\left|\det \frac{\partial(s_1, \dots, s_H)}{\partial(S, B, h_2, \dots, h_{H-1})}\right| \;=\; \frac{1}{\prod_{j=1}^{H-1} \delta_j}.$$
   In particular, for $H = 3$ (writing $\tilde{h} := h_2$, $\tau := \Lambda_2$), we have $\tilde{h} = -s_2 \frac{\delta_1 \delta_2}{\delta_1 + \delta_2}$, $s_2 = -\tilde{h}\frac{\delta_1+\delta_2}{\delta_1\delta_2}$, $s_1 = \frac{B + S t_3}{\delta_1 + \delta_2} + \frac{\tilde{h}}{\delta_1}$, $s_3 = \frac{-B - S t_1}{\delta_1 + \delta_2} + \frac{\tilde{h}}{\delta_2}$, and Jacobian $\frac{1}{\delta_1 \delta_2}$.
4. *(Dirichlet Green's function slope bound)* For every $w \in W \cap \Omega_<$ and every $j \in \{1, \dots, H-1\}$,
   $$|h_{j+1} - h_j| \;\le\; \left(\sum_{k=2}^{H-1} |s_k|\right)\delta_j \;\le\; \frac{4(H-2)}{9}\,\delta_j.$$
   For $H = 3$, the tighter exact relation $|s_2| \le \frac{4}{9}$ directly yields $|\tilde{h}| \le \frac{4}{9}\frac{\delta_1 \delta_2}{\delta_1 + \delta_2} \le \frac{4}{9}\min(\delta_1, \delta_2)$.

*Proof.*
(1) Since $\|w - w^0\|_2 \le \frac{1}{3}$, we have $|a_j - 1| \le \frac{1}{3}$, $|b_j| \le \frac{1}{3}$, and $|v_j| \le \frac{1}{3}$, so $a_j \in [\frac{2}{3}, \frac{4}{3}]$, $|t_j| = |b_j|/a_j \le \frac{1}{2}$, and $|s_j| = a_j|v_j| \le \frac{4}{9}$. Because $a_j > 0$, $v_j \max(a_j x + b_j, 0) = s_j (x - t_j)_+$. The Jacobian of $b_j = -a_j t_j, v_j = s_j / a_j$ at fixed $a_j$ is $\det\mathrm{diag}(-a_j, a_j^{-1}) = -1$.

(2) Both $f_w$ and $M + b$ are continuous and piecewise affine on $[-1, 1]$ with breakpoints contained in $\{t_1, \dots, t_H\}$. It suffices to verify equality at the nodes $\{-1, t_1, \dots, t_H, 1\}$:
- At $x \in \{-1, t_1\}$: $f_w(x) = c = M(x)$ and $b(x) = 0$.
- At $x = t_k$ ($2 \le k \le H-1$): $M(t_k) + b(t_k) = M(t_k) + h_k = f_w(t_k)$ by definition.
- At $x = t_H$: $f_w(t_H) = c + \sum_{j=1}^{H-1} s_j (t_H - t_j) = c + S t_H + B = M(t_H)$ (since $s_H(t_H - t_H) = 0$) and $b(t_H) = 0$.
- At $x = 1$: $f_w(1) = c + \sum_{j=1}^H s_j(1 - t_j) = c + S + B = M(1)$ and $b(1) = 0$.
Hence $f_w \equiv M + b$ on $[-1, 1]$.

(3) On each open interval $(-1, t_1)$, $(t_j, t_{j+1})$ ($1 \le j \le H-1$), and $(t_H, 1)$, the slope of $f_w = M + b$ is respectively $0$, $m_0 + \frac{h_{j+1} - h_j}{\delta_j}$, and $S$. Since $s_j$ is the jump in slope of $f_w$ across $t_j$, taking right-minus-left slopes immediately yields the stated formulas for $s_1, s_2, \dots, s_{H-1}, s_H$ (using $S - m_0 = \frac{S\Delta - (St_H + B)}{\Delta} = \frac{-B - S t_1}{\Delta}$). To compute the Jacobian, define partial slope sums $p_j := \sum_{i=1}^j s_i$ for $1 \le j \le H$. The triangular map $s \mapsto p$ has $|\det \frac{\partial s}{\partial p}| = 1$. Moreover $p_H = S$, and for $1 \le j \le H-1$ telescoping gives $p_j = m_0 + \frac{h_{j+1} - h_j}{\delta_j}$, so
$$\delta_j p_j \;=\; \delta_j m_0 + h_{j+1} - h_j \qquad (1 \le j \le H-1,\; h_1 = h_H = 0).$$
In the $(H-1) \times (H-1)$ matrix of $(m_0, h_2, \dots, h_{H-1}) \mapsto (\delta_1 p_1, \dots, \delta_{H-1} p_{H-1})$, adding rows $1, \dots, H-2$ into row $H-1$ leaves row $H-1$ equal to $(\Delta, 0, \dots, 0)$, while rows $1, \dots, H-2$ in columns $(h_2, \dots, h_{H-1})$ form a lower-triangular matrix with $+1$'s on the diagonal. Thus $|\det \frac{\partial(\delta_1 p_1, \dots, \delta_{H-1} p_{H-1})}{\partial(m_0, h_2, \dots, h_{H-1})}| = \Delta$, so $|\det \frac{\partial(p_1, \dots, p_H)}{\partial(m_0, S, h_2, \dots, h_{H-1})}| = \Delta / \prod_{j=1}^{H-1} \delta_j$. Since $|\det \frac{\partial(m_0, S)}{\partial(B, S)}| = \frac{1}{\Delta}$, the factor $\Delta$ cancels and $|\det \frac{\partial s}{\partial(S, B, h_2, \dots, h_{H-1})}| = \prod_{j=1}^{H-1} \delta_j^{-1}$.

(4) Set $G(x, y) := \frac{\min(x - t_1, y - t_1)\cdot(t_H - \max(x, y))}{\Delta}$ for $x, y \in [t_1, t_H]$, and define $\tilde{b}(x) := -\sum_{k=2}^{H-1} s_k G(x, t_k)$ on $[t_1, t_H]$. Then $\tilde{b}$ is continuous, piecewise affine with breakpoints at $t_2, \dots, t_{H-1}$, satisfies $\tilde{b}(t_1) = \tilde{b}(t_H) = 0$, and at each $t_k$ ($2 \le k \le H-1$) has slope jump $-s_k(-\frac{t_k - t_1}{\Delta} - \frac{t_H - t_k}{\Delta}) = +s_k$, which matches the slope jump of $b$ at $t_k$. Thus $b - \tilde{b}$ is affine on $[t_1, t_H]$ and vanishes at $t_1$ and $t_H$, so $b \equiv \tilde{b}$. On every open interval $(t_j, t_{j+1})$, each summand $-G(\cdot, t_k)$ has slope in $(-1, 1)$, so
$$\left|\frac{h_{j+1} - h_j}{\delta_j}\right| \;=\; |b'(x)| \;\le\; \sum_{k=2}^{H-1} |s_k| \;\le\; \frac{4(H-2)}{9}. \qquad \square$$

---

**Lemma 1.2 (Global Population Coercivity).**
For every $H \ge 3$ and every $w \in W \cap \Omega_<$, writing $f_w = M + b$ as in Lemma 1.1:
$$K(w) \;\ge\; \frac{1}{3072}\bigl(c^2 + S^2 + B^2\bigr) + \frac{1}{36}\int_{t_1}^{t_H} b(x)^2 dx \;\ge\; \frac{1}{3072}\bigl(c^2 + S^2 + B^2\bigr) + \frac{1}{216}\sum_{j=1}^{H-1} \delta_j\bigl(h_j^2 + h_{j+1}^2\bigr).$$
In particular, for $H = 3$,
$$K(w) \;\ge\; \frac{1}{3072}\bigl(c^2 + S^2 + B^2\bigr) + \frac{1}{108}\,\tilde{h}^2(\delta_1 + \delta_2).$$

*Proof.* Set $m_1 := M(t_1) = c$, $m_H := M(t_H) = c + S t_H + B$, and $L := 1 - t_H \in [\frac{1}{2}, \frac{3}{2}]$. Since $b$ vanishes outside $[t_1, t_H]$,
$$4 K(w) \;=\; \int_{-1}^{t_1} M(x)^2 dx + \int_{t_H}^{1} M(x)^2 dx + \int_{t_1}^{t_H} \bigl(M(x) + b(x)\bigr)^2 dx.$$
First, $\int_{-1}^{t_1} M^2 = (1 + t_1) m_1^2 \ge \frac{1}{2} m_1^2$ since $t_1 \ge -\frac{1}{2}$. Second, on $[t_H, 1]$ we have $M(t_H + u) = m_H + S u$ for $u \in [0, L]$, and direct integration gives two exact completions of the square:
$$\int_{t_H}^{1} M(x)^2 dx = L m_H^2 + L^2 m_H S + \frac{L^3}{3} S^2 = \frac{L}{4} m_H^2 + L\left(\frac{\sqrt{3}}{2} m_H + \frac{L}{\sqrt{3}} S\right)^2 = \frac{L^3}{12} S^2 + L\left(m_H + \frac{L}{2} S\right)^2.$$
Hence $\int_{t_H}^{1} M^2 \ge \frac{L}{4} m_H^2 \ge \frac{1}{8} m_H^2$ and also $\int_{t_H}^{1} M^2 \ge \frac{1}{2}\cdot\frac{L}{4} m_H^2 + \frac{1}{2}\cdot\frac{L^3}{12} S^2 \ge \frac{1}{16} m_H^2 + \frac{1}{192} S^2$.

On $[t_1, t_H]$ (of length $\Delta \le 1$), $M$ is affine between $m_1$ and $m_H$, so $\int_{t_1}^{t_H} M^2 = \frac{\Delta}{3}(m_1^2 + m_1 m_H + m_H^2) \le \frac{1}{2}(m_1^2 + m_H^2)$. Comparing with $\int_{[-1, t_1] \cup [t_H, 1]} M^2 \ge \frac{1}{2} m_1^2 + \frac{1}{8} m_H^2 \ge \frac{1}{8}(m_1^2 + m_H^2)$ yields
$$\int_{[-1, t_1] \cup [t_H, 1]} M(x)^2 dx \;\ge\; \frac{1}{4}\int_{t_1}^{t_H} M(x)^2 dx.$$
Split $\int_{[-1, t_1] \cup [t_H, 1]} M^2$ into two equal halves:
- For the first half: since $B = m_H - c - S t_H$ with $|t_H| \le \frac{1}{2}$, Cauchy–Schwarz gives $B^2 \le 3 m_H^2 + 3 c^2 + \frac{3}{4} S^2$, so
  $$\frac{1}{384}(c^2 + S^2 + B^2) \le \frac{4}{384} c^2 + \frac{7}{1536} S^2 + \frac{3}{384} m_H^2 \le \frac{1}{2} c^2 + \frac{1}{192} S^2 + \frac{1}{16} m_H^2 \le \int_{[-1, t_1] \cup [t_H, 1]} M^2.$$
  Thus the first half is at least $\frac{1}{768}(c^2 + S^2 + B^2)$.
- For the second half + interior integral: using the elementary Hilbert-space inequality $\kappa \|u\|^2 + \|u + v\|^2 = (1 + \kappa)\|u + \frac{1}{1+\kappa}v\|^2 + \frac{\kappa}{1+\kappa}\|v\|^2 \ge \frac{\kappa}{1+\kappa}\|v\|^2$ on $L^2([t_1, t_H])$ with $\kappa = \frac{1}{8}$ (giving $\frac{\kappa}{1+\kappa} = \frac{1}{9}$),
  $$\frac{1}{2}\int_{[-1, t_1] \cup [t_H, 1]} M^2 + \int_{t_1}^{t_H} (M + b)^2 \;\ge\; \frac{1}{8}\int_{t_1}^{t_H} M^2 + \int_{t_1}^{t_H} (M + b)^2 \;\ge\; \frac{1}{9}\int_{t_1}^{t_H} b(x)^2 dx.$$

Dividing $4 K(w)$ by $4$ gives the first inequality. For the second, on each $[t_j, t_{j+1}]$, $b$ is affine between $h_j$ and $h_{j+1}$, so $\int_{t_j}^{t_{j+1}} b^2 = \frac{\delta_j}{3}(h_j^2 + h_j h_{j+1} + h_{j+1}^2) \ge \frac{\delta_j}{6}(h_j^2 + h_{j+1}^2)$ since $h_j^2 + h_j h_{j+1} + h_{j+1}^2 = \frac{1}{2}(h_j^2 + h_{j+1}^2) + \frac{1}{2}(h_j + h_{j+1})^2$. At $H = 3$, $\int_{t_1}^{t_3} \tau^2 = \frac{\delta_1 + \delta_2}{3}$, giving $\frac{1}{36}\cdot\frac{1}{3} = \frac{1}{108}$. $\square$

---

**Lemma 1.3 (Shared High-Probability Empirical Events and Uniform Bounds).**
Fix $n \ge 10$ and $K_0 > 0$. Define the following four events:
1. *(Endpoint statistics $E_{\mathrm{end}}$)* Let $N_L := N([-1, -\frac{1}{2}])$, $N_R := N([\frac{1}{2}, 1])$, $S_1 := \sum_{i=1}^n (X_i - \frac{3}{4})\mathbf{1}_{[\frac{1}{2}, 1]}(X_i)$, and $S_2 := \sum_{i=1}^n (X_i - \frac{3}{4})^2 \mathbf{1}_{[\frac{1}{2}, 1]}(X_i)$. Define
   $$E_{\mathrm{end}} \;:=\; \left\{N_L \ge \frac{n}{8},\; \frac{3n}{16} \le N_R \le \frac{5n}{16},\; |S_1| \le \frac{n}{200},\; S_2 \ge \frac{n}{256}\right\}.$$
2. *(Grid interval counts $E_{\mathrm{unif}}(h)$)* Given a mesh scale $h \in (0, \frac{1}{32}]$, let $M_h := \lceil 2/h \rceil$ and partition $[-1, 1]$ into $M_h$ consecutive intervals $C_1, \dots, C_{M_h}$ of equal length $h' := 2/M_h \in (\frac{1}{2}h, h]$. Define
   $$E_{\mathrm{unif}}(h) \;:=\; \left\{\forall j \in \{1, \dots, M_h\}:\; \frac{1}{4} n h' \le N(C_j) \le n h'\right\}.$$
3. *(1D partial-sum maximum $E_{\mathrm{max}}(K_0)$)* Let $M_n := \sup_{t \in [-1, 1]} \left|\sum_{i=1}^n \varepsilon_i \mathbf{1}_{\{X_i \ge t\}}\right|$ and define $E_{\mathrm{max}}(K_0) := \{M_n \le K_0 \sqrt{n}\}$.
4. *(All-interval Gaussian scan $E_{\mathrm{scan}}$)* Almost surely the order statistics $X_{(1)} < X_{(2)} < \cdots < X_{(n)}$ are distinct; let $\tilde{\varepsilon}_j$ be the noise associated with $X_{(j)}$. Define
   $$E_{\mathrm{scan}} \;:=\; \left\{\max_{1 \le p \le q \le n} \frac{\left|\sum_{j=p}^q \tilde{\varepsilon}_j\right|}{\sqrt{q - p + 1}} \le \sqrt{6\log n}\right\}.$$

Then the following hold:
- **(a) Probability bounds:**
  $$\mathbb{P}(E_{\mathrm{end}}^c) \le 6 e^{-n/5000}, \qquad \mathbb{P}(E_{\mathrm{unif}}(h)^c) \le 2 M_h e^{-n h / 32}, \qquad \mathbb{P}(E_{\mathrm{max}}(K_0)^c) \le 4 e^{-K_0^2/2}, \qquad \mathbb{P}(E_{\mathrm{scan}}^c) \le \frac{2}{n}.$$
- **(b) Uniform empirical macroscopic Gram & projection bounds on $E_{\mathrm{end}}$:** For every $H \ge 3$, every $-\frac{1}{2} \le t_1 < t_H \le \frac{1}{2}$, every $M = c + S\phi_S + B\phi_B \in \mathrm{span}(1, \phi_S, \phi_B)$ (with breakpoints $t_1, t_H$), and every function $b : [-1, 1] \to \mathbb{R}$ supported on $(t_1, t_H)$:
  1. The empirical $3 \times 3$ Gram matrix $G_n^{\mathrm{mac}}(t_1, t_H)$ of $\Phi := (1, \phi_S, \phi_B)^\top$ satisfies $G_n^{\mathrm{mac}}(t_1, t_H) \succeq \frac{n}{15000} I_3$.
  2. Letting $b_\perp$ be the $L^2(\mathbb{P}_n)$-orthogonal projection of $b$ onto $\mathrm{span}(\Phi)^\perp$, we have $\|b_\perp\|_n^2 \ge \frac{1}{1809}\|b\|_n^2$.
- **(c) Uniform interval counts & quarter-pairing on $E_{\mathrm{unif}}(h)$:** On $E_{\mathrm{unif}}(h)$, every interval $I \subset [-1, 1]$ of length $|I| \ge 4 h$ satisfies $\frac{1}{8} n |I| \le N(I) \le 2 n |I|$; every interval $I$ of length $|I| \le 12 h$ satisfies $N(I) \le 14 n h$. Moreover, if $b$ is affine on $[a, b'] \subset [-1, 1]$ with $b' - a \ge 16 h$, then
  $$\sum_{X_i \in (a, b')} b(X_i)^2 \;\ge\; \frac{1}{512}\, n (b' - a)\bigl(b(a)^2 + b(b')^2\bigr).$$
- **(d) Exact integral representations & scan bounds:** For every $-\frac{1}{2} \le t_1 < t_H \le \frac{1}{2}$, letting $U_n^{\mathrm{mac}}(t_1, t_H) := \sum_{i=1}^n \varepsilon_i \Phi(X_i) \in \mathbb{R}^3$, we have $\|U_n^{\mathrm{mac}}(t_1, t_H)\|_2^2 \le 6 M_n^2$ deterministically. On $E_{\mathrm{scan}}$, every interval $I \subset \mathbb{R}$ satisfies $|\sum_{X_i \in I} \varepsilon_i| \le \sqrt{6\log n}\,\sqrt{N(I)}$, and every monotone ramp $r_L(x; a, b') := \frac{x - a}{b' - a}\mathbf{1}_{[a, b']}(x)$ or $r_R(x; a, b') := \frac{b' - x}{b' - a}\mathbf{1}_{(a, b']}(x)$ satisfies $|\langle \varepsilon, r\rangle_n| \le \sqrt{6\log n}\,\sqrt{N([a, b'])}$.

*Proof.*
**(a)** For $E_{\mathrm{end}}$: $\mathbb{E}[N_L] = \mathbb{E}[N_R] = \frac{n}{4}$, $\mathbb{E}[S_1] = 0$ with summands in $[-\frac{1}{4}, \frac{1}{4}]$ (range $\frac{1}{2}$), and $\mathbb{E}[S_2] = \frac{n}{2}\int_{1/2}^1 (x - \frac{3}{4})^2 dx = \frac{n}{192}$ with summands in $[0, \frac{1}{16}]$ (range $\frac{1}{16}$). Applying Hoeffding's inequality to each of the four conditions gives
$$\mathbb{P}(E_{\mathrm{end}}^c) \le e^{-2n(1/8)^2} + 2 e^{-2n(1/16)^2} + 2 e^{-2(n/200)^2/(n/4)} + e^{-2(n/768)^2/(n/256)} = e^{-n/32} + 2 e^{-n/128} + 2 e^{-n/5000} + e^{-n/1152} \le 6 e^{-n/5000}.$$
For $E_{\mathrm{unif}}(h)$: each $N(C_j) \sim \mathrm{Bin}(n, h'/2)$ has mean $\mu = \frac{1}{2} n h' \ge \frac{1}{4} n h$, so the multiplicative Chernoff bound and a union bound over $j = 1, \dots, M_h$ give $\mathbb{P}(E_{\mathrm{unif}}(h)^c) \le M_h (e^{-\mu/8} + e^{-\mu/3}) \le 2 M_h e^{-n h / 32}$.
For $E_{\mathrm{max}}(K_0)$: conditional on $X^n$ (with distinct order statistics), $(\tilde{\varepsilon}_1, \dots, \tilde{\varepsilon}_n) \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$, and $M_n = \max_{1 \le k \le n} |\sum_{j=n-k+1}^n \tilde{\varepsilon}_j|$, so Lévy's maximal inequality yields $\mathbb{P}(M_n > K_0 \sqrt{n} \mid X^n) \le 4 e^{-K_0^2/2}$.
For $E_{\mathrm{scan}}$: conditional on $X^n$, for each of the $\binom{n+1}{2} = \frac{n(n+1)}{2}$ pairs $1 \le p \le q \le n$, $(q - p + 1)^{-1/2}\sum_{j=p}^q \tilde{\varepsilon}_j \sim \mathcal{N}(0, 1)$, so the Gaussian tail bound $\mathbb{P}(|Z| > \sqrt{6\log n}) \le 2 n^{-3}$ and a union bound give $\mathbb{P}(E_{\mathrm{scan}}^c \mid X^n) \le \frac{n(n+1)}{2}\cdot 2 n^{-3} = \frac{n+1}{n^2} \le \frac{2}{n}$.

**(b)** Assume $E_{\mathrm{end}}$ holds. Write $\bar{x}_R := \frac{3}{4} + \frac{S_1}{N_R}$ and $v_R := \frac{1}{N_R}\sum_{X_i \in [\frac{1}{2}, 1]} (X_i - \bar{x}_R)^2 = \frac{S_2}{N_R} - (\bar{x}_R - \frac{3}{4})^2$. On $E_{\mathrm{end}}$, $|\bar{x}_R - \frac{3}{4}| \le \frac{n/200}{3n/16} = \frac{2}{75} < 0.03$ and $v_R \ge \frac{n/256}{5n/16} - (\frac{2}{75})^2 = \frac{1}{80} - \frac{4}{5625} > \frac{1}{100}$. Since $t_H \in [-\frac{1}{2}, \frac{1}{2}]$, $|\bar{x}_R - t_H| \le 0.78 + 0.50 = 1.28 < \frac{3}{2}$. Let $m_1 := c = M(t_1)$ and $m_H := c + S t_H + B = M(t_H)$. Because $[-1, -\frac{1}{2}]$, $(t_1, t_H)$, and $[\frac{1}{2}, 1]$ are pairwise disjoint,
$$\sum_{X_i \in [-1, -\frac{1}{2}]} M(X_i)^2 = N_L c^2 \ge \frac{n}{8} c^2, \qquad \sum_{X_i \in [\frac{1}{2}, 1]} M(X_i)^2 = N_R\Bigl(\bigl(m_H + S(\bar{x}_R - t_H)\bigr)^2 + v_R S^2\Bigr).$$
Since $v_R S^2 \ge \frac{1}{100}\cdot\frac{4}{9}\bigl(S(\bar{x}_R - t_H)\bigr)^2 = \frac{1}{225}\bigl(S(\bar{x}_R - t_H)\bigr)^2$:
- Using the full $v_R S^2$ with $\kappa = \frac{1}{225}$ gives $\sum_{X_i \in [\frac{1}{2}, 1]} M^2 \ge \frac{n}{8}\cdot\frac{1}{226} m_H^2 = \frac{n}{1808} m_H^2$. Since $M$ is affine on $[t_1, t_H]$, $M(x)^2 \le \max(m_1^2, m_H^2) \le m_1^2 + m_H^2$ on $(t_1, t_H)$, so $\sum_{X_i \in (t_1, t_H)} M^2 \le n(m_1^2 + m_H^2) \le 1808 \sum_{X_i \in [-1, -\frac{1}{2}] \cup [\frac{1}{2}, 1]} M^2$. Therefore, for every $M \in \mathrm{span}(\Phi)$,
  $$\|M + b\|_n^2 \ge \sum_{X_i \in [-1, -\frac{1}{2}] \cup [\frac{1}{2}, 1]} M^2 + \sum_{X_i \in (t_1, t_H)} (M + b)^2 \ge \frac{1}{1808}\sum_{X_i \in (t_1, t_H)} M^2 + \sum_{X_i \in (t_1, t_H)} (M + b)^2 \ge \frac{1}{1809} \|b\|_n^2.$$
  Taking the infimum over $M \in \mathrm{span}(\Phi)$ gives $\|b_\perp\|_n^2 \ge \frac{1}{1809} \|b\|_n^2$.
- Splitting $v_R S^2 = \frac{1}{2} v_R S^2 + \frac{1}{2} v_R S^2$ ($\kappa = \frac{1}{450}$) gives $\sum_{X_i \in [\frac{1}{2}, 1]} M^2 \ge \frac{n}{8}(\frac{1}{451} m_H^2 + \frac{1}{200} S^2) = \frac{n}{3608} m_H^2 + \frac{n}{1600} S^2$. Since $B^2 = (m_H - c - S t_H)^2 \le 3 m_H^2 + 3 c^2 + \frac{3}{4} S^2$, we have
  $$\frac{n}{15000}(c^2 + S^2 + B^2) \le \frac{4n}{15000} c^2 + \frac{7n}{60000} S^2 + \frac{3n}{15000} m_H^2 \le \frac{n}{8} c^2 + \frac{n}{1600} S^2 + \frac{n}{3608} m_H^2 \le \|M\|_n^2,$$
  proving $G_n^{\mathrm{mac}}(t_1, t_H) \succeq \frac{n}{15000} I_3$.

**(c)** On $E_{\mathrm{unif}}(h)$, any interval $I \subset [-1, 1]$ of length $|I| \ge 4 h \ge 4 h'$ completely contains at least $|I|/h' - 2 \ge \frac{1}{2}|I|/h'$ cells $C_j$ and intersects at most $|I|/h' + 2 \le \frac{3}{2}|I|/h' \le 2|I|/h'$ cells $C_j$, yielding $\frac{1}{8} n |I| \le N(I) \le 2 n |I|$. If $|I| \le 12 h$, then since $h' > \frac{1}{2}h$ we have $|I|/h' + 2 \le \frac{12 h}{h'} + 2$, so $N(I) \le (12 h/h' + 2)(n h') = 12 n h + 2 n h' \le 14 n h$.
For the quarter-pairing bound: let $L := b' - a \ge 16 h$, $Q_1 := (a, a + L/4)$, $Q_4 := (b' - L/4, b')$. Since $|Q_1| = |Q_4| = L/4 \ge 4 h$, both $N(Q_1)$ and $N(Q_4)$ are at least $\frac{1}{8} n (L/4) = \frac{1}{32} n L$. Let $m := \min(N(Q_1), N(Q_4)) \ge \frac{1}{32} n L$, and pair $m$ distinct observations $x_1, \dots, x_m \in Q_1$ with $m$ distinct observations $x'_1, \dots, x'_m \in Q_4$. Writing $x_r = (1 - \theta_r) a + \theta_r b'$ and $x'_r = (1 - \theta'_r) a + \theta'_r b'$ with $\theta_r \in (0, \frac{1}{4})$ and $\theta'_r \in (\frac{3}{4}, 1)$, we have $\theta'_r - \theta_r > \frac{1}{2}$, and solving the $2 \times 2$ linear system $b(x_r) = (1 - \theta_r) b(a) + \theta_r b(b')$, $b(x'_r) = (1 - \theta'_r) b(a) + \theta'_r b(b')$ yields
$$b(a) = \frac{\theta'_r b(x_r) - \theta_r b(x'_r)}{\theta'_r - \theta_r}, \qquad b(b') = \frac{(1 - \theta_r) b(x'_r) - (1 - \theta'_r) b(x_r)}{\theta'_r - \theta_r},$$
so $b(a)^2 + b(b')^2 \le 4 \cdot 2(b(x_r)^2 + b(x'_r)^2) + 4 \cdot 2(b(x_r)^2 + b(x'_r)^2) = 16(b(x_r)^2 + b(x'_r)^2)$. Summing over $r = 1, \dots, m$ gives $\sum_{X_i \in (a, b')} b(X_i)^2 \ge \frac{m}{16}(b(a)^2 + b(b')^2) \ge \frac{1}{512} n L (b(a)^2 + b(b')^2)$.

**(d)** For all $x \in [-1, 1]$, we have the exact integral identities
$$\phi_B(x) = \frac{1}{\Delta}\int_{t_1}^{t_H} \mathbf{1}_{\{x \ge t\}}\,dt, \qquad \phi_S(x) = t_H \phi_B(x) + \int_{t_H}^{1} \mathbf{1}_{\{x \ge t\}}\,dt.$$
Indeed, both sides agree on $[-1, t_1)$ (value $0$), on $[t_1, t_H]$ (values $\frac{x - t_1}{\Delta}$ and $t_H \frac{x - t_1}{\Delta}$), and on $(t_H, 1]$ (values $1$ and $t_H + (x - t_H) = x$). Hence $|U_{n, 0}^{\mathrm{mac}}| = |\sum_{i=1}^n \varepsilon_i| \le M_n$, $|U_{n, 2}^{\mathrm{mac}}| \le \frac{1}{\Delta}\int_{t_1}^{t_H} M_n\,dt = M_n$, and $|U_{n, 1}^{\mathrm{mac}}| \le |t_H|\,M_n + (1 - t_H) M_n \le 2 M_n$ (using $|t_H| \le \frac{1}{2}$), giving $\|U_n^{\mathrm{mac}}\|_2^2 \le (1 + 1 + 4) M_n^2 = 6 M_n^2$.
Finally, on $E_{\mathrm{scan}}$, for any interval $I \subset \mathbb{R}$, the indices $\{j : X_{(j)} \in I\}$ form a contiguous block of length $N(I)$, so $|\sum_{X_i \in I} \varepsilon_i| \le \sqrt{6\log n}\,\sqrt{N(I)}$. Using the exact pointwise identities
$$r_L(x; a, b') = \frac{1}{b' - a}\int_{a}^{b'} \mathbf{1}_{[s, b']}(x)\,ds, \qquad r_R(x; a, b') = \frac{1}{b' - a}\int_{a}^{b'} \mathbf{1}_{(a, s]}(x)\,ds \qquad (\forall x \in \mathbb{R}),$$
and noting $N([s, b']) \le N([a, b'])$ and $N((a, s]) \le N([a, b'])$ for $s \in [a, b']$, the triangle inequality yields $|\langle \varepsilon, r\rangle_n| \le \sqrt{6\log n}\,\sqrt{N([a, b'])}$. $\square$

---

## 2. Theorem A: Display 1 at $r = 1, H = 3$ [(iii)]

**Theorem A (Sublevel Volume Asymptotics at $r = 1, H = 3$) [(iii)].**
Let $r = 1$, $H = 3$, $w^0 = \bigl(0, (1, 0, 0), (1, 0, 0), (1, 0, 0)\bigr) \in \mathbb{R}^{10}$, $W = \overline{B_{1/3}(w^0)}$, and $\varphi \equiv 1/\mathrm{vol}(W)$. Then there exists an explicit finite constant $c_0 > 0$ such that as $\varepsilon \downarrow 0$,
$$\int_{\{K \le \varepsilon\} \cap W} \varphi(w)\,dw \;=\; c_0\,\varepsilon^{11/6}\bigl(1 + o(1)\bigr).$$
Consequently, Display 1 holds with the uniquely determined pair $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = \bigl(\tfrac{11}{6}, 1\bigr)$ (no $\log(1/\varepsilon)$ factor).

*Proof.* The set $\{w \in W : t_i = t_j \text{ for some } i \neq j\}$ is contained in a finite union of hypersurfaces and has Lebesgue measure $0$. By $S_3$ permutation symmetry of $W$ and $K$,
$$\mathrm{vol}\bigl(\{K \le \varepsilon\} \cap W\bigr) \;=\; 6\,\mathrm{vol}\bigl(\{K \le \varepsilon\} \cap W \cap \Omega_<\bigr).$$
Apply the $C^\infty$ diffeomorphism of Lemma 1.1 on $\Omega_< = \{t_1 < t_2 < t_3\}$ to coordinates $(a, t_1, c, S, B, \delta_1, \delta_2, \tilde{h})$ (with $a = (a_1, a_2, a_3)$ and Jacobian $\frac{1}{\delta_1 \delta_2}$), followed by the $\varepsilon$-rescaling
$$(c, S, B) = \varepsilon^{1/2}(\hat{c}, \hat{S}, \hat{B}), \qquad (\delta_1, \delta_2, \tilde{h}) = \varepsilon^{1/3}(x_1, x_2, y),$$
leaving $(a, t_1)$ unscaled. The Jacobian of the rescaling is $\varepsilon^{3/2} \cdot \varepsilon^{3/3} / \varepsilon^{2/3} = \varepsilon^{11/6}$, so
$$\frac{\mathrm{vol}\bigl(\{K \le \varepsilon\} \cap W\bigr)}{\varepsilon^{11/6}} \;=\; 6 \int_{\mathcal{U}} \mathbf{1}_{A_\varepsilon}(a, t_1, \hat{c}, \hat{S}, \hat{B}, x_1, x_2, y)\,\frac{da\,dt_1\,d\hat{c}\,d\hat{S}\,d\hat{B}\,dx_1\,dx_2\,dy}{x_1 x_2},$$
where $\mathcal{U} := (0, \infty)^3 \times [-1/2,1/2] \times \mathbb{R}^3 \times (0, \infty)^2 \times \mathbb{R}$, and $A_\varepsilon \subset \mathcal{U}$ is the set of rescaled coordinates whose preimage $w_\varepsilon$ satisfies $\|w_\varepsilon - w^0\|_2^2 \le \frac{1}{9}$ and $K(w_\varepsilon) \le \varepsilon$.

**Step 1: Uniform $L^1$ dominating function.** For any point in $A_\varepsilon$:
- By Lemma 1.1(1), $a \in [\frac{2}{3}, \frac{4}{3}]^3$ and $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$.
- By Lemma 1.2, $K(w_\varepsilon) \le \varepsilon$ implies $\hat{c}^2 + \hat{S}^2 + \hat{B}^2 \le 3072$ (so $\hat{c}, \hat{S}, \hat{B} \in [-\sqrt{3072}, \sqrt{3072}]$) and $(x_1 + x_2) y^2 \le 108$, hence $|y| \le \sqrt{108/(x_1 + x_2)}$.
- By Lemma 1.1(4), $s_2 = -y\frac{x_1 + x_2}{x_1 x_2}$ is independent of $(c, S, B, \varepsilon)$, so $|s_2| \le \frac{4}{9}$ yields $|y| \le \frac{4}{9}\frac{x_1 x_2}{x_1 + x_2}$ uniformly in $\varepsilon > 0$.

Therefore $\frac{\mathbf{1}_{A_\varepsilon}}{x_1 x_2} \le g$ pointwise for all $\varepsilon > 0$, where
$$g \;:=\; \mathbf{1}_{[\frac{2}{3}, \frac{4}{3}]^3}(a)\,\mathbf{1}_{[-\frac{1}{2}, \frac{1}{2}]}(t_1)\,\mathbf{1}_{[-\sqrt{3072}, \sqrt{3072}]^3}(\hat{c}, \hat{S}, \hat{B})\,\mathbf{1}_{\left\{|y| \le \min\left(\frac{4}{9}\frac{x_1 x_2}{x_1 + x_2},\; \sqrt{\frac{108}{x_1 + x_2}}\right)\right\}}\,\frac{1}{x_1 x_2}.$$
To verify $g \in L^1(\mathcal{U})$, integrate out $(a, t_1, \hat{c}, \hat{S}, \hat{B})$ (finite volume $M_0 := (\frac{2}{3})^3 \cdot 1 \cdot (2\sqrt{3072})^3$) and $y$, and use $(x_1, x_2)$-symmetry to restrict to $0 < x_1 \le x_2 < \infty$ (factor $2$). Setting $x_2 = x \in (0, \infty)$ and $x_1 = u x$ with $u \in (0, 1]$ (Jacobian $\frac{dx_1 dx_2}{x_1 x_2} = \frac{du\,dx}{u x}$), the crossover point where $\frac{4}{9}\frac{ux}{1+u} = \sqrt{\frac{108}{(1+u)x}}$ is $x_*(u) = \alpha_0 (1+u)^{1/3} u^{-2/3}$ with $\alpha_0 := (\frac{9}{4}\sqrt{108})^{2/3}$. Thus
$$\int_{\mathcal{U}} g \;=\; 4 M_0 \int_0^1 \left[\int_0^{x_*(u)} \frac{4}{9(1+u)}\,dx + \int_{x_*(u)}^\infty \frac{\sqrt{108}}{u\sqrt{1+u}}\,x^{-3/2}\,dx\right] du \;=\; 4 M_0 \int_0^1 \frac{4\alpha_0}{3}(1+u)^{-2/3} u^{-2/3}\,du \;\le\; 16 M_0 \alpha_0 < \infty,$$
using $\int_0^1 u^{-2/3}\,du = 3$.

**Step 2: Pointwise limit a.e.** Fix $(a, t_1, \hat{c}, \hat{S}, \hat{B}, x_1, x_2, y)$ in the support box of Step 1. Off that box the rescaled integrand vanishes. As $\varepsilon \downarrow 0$, we have $c, S, B = O(\varepsilon^{1/2}) \to 0$, $t_2 = t_1 + \varepsilon^{1/3} x_1 \to t_1$, $t_3 = t_1 + \varepsilon^{1/3}(x_1 + x_2) \to t_1$, and from Lemma 1.1(3):
$$s_1 = \varepsilon^{1/6}\frac{\hat{B} + \hat{S} t_3}{x_1 + x_2} + \frac{y}{x_1} \to \frac{y}{x_1}, \qquad s_2 = -y\frac{x_1 + x_2}{x_1 x_2}, \qquad s_3 = \varepsilon^{1/6}\frac{-\hat{B} - \hat{S} t_1}{x_1 + x_2} + \frac{y}{x_2} \to \frac{y}{x_2}.$$
Hence $\|w_\varepsilon - w^0\|_2^2 \to D_0(a, t_1, x_1, x_2, y) := \sum_{j=1}^3 ((a_j - 1)^2 + a_j^2 t_1^2) + y^2 Q(a, x_1, x_2)$, where
$$Q(a, x_1, x_2) \;:=\; \frac{1}{a_1^2 x_1^2} + \frac{(x_1 + x_2)^2}{a_2^2 x_1^2 x_2^2} + \frac{1}{a_3^2 x_2^2} > 0.$$
Next, write $M_\varepsilon = \varepsilon^{1/2} \hat{M}_\varepsilon$ where $\hat{M}_\varepsilon(x) = \hat{c} + \hat{S}\phi_S(x) + \hat{B}\phi_B(x)$. As $\varepsilon \downarrow 0$, $\hat{M}_\varepsilon(x) \to \hat{c} + (\hat{S}x + \hat{B})\mathbf{1}_{\{x > t_1\}}$ for every $x \neq t_1$, with $|\hat{M}_\varepsilon(x)| \le |\hat{c}| + |\hat{S}| + |\hat{B}|$. Therefore,
$$\frac{K(w_\varepsilon)}{\varepsilon} = \frac{1}{4}\int_{-1}^{1} \hat{M}_\varepsilon(x)^2 dx + \frac{1}{2}\varepsilon^{-1/6} y \int_{t_1}^{t_3} \hat{M}_\varepsilon(x)\tau(x)\,dx + \frac{1}{12} y^2(x_1 + x_2) \;\longrightarrow\; K_0(\hat{c}, \hat{S}, \hat{B}, x_1, x_2, y; t_1),$$
since the cross term is bounded in magnitude by $\frac{1}{2}\varepsilon^{1/6}|y|(x_1 + x_2)(|\hat{c}| + |\hat{S}| + |\hat{B}|) \to 0$, and where
$$K_0(\hat{c}, \hat{S}, \hat{B}, x_1, x_2, y; t_1) \;:=\; K_{\mathrm{mac}}(\hat{c}, \hat{S}, \hat{B}; t_1) + \frac{1}{12} y^2 (x_1 + x_2), \qquad K_{\mathrm{mac}} := \frac{1}{4}\left((1+t_1)\hat{c}^2 + \int_{t_1}^{1} (\hat{c} + \hat{S}x + \hat{B})^2 dx\right).$$
For any fixed $(a, t_1, \hat{c}, \hat{S}, \hat{B}, x_1, x_2)$ with $a_j > 0, x_1, x_2 > 0$, $y \mapsto D_0$ is a strictly convex quadratic ($Q > 0$), so $\{y : D_0 = \frac{1}{9}\}$ has at most $2$ points; for any fixed $(a, t_1, x_1, x_2, y)$ with $t_1 \in [-1/2, 1/2]$, $(\hat{c}, \hat{S}, \hat{B}) \mapsto K_{\mathrm{mac}}$ is a positive-definite quadratic form (its three basis functions are linearly independent on the two exterior intervals), so $\{(\hat{c}, \hat{S}, \hat{B}) : K_0 = 1\}$ has three-dimensional Lebesgue measure $0$. By Tonelli's theorem, $\{D_0 = \frac{1}{9}\} \cup \{K_0 = 1\}$ has Lebesgue measure $0$, so $\mathbf{1}_{A_\varepsilon} \to \mathbf{1}_{\{D_0 < 1/9,\; K_0 < 1\}}$ a.e. on $\mathcal{U}$.

**Step 3: DCT and positivity.** By Lebesgue's Dominated Convergence Theorem,
$$\lim_{\varepsilon \downarrow 0} \frac{\mathrm{vol}\bigl(\{K \le \varepsilon\} \cap W\bigr)}{\varepsilon^{11/6}} \;=\; C_{\mathrm{vol}} \;:=\; 6 \int_{\mathcal{U}} \mathbf{1}_{\{D_0 < 1/9,\; K_0 < 1\}}\,\frac{da\,dt_1\,d\hat{c}\,d\hat{S}\,d\hat{B}\,dx_1\,dx_2\,dy}{x_1 x_2} \;<\; \infty.$$
The limit set $\{D_0 < \frac{1}{9},\; K_0 < 1\}$ is open in $\mathcal{U}$ and nonempty—it contains $(a, t_1, \hat{c}, \hat{S}, \hat{B}, x_1, x_2, y) = ((1, 1, 1), 0, 0, 0, 0, 1, 1, 0)$, where $D_0 = 0 < \frac{1}{9}$ and $K_0 = 0 < 1$—so $C_{\mathrm{vol}} > 0$. Setting $c_0 := C_{\mathrm{vol}}/\mathrm{vol}(W) \in (0, \infty)$ completes the proof. Finally, if $c_0 \varepsilon^{11/6}(1+o(1)) = c_0' \varepsilon^{\lambda'}(\log(1/\varepsilon))^{m'-1}(1+o(1))$, taking ratios forces $\lambda' = \frac{11}{6}$ and then $m' = 1$. $\square$

---
*Volume interpretation.* For $X$ uniform on $[-1,1]$, let $G_{\mathrm{mac}}(t)$ be the Gram matrix of $(1,X\mathbf1_{X>t},\mathbf1_{X>t})$. Then $K_{\mathrm{mac}}(\theta;t)=\tfrac12\theta^\top G_{\mathrm{mac}}(t)\theta$. Its determinant is $(1+t)(1-t)^4/96$, by taking moments on $[t,1]$. This notation will also be used for width two.

There is a shorter way to identify the pair once the order of the volume is known. The domination in Step 1 gives the upper bound, and the strict feasible point in Step 3 and a compact neighborhood give a lower bound of the same order by Fatou's lemma. Here $K$ is piecewise rational on the ordered sectors by integration of the squared affine pieces. For this semialgebraic family, subanalytic volume integration gives a one-variable constructible function with leading power–log term (Lion–Rolin). Order $\Theta(\varepsilon^{11/6})$ forces the pair $(11/6,1)$. Steps 1–3 give its finite positive limit directly.

*Numerical illustration.* At $H=3$, estimated local slopes of the log sublevel volume against $\log\varepsilon$ were about $1.812$ at $\varepsilon=10^{-14}$ and $1.832$ at $10^{-24}$. These illustrate the approach to $11/6$. The probabilistic coefficient of $\log\log n$ follows from the evidence bounds in §§3–4.

---

## 3. Theorem B (Part I) and Corollary 1: Refutation of MAIS-O71 [(iii)]

**Theorem B (Evidence Lower Bound / Free-Energy Upper Bound at $r = 1, H = 3$) [(iii)].**
In the setting of Theorem A ($r = 1$, $H = 3$, $w^0 = (0, (1, 0, 0)^3)$, $W = \overline{B_{1/3}(w^0)}$, $\varphi \equiv 1/\mathrm{vol}(W)$),
$$F_n - n S_n \;\le\; \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1).$$
Equivalently, for every $\eta \in (0, 1)$ there exist $c(\eta) > 0$ and $N(\eta) \in \mathbb{N}$ such that for all $n \ge N(\eta)$,
$$\mathbb{P}\!\left(Z_n \;\ge\; c(\eta)\, n^{-11/6} (\log n)^{1/3}\right) \;\ge\; 1 - \eta.$$

*Proof.* Restrict the nonnegative integrand of $Z_n$ to the ordered sector $\Omega_< = \{t_1 < t_2 < t_3\}$ and change variables from Lemma 1.1's $(a_1, a_2, a_3, t_1, c, S, B, \delta_1, \delta_2, \tilde{h})$ to $(a_1, a_2, a_3, t_1, c, S, B, \delta, u, \tilde{s}_1)$ via
$$\delta := \delta_2, \qquad u := \frac{\delta_1}{\delta_2}, \qquad \tilde{s}_1 := \frac{\tilde{h}}{u\delta}.$$
The absolute Jacobian of $(u, \delta, \tilde{s}_1)\mapsto(\delta_1,\delta_2,\tilde h)$ is $\delta \cdot u\delta = u\delta^2 = \delta_1 \delta_2$, which cancels the factor $\frac{1}{\delta_1 \delta_2}$ from Lemma 1.1(3); hence the total Jacobian from the original coordinates $w \in \mathbb{R}^{10}$ to $(a_1, a_2, a_3, t_1, c, S, B, \delta, u, \tilde{s}_1)$ is **identically $1$**.

Set $c_1 := 10$, $\delta_- := n^{-1/3}$, and $\delta_+ := c_1 n^{-1/3} (\log n)^{1/3} = 10 n^{-1/3} (\log n)^{1/3}$. Define the coordinate sub-box
$$B_n \;:=\; \Bigl\{a_j \in [0.95, 1.05],\; t_1 \in [-0.03, 0.03],\; u \in [\tfrac{1}{4}, \tfrac{1}{2}],\; \tilde{s}_1 \in [-0.02, 0.02],\; c, S, B \in [-n^{-1/2}, n^{-1/2}],\; \delta \in [\delta_-, \delta_+]\Bigr\}.$$

**Step 1: Sub-box inclusion $B_n \subset W$.** Choose $N_1 \in \mathbb{N}$ so that for all $n \ge N_1$, $\delta_+ \le 0.05$, $\delta_+ \ge 2\delta_-$, and $n^{-1/6} \le 0.05$ (e.g., $N_1 = 2 \times 10^8$). On $B_n$:
- $c^2 \le n^{-1} \le 0.05^6 < 10^{-7}$ and $\sum_{j=1}^3 (a_j - 1)^2 \le 3(0.05)^2 = 0.0075$.
- $|t_1| \le 0.03$, $|t_2| \le 0.03 + \frac{1}{2}\delta_+ \le 0.055$, and $|t_3| \le 0.03 + \frac{3}{2}\delta_+ \le 0.105$, so $\sum_{j=1}^3 b_j^2 = \sum_{j=1}^3 a_j^2 t_j^2 \le (1.05)^2(0.03^2 + 0.055^2 + 0.105^2) < 0.017$.
- From Lemma 1.1(3), $s_2 = -\tilde{s}_1(1 + u)$, $s_1 = \frac{B + S t_3}{(1+u)\delta} + \tilde{s}_1$, and $s_3 = \frac{-B - S t_1}{(1+u)\delta} + u\tilde{s}_1$. Since $(1+u)\delta \ge \frac{5}{4} n^{-1/3}$ and $|B + S t_j| \le 2 n^{-1/2}$, we obtain $|s_2| \le 0.03$, $|s_1| \le \frac{8}{5} n^{-1/6} + 0.02 \le 0.10$, and $|s_3| \le \frac{8}{5} n^{-1/6} + 0.01 \le 0.09$. Hence $\sum_{j=1}^3 v_j^2 = \sum_{j=1}^3 s_j^2 / a_j^2 \le (0.10^2 + 0.03^2 + 0.09^2)/0.95^2 < 0.022$.

Summing gives $\|w - w^0\|_2^2 < 0.0001 + 0.0075 + 0.017 + 0.022 = 0.0466 < \frac{1}{9}$, so $B_n \subset W$ for all $n \ge N_1$.

**Step 2: Exact splitting of the log-likelihood ratio and uniform macro/cross bounds.** On $B_n$, $f_w = M + \tilde{s}_1 \psi_{t_1, u, \delta}$ where $\psi_{t_1, u, \delta}(x) := u\delta\,\tau_{t_1, u\delta, \delta}(x)$ is supported on $[t_1, t_1 + (1+u)\delta]$ (of length $(1+u)\delta \le \frac{3}{2}\delta_+$) and satisfies $0 \le \psi_{t_1, u, \delta}(x) \le \frac{1}{2}\delta_+$. The exponent splits identically as
$$\langle \varepsilon, f_w\rangle_n - \frac{1}{2}\|f_w\|_n^2 \;=\; \underbrace{\langle \varepsilon, M\rangle_n - \frac{1}{2}\|M\|_n^2}_{\mathrm{Macro}} \;+\; \underbrace{\tilde{s}_1\langle \varepsilon, \psi_{t_1, u, \delta}\rangle_n - \frac{1}{2}\tilde{s}_1^2\|\psi_{t_1, u, \delta}\|_n^2}_{\mathrm{Tent}} \;-\; \underbrace{\tilde{s}_1\langle M, \psi_{t_1, u, \delta}\rangle_n}_{\mathrm{Cross}}.$$
Apply Lemma 1.3 with mesh $h := \delta_+ / 8$ (so $M_h \le \frac{16}{\delta_+} + 1 \le 17 n^{1/3}$) and $K_0 := \sqrt{2\log(16/\eta)}$.
- *Macro:* For every $x \in [-1, 1]$ and $(c, S, B) \in [-n^{-1/2}, n^{-1/2}]^3$, $|M(x)| \le |c| + |S| + |B| \le 3 n^{-1/2}$, so $\frac{1}{2}\|M\|_n^2 \le \frac{9}{2}$. By Lemma 1.3(d), $|\langle \varepsilon, M\rangle_n| \le n^{-1/2}(M_n + 2 M_n + M_n) = 4 n^{-1/2} M_n$. Thus on $E_{\mathrm{max}}(K_0)$, $\mathrm{Macro} \ge -4 K_0 - \frac{9}{2}$ uniformly on $B_n$.
- *Cross:* Every support interval $I = [t_1, t_1 + (1+u)\delta]$ has length $\le \frac{3}{2}\delta_+ = 12 h$, and is contained in an interval of length $2\delta_+$ (whose expected sample count is $n\delta_+$). On $E_{\mathrm{unif}}(\delta_+/8)$, Lemma 1.3(c) gives $N(I) \le 14 n h = \frac{7}{4} n \delta_+ \le 2 n \delta_+$ uniformly over $B_n$. Therefore, on $E_{\mathrm{unif}}(\delta_+/8)$,
  $$|\mathrm{Cross}| \;\le\; (0.02)(3 n^{-1/2})\left(\frac{1}{2}\delta_+\right)(2 n \delta_+) \;=\; 0.06\, n^{1/2}\delta_+^2 \;=\; 6\,n^{-1/6}(\log n)^{2/3} \;\le\; 1$$
  for all $n \ge N_2$ (choosing $N_2 \ge N_1$ so that $6 n^{-1/6}(\log n)^{2/3} \le 1$).

Integrating out $(a_1, a_2, a_3) \in [0.95, 1.05]^3$ (volume $10^{-3}$) and $(c, S, B) \in [-n^{-1/2}, n^{-1/2}]^3$ (volume $8 n^{-3/2}$), we obtain on $E_{\mathrm{max}}(K_0) \cap E_{\mathrm{unif}}(\delta_+/8)$:
$$Z_n \;\ge\; \frac{8 \times 10^{-3}}{\mathrm{vol}(W)}\, e^{-4 K_0 - 11/2}\, n^{-3/2}\, J_n,$$
where
$$g(t_1; u, \delta) := \int_{-0.02}^{0.02} \exp\!\left(\tilde{s}_1\langle \varepsilon, \psi_{t_1, u, \delta}\rangle_n - \frac{1}{2}\tilde{s}_1^2\|\psi_{t_1, u, \delta}\|_n^2\right) d\tilde{s}_1, \quad G_n(u, \delta) := \int_{-0.03}^{0.03} g(t_1; u, \delta)\,dt_1, \quad J_n := \int_{\delta_-}^{\delta_+} \int_{1/4}^{1/2} G_n(u, \delta)\,du\,d\delta.$$

**Step 3: Conditional first and second moment of $J_n$ given $X^n$.** Condition on $X^n \in E_{\mathrm{unif}}(\delta_+/8)$.
- *Exact conditional mean:* By Tonelli's theorem and the Gaussian MGF identity $\mathbb{E}_\varepsilon[\exp(\tilde{s}_1\langle \varepsilon, \psi\rangle_n - \frac{1}{2}\tilde{s}_1^2\|\psi\|_n^2) \mid X^n] = 1$,
  $$\mathbb{E}_\varepsilon[g(t_1; u, \delta) \mid X^n] = 0.04, \qquad \mathbb{E}_\varepsilon[G_n(u, \delta) \mid X^n] = 0.0024, \qquad \mathbb{E}_\varepsilon[J_n \mid X^n] = 0.0006(\delta_+ - \delta_-).$$
- *Disjoint-support conditional variance:* Fix $(u, \delta) \in [\frac{1}{4}, \frac{1}{2}] \times [\delta_-, \delta_+]$. Because $\mathrm{supp}(\psi_{t_1, u, \delta}) = [t_1, t_1 + (1+u)\delta]$ has length $(1+u)\delta \le \frac{3}{2}\delta$, whenever $|t_1 - t_1'| > \frac{3}{2}\delta$ the supports of $\psi_{t_1, u, \delta}$ and $\psi_{t_1', u, \delta}$ are disjoint. Consequently $g(t_1; u, \delta)$ and $g(t_1'; u, \delta)$ depend on disjoint subsets of the independent variables $\{\varepsilon_1, \dots, \varepsilon_n\}$, so $\mathrm{Cov}_\varepsilon(g(t_1), g(t_1') \mid X^n) = 0$.
  For $|t_1 - t_1'| \le \frac{3}{2}\delta$, Cauchy–Schwarz gives $\mathrm{Cov}_\varepsilon(g(t_1), g(t_1') \mid X^n) \le (\mathbb{E}_\varepsilon[g(t_1)^2 \mid X^n]\,\mathbb{E}_\varepsilon[g(t_1')^2 \mid X^n])^{1/2}$. By Tonelli and the Gaussian MGF identity,
  $$\mathbb{E}_\varepsilon[g(t_1)^2 \mid X^n] = \iint_{[-0.02, 0.02]^2} \mathbb{E}_\varepsilon\!\left[\exp\!\left((a+b)\langle\varepsilon, \psi\rangle_n - \frac{1}{2}(a^2 + b^2)\|\psi\|_n^2\right) \,\Big|\, X^n\right] da\,db = \iint_{[-0.02, 0.02]^2} e^{ab\|\psi\|_n^2}\,da\,db \le (0.04)^2 e^{(0.02)^2 \|\psi\|_n^2}.$$
  On $E_{\mathrm{unif}}(\delta_+/8)$, we have $\|\psi_{t_1, u, \delta}\|_n^2 \le (\frac{1}{2}\delta_+)^2 N(\mathrm{supp}(\psi)) \le \frac{1}{4}\delta_+^2 \cdot (2 n \delta_+) = \frac{1}{2} c_1^3 \log n = 500 \log n$, so $(0.02)^2 \|\psi\|_n^2 \le 0.2 \log n$ and $\mathbb{E}_\varepsilon[g(t_1)^2 \mid X^n] \le (0.04)^2 n^{0.2}$. The set $\{(t_1, t_1') \in [-0.03, 0.03]^2 : |t_1 - t_1'| \le \frac{3}{2}\delta\}$ has area at most $0.06 \cdot 3\delta \le 0.18\,\delta_+$, hence
  $$\mathrm{Var}_\varepsilon\bigl(G_n(u, \delta) \mid X^n\bigr) \;\le\; 0.18\,\delta_+ \cdot (0.04)^2 n^{0.2} \;=\; 2.88 \times 10^{-4}\,\delta_+ n^{0.2}.$$
  Integrating over $\Omega := [\frac{1}{4}, \frac{1}{2}] \times [\delta_-, \delta_+]$ (area $\frac{1}{4}(\delta_+ - \delta_-)$) and applying Cauchy–Schwarz to $\mathrm{Cov}_\varepsilon(G_n(\omega), G_n(\omega') \mid X^n)$ gives
  $$\mathrm{Var}_\varepsilon(J_n \mid X^n) \;\le\; \left(\int_\Omega \sqrt{\mathrm{Var}_\varepsilon(G_n(\omega) \mid X^n)}\,d\omega\right)^2 \;\le\; \frac{1}{16}(\delta_+ - \delta_-)^2 \cdot 2.88 \times 10^{-4}\,\delta_+ n^{0.2}.$$
- *Conditional Chebyshev bound:* On $E_{\mathrm{unif}}(\delta_+/8)$,
  $$\mathbb{P}_\varepsilon\!\left(J_n < \frac{1}{2}\mathbb{E}_\varepsilon[J_n \mid X^n] \,\Big|\, X^n\right) \;\le\; \frac{4\,\mathrm{Var}_\varepsilon(J_n \mid X^n)}{(\mathbb{E}_\varepsilon[J_n \mid X^n])^2} \;\le\; \frac{4 \cdot \frac{1}{16} \cdot 2.88 \times 10^{-4}\,\delta_+ n^{0.2}}{(0.0006)^2} \;=\; 200\,\delta_+ n^{0.2} \;=\; 2000\,n^{-2/15}(\log n)^{1/3}.$$

**Step 4: Union bound and conclusion.** By Lemma 1.3(a), $\mathbb{P}(E_{\mathrm{max}}(K_0)^c) \le 4 e^{-K_0^2/2} = \eta/4$, and $\mathbb{P}(E_{\mathrm{unif}}(\delta_+/8)^c) \le 34 n^{1/3}\exp(-\frac{10}{256} n^{2/3}(\log n)^{1/3}) \to 0$. Choose $N(\eta) \ge N_2$ large enough that for all $n \ge N(\eta)$, $\mathbb{P}(E_{\mathrm{unif}}(\delta_+/8)^c) \le \eta/4$ and $2000 n^{-2/15}(\log n)^{1/3} \le \eta/2$. Then the event $E_{\mathrm{max}}(K_0) \cap E_{\mathrm{unif}}(\delta_+/8) \cap \{J_n \ge \frac{1}{2}\mathbb{E}_\varepsilon[J_n \mid X^n]\}$ has probability at least $1 - \eta$. On this event, using $\delta_+ - \delta_- \ge \frac{1}{2}\delta_+ = 5 n^{-1/3}(\log n)^{1/3}$,
$$Z_n \;\ge\; \frac{8 \times 10^{-3}}{\mathrm{vol}(W)}\,e^{-4 K_0 - 11/2}\,n^{-3/2}\cdot (0.0003 \cdot 5 n^{-1/3}(\log n)^{1/3}) \;=\; \frac{1.2 \times 10^{-5}\, e^{-4 K_0 - 11/2}}{\mathrm{vol}(W)}\,n^{-11/6}(\log n)^{1/3}.$$
Taking $-\log$ yields $F_n - n S_n \le \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$. $\square$

---

**Corollary 1 (Refutation of MAIS-O71) [(iii)].**
MAIS-O71 (MAIS-A6, Question 9.2) is **false**.

*Proof.* Take $r = 1$, $H = 3$, $w^0 = (0, (1, 0, 0)^3)$, $W = \overline{B_{1/3}(w^0)}$, and $\varphi \equiv 1/\mathrm{vol}(W)$. Suppose for contradiction that there exist $\lambda > 0$, an integer $m \ge 1$, and $c_0 > 0$ satisfying both Display 1 and Display 2. By Theorem A, Display 1 forces $(\lambda, m) = (\frac{11}{6}, 1)$ uniquely. Display 2 with $(\lambda, m) = (\frac{11}{6}, 1)$ asserts that $R_n := F_n - n S_n - \frac{11}{6}\log n = O_p(1)$. However, Theorem B gives $R_n \le -\frac{1}{3}\log\log n + O_p(1)$, whence $R_n \xrightarrow{p} -\infty$, contradicting $R_n = O_p(1)$. $\square$

---

## 4. Theorem C (Part II) and Corollary 2: Matching Upper Bound at $r = 1, H = 3$ [(iii)]

Corollary 1 already refutes MAIS-O71 as stated. We now prove the matching upper bound on $Z_n$, using the interval scan bound and handling both $\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$ explicitly. This establishes the exact $-\frac{1}{3}\log\log n$ coefficient and rules out **every** integer multiplicity $m' \in \mathbb{Z}$, even if Display 2 were decoupled from Display 1.

**Theorem C (Evidence Upper Bound / Free-Energy Lower Bound at $r = 1, H = 3$) [(iii)].**
In the setting of Theorem A,
$$F_n - n S_n \;\ge\; \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1).$$
Equivalently, $Z_n = O_p\bigl(n^{-11/6}(\log n)^{1/3}\bigr)$.

*Proof.* By $S_3$ symmetry of $W$ and $f_w$, $Z_n = \frac{6}{\mathrm{vol}(W)} Z_n^{(<)}$, where $Z_n^{(<)}$ is the integral of $\exp(\langle \varepsilon, f_w\rangle_n - \frac{1}{2}\|f_w\|_n^2)$ over $W \cap \Omega_<$. Apply Lemma 1.1 to pass to coordinates $(a, t_1, c, S, B, \delta_1, \delta_2, \tilde{h})$ with Jacobian $\frac{1}{\delta_1 \delta_2}$. On $W \cap \Omega_<$, we have $a \in [\frac{2}{3}, \frac{4}{3}]^3$ (volume $\frac{8}{27}$, and $f_w$ does not depend on $a$), $-\frac{1}{2} \le t_1 < t_2 < t_3 \le \frac{1}{2}$ (so $\delta_1 + \delta_2 \le 1$), and $|\tilde{h}| \le \frac{4}{9}\min(\delta_1, \delta_2)$ (by Lemma 1.1(4), symmetrically in $\delta_1$ and $\delta_2$). Extending $(c, S, B)$ to all of $\mathbb{R}^3$ and dropping the remaining ball constraints can only increase the nonnegative integral:
$$Z_n^{(<)} \;\le\; \frac{8}{27}\int_{\mathcal{T}} \frac{dt_1\,d\delta_1\,d\delta_2}{\delta_1 \delta_2} \int_{|\tilde{h}| \le \frac{4}{9}\min(\delta_1, \delta_2)} d\tilde{h} \int_{\mathbb{R}^3} \exp\!\left(\langle\varepsilon, M + \tilde{h}\tau\rangle_n - \frac{1}{2}\|M + \tilde{h}\tau\|_n^2\right) dc\,dS\,dB,$$
where $\mathcal{T} := \{(t_1, \delta_1, \delta_2) : -\frac{1}{2} \le t_1,\; \delta_1 > 0,\; \delta_2 > 0,\; t_1 + \delta_1 + \delta_2 \le \frac{1}{2}\}$.

**Step 1: Exact empirical Gram–Schmidt decoupling of $M$ and $\tau$.** Take $n$ sufficiently large that $h\le1/32$ below and define the scale
$$\delta_+ \;:=\; n^{-1/3}(\log n)^{1/3} \;<\; 1, \qquad h \;:=\; \frac{\delta_+}{8}.$$
Fix $\eta \in (0, 1)$, set $K_0 := \sqrt{2\log(16/\eta)}$, and define the combined high-probability event
$$E_{\mathrm{good}}(K_0) \;:=\; E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h) \cap E_{\mathrm{max}}(K_0) \cap E_{\mathrm{scan}},$$
from Lemma 1.3. By Lemma 1.3(a), $\mathbb{P}(E_{\mathrm{max}}(K_0)^c) \le \eta/4$, and $\mathbb{P}(E_{\mathrm{end}}^c) + \mathbb{P}(E_{\mathrm{unif}}(h)^c) + \mathbb{P}(E_{\mathrm{scan}}^c) \le 6 e^{-n/5000} + 34 n^{1/3} e^{-\frac{1}{256} n^{2/3}(\log n)^{1/3}} + \frac{2}{n} \le \eta/4$ for all $n \ge N_0(\eta)$, so $\mathbb{P}(E_{\mathrm{good}}(K_0)^c) \le \eta/2$.

Assume $X^n \in E_{\mathrm{end}}$. For any $(t_1, \delta_1, \delta_2) \in \mathcal{T}$, Lemma 1.3(b) ensures $G_n^{\mathrm{mac}}(t_1, t_3) \succeq \frac{n}{15000} I_3$. Let $\alpha := G_n^{\mathrm{mac}}(t_1, t_3)^{-1} \sum_{i=1}^n \tau(X_i)\Phi(X_i) \in \mathbb{R}^3$ and $\tau_\perp := \tau - \alpha^\top \Phi$ be the $L^2(\mathbb{P}_n)$-orthogonal projection of $\tau$ onto $\mathrm{span}(\Phi)^\perp$. Substituting $\tilde{\theta} := (c, S, B)^\top + \tilde{h}\alpha$ (a translation of $\mathbb{R}^3$ with Jacobian $1$) gives $M + \tilde{h}\tau = \tilde{\theta}^\top \Phi + \tilde{h}\tau_\perp$ with $\langle \tilde{\theta}^\top \Phi, \tau_\perp\rangle_n = 0$. The Gaussian integral over $\tilde{\theta} \in \mathbb{R}^3$ evaluates exactly to
$$\frac{(2\pi)^{3/2}}{\sqrt{\det G_n^{\mathrm{mac}}(t_1, t_3)}}\exp\!\left(\frac{1}{2} (U_n^{\mathrm{mac}})^\top (G_n^{\mathrm{mac}})^{-1} U_n^{\mathrm{mac}}\right).$$
On $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$, we have $\det G_n^{\mathrm{mac}} \ge (n/15000)^3$ and $(U_n^{\mathrm{mac}})^\top (G_n^{\mathrm{mac}})^{-1} U_n^{\mathrm{mac}} \le \frac{15000}{n}\|U_n^{\mathrm{mac}}\|_2^2 \le 90000 K_0^2$ by Lemma 1.3(d). Setting $C_{\mathrm{mac}}(K_0) := \frac{8}{27}(30000\pi)^{3/2} e^{45000 K_0^2}$, we obtain pointwise on $E_{\mathrm{good}}(K_0)$:
$$Z_n^{(<)} \;\le\; C_{\mathrm{mac}}(K_0)\, n^{-3/2} \int_{\mathcal{T}} \frac{dt_1\,d\delta_1\,d\delta_2}{\delta_1 \delta_2} \int_{|\tilde{h}| \le \frac{4}{9}\min(\delta_1, \delta_2)} \exp\!\left(\tilde{h}\langle\varepsilon, \tau_\perp\rangle_n - \frac{1}{2}\tilde{h}^2 \|\tau_\perp\|_n^2\right) d\tilde{h}.$$

**Step 2: Explicit partitioning of $\mathcal{T}$ (covering both $\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$).**
For every $(t_1, \delta_1, \delta_2) \in \mathcal{T}$, define
$$\delta \;:=\; \max(\delta_1, \delta_2) \in (0, 1), \qquad u \;:=\; \frac{\min(\delta_1, \delta_2)}{\max(\delta_1, \delta_2)} \in (0, 1], \qquad u_{\max}(\delta) \;:=\; \left(\frac{\delta_+}{\delta}\right)^{3/2} = \sqrt{\frac{\log n}{n \delta^3}}.$$
Partition $\mathcal{T}$ into three disjoint regions, each explicitly decomposed as the disjoint union of its $\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$ halves:
- $\mathcal{R}_{1+2} := \{(t_1, \delta_1, \delta_2) \in \mathcal{T} : \delta \le \delta_+\}$;
- $\mathcal{R}_{3a} := \{(t_1, \delta_1, \delta_2) \in \mathcal{T} : \delta > \delta_+,\; u \le u_{\max}(\delta)\}$;
- $\mathcal{R}_{3b} := \{(t_1, \delta_1, \delta_2) \in \mathcal{T} : \delta > \delta_+,\; u > u_{\max}(\delta)\}$.

Note that on $\mathcal{T} \cap \{\delta_1 \le \delta_2\}$ we have $(\delta_1, \delta_2) = (u\delta, \delta)$ with $\frac{d\delta_1 d\delta_2}{\delta_1 \delta_2} = \frac{du\,d\delta}{u\delta}$, and on $\mathcal{T} \cap \{\delta_1 > \delta_2\}$ we have $(\delta_1, \delta_2) = (\delta, u\delta)$ with the exact same measure $\frac{d\delta_1 d\delta_2}{\delta_1 \delta_2} = \frac{du\,d\delta}{u\delta}$; in both halves $|\tilde{h}| \le \frac{4}{9} u\delta$ and $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$ (length $1$). Write $Z_n^{(<)} = Z_n(\mathcal{R}_{1+2}) + Z_n(\mathcal{R}_{3a}) + Z_n(\mathcal{R}_{3b})$.

**Step 3: Expectation bounds on $\mathcal{R}_{1+2}$ and $\mathcal{R}_{3a}$ (exact mean-$1$ identity).**
For $\mathcal{R} \in \{\mathcal{R}_{1+2}, \mathcal{R}_{3a}\}$, bound $\mathbf{1}_{E_{\mathrm{good}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}}}$ (which depends only on $X^n$) and take $\mathbb{E}_\varepsilon[\cdot \mid X^n]$. By Tonelli's theorem and the exact Gaussian MGF identity $\mathbb{E}_\varepsilon[\exp(\tilde{h}\langle\varepsilon, \tau_\perp\rangle_n - \frac{1}{2}\tilde{h}^2 \|\tau_\perp\|_n^2) \mid X^n] = 1$ (valid even if $\|\tau_\perp\|_n = 0$), integrating over $|\tilde{h}| \le \frac{4}{9} u\delta$ (length $\frac{8}{9} u\delta$) and summing both halves ($\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$, factor $2$) gives:
- On $\mathcal{R}_{1+2}$:
  $$\mathbb{E}_\varepsilon\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(\mathcal{R}_{1+2}) \mid X^n\right] \;\le\; C_{\mathrm{mac}}(K_0)\, n^{-3/2} \cdot 2 \int_{-1/2}^{1/2} dt_1 \int_0^{\delta_+} \int_0^1 \frac{8}{9} u\delta \cdot \frac{du\,d\delta}{u\delta} \;=\; \frac{16}{9} C_{\mathrm{mac}}(K_0)\, n^{-11/6} (\log n)^{1/3}.$$
- On $\mathcal{R}_{3a}$:
  $$\mathbb{E}_\varepsilon\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(\mathcal{R}_{3a}) \mid X^n\right] \;\le\; C_{\mathrm{mac}}(K_0)\, n^{-3/2} \cdot 2 \int_{\delta_+}^{1} \frac{8}{9}\left(\frac{\delta_+}{\delta}\right)^{3/2} d\delta \;\le\; \frac{32}{9} C_{\mathrm{mac}}(K_0)\, n^{-3/2} \delta_+ \;=\; \frac{32}{9} C_{\mathrm{mac}}(K_0)\, n^{-11/6} (\log n)^{1/3},$$
  since $\int_{\delta_+}^{1} \delta^{-3/2}\,d\delta \le 2 \delta_+^{-1/2}$.

**Step 4: Uniform norm and elementary scan bound on $\mathcal{R}_{3b}$ (both $\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$).**
Fix any $(t_1, \delta_1, \delta_2) \in \mathcal{R}_{3b}$, so $\delta = \max(\delta_1, \delta_2) > \delta_+ = 8 h$.
1. *Uniform lower bound on $\|\tau_\perp\|_n^2$:* If $\delta_2 = \delta$, let $I_{\mathrm{half}} := [t_2, t_2 + \delta/2] \subset [t_2, t_3]$; if $\delta_1 = \delta$, let $I_{\mathrm{half}} := [t_2 - \delta/2, t_2] \subset [t_1, t_2]$. In either case, $|I_{\mathrm{half}}| = \delta/2 > 4 h$ and $\tau(x) \ge \frac{1}{2}$ everywhere on $I_{\mathrm{half}}$. On $E_{\mathrm{unif}}(h)$, Lemma 1.3(c) gives $N(I_{\mathrm{half}}) \ge \frac{1}{8} n (\delta/2) = \frac{1}{16} n \delta$, so $\|\tau\|_n^2 \ge \frac{1}{4} N(I_{\mathrm{half}}) \ge \frac{1}{64} n \delta$. Combined with Lemma 1.3(b) on $E_{\mathrm{end}}$,
   $$\|\tau_\perp\|_n^2 \;\ge\; \frac{1}{1809} \|\tau\|_n^2 \;\ge\; c_\perp n \delta, \qquad c_\perp \;:=\; \frac{1}{115776},$$
   uniformly over all $(t_1, \delta_1, \delta_2) \in \mathcal{R}_{3b}$ (including as $u \to 0$ and for both $\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$).
2. *Uniform bound on $\hat{Z}_4 := \langle \varepsilon, \tau_\perp\rangle_n / \|\tau_\perp\|_n$:* Write $\langle \varepsilon, \tau_\perp\rangle_n = \langle \varepsilon, \tau\rangle_n - \langle \varepsilon, \alpha^\top \Phi\rangle_n$.
   - For the raw tent $\tau(x) = r_L(x; t_1, t_2) + r_R(x; t_2, t_3)$, Lemma 1.3(d) on $E_{\mathrm{scan}}$ gives
     $$|\langle \varepsilon, \tau\rangle_n| \;\le\; \sqrt{6\log n}\,\Bigl(\sqrt{N([t_1, t_2])} + \sqrt{N((t_2, t_3])}\Bigr) \;\le\; \sqrt{12\log n}\,\sqrt{N([t_1, t_3])}.$$
     Since $|[t_1, t_3]| = \delta_1 + \delta_2 \in [\delta, 2\delta]$ and $\delta > 8 h \ge 8 h'$, covering $[t_1, t_3]$ by cells of $E_{\mathrm{unif}}(h)$ gives $N([t_1, t_3]) \le (2\delta/h' + 2) n h' = 2 n\delta + 2 n h' \le 2 n\delta + \frac{1}{4} n\delta < 3 n\delta$. Thus $|\langle \varepsilon, \tau\rangle_n| / \|\tau_\perp\|_n \le \sqrt{36\log n}/\sqrt{c_\perp} = 6\sqrt{115776}\,\sqrt{\log n} < 2042 \sqrt{\log n}$.
   - For the projection subtraction $\alpha^\top \Phi$, Cauchy–Schwarz in $\mathbb{R}^n$ gives $|\langle \varepsilon, \alpha^\top \Phi\rangle_n| = |\alpha^\top U_n^{\mathrm{mac}}| \le \|(G_n^{\mathrm{mac}})^{-1/2} U_n^{\mathrm{mac}}\|_2 \cdot \|\alpha^\top \Phi\|_n$. Since $\|\alpha^\top \Phi\|_n \le \|\tau\|_n$ and on $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$ we have $\|(G_n^{\mathrm{mac}})^{-1/2} U_n^{\mathrm{mac}}\|_2 \le 300 K_0$, Lemma 1.3(b) gives
     $$\frac{|\langle \varepsilon, \alpha^\top \Phi\rangle_n|}{\|\tau_\perp\|_n} \;\le\; 300 K_0 \frac{\|\tau\|_n}{\|\tau_\perp\|_n} \;\le\; 300\sqrt{1809}\,K_0 \;<\; 12760 K_0.$$
   Combining both pieces, since $\sqrt{\log n} > 1$ for $n \ge 10$, we have on $E_{\mathrm{good}}(K_0)$:
   $$\sup_{(t_1, \delta_1, \delta_2) \in \mathcal{R}_{3b}} |\hat{Z}_4(t_1, \delta_1, \delta_2)| \;\le\; A_n(K_0) \;:=\; (2042 + 12760 K_0)\sqrt{\log n}.$$

3. *Truncated expectation on $\mathcal{R}_{3b}$:* Extending the $\tilde{h}$-integral to $\mathbb{R}$ gives $\int_{|\tilde{h}| \le \frac{4}{9} u\delta} \exp(\tilde{h}\langle\varepsilon, \tau_\perp\rangle_n - \frac{1}{2}\tilde{h}^2 \|\tau_\perp\|_n^2)\,d\tilde{h} \le \frac{\sqrt{2\pi}}{\|\tau_\perp\|_n} e^{\frac{1}{2}\hat{Z}_4^2}$. Since $\mathbf{1}_{E_{\mathrm{good}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h)} \mathbf{1}_{\{|\hat{Z}_4(t_1, \delta_1, \delta_2)| \le A_n(K_0)\}}$ for every $(t_1, \delta_1, \delta_2) \in \mathcal{R}_{3b}$, and conditional on $X^n \in E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h)$ we have $\hat{Z}_4 \sim \mathcal{N}(0, 1)$, Tonelli's theorem and the exact truncated Gaussian identity $\mathbb{E}[e^{Z^2/2}\mathbf{1}_{|Z| \le A}] = \sqrt{\frac{2}{\pi}} A$ yield
   $$\mathbb{E}_\varepsilon\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(\mathcal{R}_{3b}) \mid X^n\right] \;\le\; \mathbf{1}_{E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h)} C_{\mathrm{mac}}(K_0)\, n^{-3/2} \int_{\mathcal{R}_{3b}} \frac{\sqrt{2\pi}}{\sqrt{c_\perp n \delta}} \cdot \sqrt{\frac{2}{\pi}} A_n(K_0)\,\frac{dt_1\,d\delta_1\,d\delta_2}{\delta_1 \delta_2}.$$
   Evaluating the integral over both halves ($\delta_1 \le \delta_2$ and $\delta_1 > \delta_2$, factor $2$) with $s := \delta / \delta_+ \in [1, 1/\delta_+]$:
   $$\int_{\mathcal{R}_{3b}} \frac{dt_1\,d\delta_1\,d\delta_2}{\delta^{1/2}\delta_1 \delta_2} \;\le\; 2 \int_{\delta_+}^{1} \delta^{-3/2}\left(\int_{u_{\max}(\delta)}^{1} \frac{du}{u}\right) d\delta \;=\; 3 \int_{\delta_+}^{1} \delta^{-3/2}\log\left(\frac{\delta}{\delta_+}\right) d\delta \;\le\; 3 \delta_+^{-1/2}\int_1^\infty s^{-3/2}\log s\,ds \;=\; 12\,\delta_+^{-1/2},$$
   using $\int_1^\infty s^{-3/2}\log s\,ds = [-2 s^{-1/2}\log s]_1^\infty + 2\int_1^\infty s^{-3/2}\,ds = 4$. Therefore,
   $$\mathbb{E}\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(\mathcal{R}_{3b})\right] \;\le\; \frac{24}{\sqrt{c_\perp}}\,C_{\mathrm{mac}}(K_0)(2042 + 12760 K_0)\, n^{-2}(\log n)^{1/2} \delta_+^{-1/2} \;=\; C_{3b}(K_0)\, n^{-11/6} (\log n)^{1/3}.$$

**Step 5: Markov's inequality.** Summing Steps 3 and 4 across $\mathcal{R}_{1+2}, \mathcal{R}_{3a}, \mathcal{R}_{3b}$ yields $\mathbb{E}[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n] \le C_{\mathrm{tot}}(K_0)\, n^{-11/6}(\log n)^{1/3}$. Setting $M_\eta := \frac{2}{\eta} C_{\mathrm{tot}}(K_0)$, Markov's inequality gives for all $n \ge N_0(\eta)$:
$$\mathbb{P}\!\left(Z_n > M_\eta\, n^{-11/6}(\log n)^{1/3}\right) \;\le\; \mathbb{P}(E_{\mathrm{good}}(K_0)^c) + \frac{\mathbb{E}[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n]}{M_\eta\, n^{-11/6}(\log n)^{1/3}} \;\le\; \frac{\eta}{2} + \frac{\eta}{2} \;=\; \eta.$$
Taking $-\log$ gives $F_n - n S_n \ge \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$. $\square$

---

**Corollary 2 (Exact Free-Energy Expansion & Failure of Display 2 Alone for Every Integer $m'$) [(iii)].**
In the setting of Theorem A,
$$F_n \;=\; n S_n + \frac{11}{6}\log n - \frac{1}{3}\log\log n + O_p(1).$$
Consequently, there is **no** pair $(\lambda', m') \in \mathbb{R} \times \mathbb{Z}$ for which $F_n = n S_n + \lambda'\log n - (m' - 1)\log\log n + O_p(1)$.

*Proof.* The two-sided expansion follows immediately from Theorems B and C. For any $(\lambda', m') \in \mathbb{R} \times \mathbb{Z}$,
$$(F_n - n S_n) - \bigl(\lambda'\log n - (m' - 1)\log\log n\bigr) \;=\; \left(\frac{11}{6} - \lambda'\right)\log n + \left(m' - \frac{4}{3}\right)\log\log n + O_p(1).$$
If $\lambda' \neq \frac{11}{6}$, the leading $\log n$ term diverges; if $\lambda' = \frac{11}{6}$, then $m' - \frac{4}{3} \neq 0$ (as $m' \in \mathbb{Z}$), so the $\log\log n$ term diverges. In both cases the remainder fails to be $O_p(1)$. $\square$

---

## 5. Theorem D: Complete General-$H$ Law for All $H \ge 3$ [(iii)]

We now establish the exact volume and free-energy asymptotics for **every** width $H \ge 3$ on the standard local ball $W = \overline{B_{1/3}(w^0)}$ around $w^0 = (0, (1, 0, 0)^H)$.

**Theorem D (General-$H$ Sublevel Volume and Free-Energy Law for All $H \ge 3$) [(iii)].**
Fix any integer $H \ge 3$, $r = 1$, $w^0 = (0, (1, 0, 0)^H) \in \mathbb{R}^{3H+1}$, $W = \overline{B_{1/3}(w^0)}$, and $\varphi \equiv 1/\mathrm{vol}(W)$. Then:
1. *(Display 1)* There exists a constant $c_0(H) \in (0, \infty)$ such that as $\varepsilon \downarrow 0$,
   $$\int_{\{K \le \varepsilon\} \cap W} \varphi(w)\,dw \;=\; c_0(H)\,\varepsilon^{\frac{2H + 5}{6}}\bigl(1 + o(1)\bigr),$$
   so Display 1 holds with the uniquely determined pair $(\lambda_{\mathrm{vol}}(H), m_{\mathrm{vol}}(H)) = \bigl(\tfrac{2H + 5}{6},\; 1\bigr)$.
2. *(Exact two-sided free-energy expansion)* As $n \to \infty$,
   $$F_n \;=\; n S_n + \frac{2H + 5}{6}\log n - \frac{H - 2}{3}\log\log n + O_p(1).$$

Consequently the paired claim fails for every $H\ge3$ in this family. Display 1 forces $m_{\mathrm{vol}}=1$. Display 2 alone would require $m'=1+(H-2)/3=(H+1)/3$, which is an integer exactly for $H\equiv2\pmod3$. In that case it differs from the volume multiplicity.

*Proof.* We prove Part 1 (Display 1), Part 2a (evidence lower bound), and Part 2b (evidence upper bound) in turn.

### Part D.1: Proof of Display 1 for All $H \ge 3$

By $S_H$ symmetry, $\mathrm{vol}(\{K \le \varepsilon\} \cap W) = H!\,\mathrm{vol}(\{K \le \varepsilon\} \cap W \cap \Omega_<)$. Pass to the coordinates $(a, t_1, c, S, B, \delta_1, \dots, \delta_{H-1}, h_2, \dots, h_{H-1})$ of Lemma 1.1 (Jacobian $\prod_{j=1}^{H-1} \delta_j^{-1}$) and rescale:
$$(c, S, B) = \varepsilon^{1/2}(\hat{c}, \hat{S}, \hat{B}), \qquad \delta_j = \varepsilon^{1/3} x_j \;\;(1 \le j \le H-1), \qquad h_k = \varepsilon^{1/3} y_k \;\;(2 \le k \le H-1),$$
with $y_1 := y_H := 0$. Write $\mathcal U_H=(0,\infty)^H\times[-1/2,1/2]\times\mathbb R^3\times(0,\infty)^{H-1}\times\mathbb R^{H-2}$ for the rescaled integration domain and $A_\varepsilon^{(H)}$ for the constraints $w_\varepsilon\in W$, $K(w_\varepsilon)\le\varepsilon$. The Jacobian contributes the power
$$\varepsilon^{3/2}\cdot \frac{(\varepsilon^{1/3})^{(H-1) + (H-2)}}{(\varepsilon^{1/3})^{H-1}} \;=\; \varepsilon^{\frac{3}{2} + \frac{H-2}{3}} \;=\; \varepsilon^{\frac{2H + 5}{6}},$$
yielding
$$\frac{\mathrm{vol}(\{K \le \varepsilon\} \cap W)}{\varepsilon^{(2H+5)/6}} \;=\; H! \int_{\mathcal{U}_H} \mathbf{1}_{A_\varepsilon^{(H)}}(a, t_1, \hat{c}, \hat{S}, \hat{B}, x, y)\,\frac{da\,dt_1\,d\hat{c}\,d\hat{S}\,d\hat{B}\,dx\,dy}{\prod_{j=1}^{H-1} x_j}.$$

**Uniform $L^1$ dominating function via Fubini and AM–GM.** For every point in $A_\varepsilon^{(H)}$:
- $a \in [\frac{2}{3}, \frac{4}{3}]^H$, $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$, and (by Lemma 1.2) $\hat{c}, \hat{S}, \hat{B} \in [-\sqrt{3072}, \sqrt{3072}]$ and $\sum_{j=1}^{H-1} x_j (y_j^2 + y_{j+1}^2) \le 216$.
- By Lemma 1.1(4), for every $j \in \{1, \dots, H-1\}$, $|y_{j+1} - y_j| \le C_H x_j$ uniformly in $\varepsilon$, where $C_H := \frac{4(H-2)}{9}$.

Hence $\mathbf{1}_{A_\varepsilon^{(H)}} / \prod_{j=1}^{H-1} x_j \le g_H$, where $g_H$ restricts $(a, t_1, \hat{c}, \hat{S}, \hat{B})$ to the compact box above and restricts $(x, y)$ to the set where, for every $j \in \{1, \dots, H-1\}$,
$$\frac{|y_{j+1} - y_j|}{C_H} \;\le\; x_j \;\le\; \frac{216}{y_j^2 + y_{j+1}^2}.$$
To prove $g_H \in L^1$, integrate out $(x_1, \dots, x_{H-1})$ **first** for fixed $(y_2, \dots, y_{H-1})$ using Tonelli's theorem. Set $M_H := 216 C_H$ and $R_0 := M_H^{1/3}$. First observe that the feasibility condition $|y_{j+1} - y_j|(y_j^2 + y_{j+1}^2) \le M_H$ for all $j = 1, \dots, H-1$ forces **compactness in $y$**: since $y_1 = 0$, induction on $k = 1, \dots, H-2$ shows $|y_{k+1}| \le |y_k| + R_0$ (for if $|y_{k+1}| > |y_k| + R_0$, then $|y_{k+1} - y_k| > R_0$ and $y_{k+1}^2 > R_0^2$, so $|y_{k+1} - y_k|(y_k^2 + y_{k+1}^2) > R_0^3 = M_H$, contradiction). Hence $|y_k| \le H R_0 =: R_H$ for all $k = 2, \dots, H-1$. Integrating each $\frac{dx_j}{x_j}$ between $|y_{j+1} - y_j|/C_H$ and $216/(y_j^2 + y_{j+1}^2)$ gives
$$\int_{(0, \infty)^{H-1}} \mathbf{1}_{\{\forall j:\; \frac{|y_{j+1}-y_j|}{C_H} \le x_j \le \frac{216}{y_j^2 + y_{j+1}^2}\}}\,\frac{dx_1 \cdots dx_{H-1}}{x_1 \cdots x_{H-1}} \;\le\; \prod_{j=1}^{H-1} \log_+\!\left(\frac{M_H}{|y_{j+1} - y_j|(y_j^2 + y_{j+1}^2)}\right).$$
By the AM–GM inequality $\prod_{j=1}^{H-1} \alpha_j \le \frac{1}{H-1}\sum_{j=1}^{H-1} \alpha_j^{H-1}$, the right-hand side is bounded by $\frac{1}{H-1}\sum_{j=1}^{H-1} L_j(y)^{H-1}$ where $L_j(y) := \log_+\!\bigl(\frac{M_H}{|y_{j+1}-y_j|(y_j^2+y_{j+1}^2)}\bigr)$. For $j = 1$ (and symmetrically $j = H-1$), $L_1(y) = \log_+(M_H / |y_2|^3)$, which has finite $(H-1)$-th power integral on $[-R_H, R_H]$. For $2 \le j \le H-2$, using $\log_+(AB) \le \log_+(A) + \log_+(B)$ and $(u + v)^{H-1} \le 2^{H-1}(u^{H-1} + v^{H-1})$,
$$L_j(y)^{H-1} \;\le\; 2^{H-1}\left[\left(\log_+\frac{\sqrt{M_H}}{|y_{j+1} - y_j|}\right)^{H-1} + \left(\log_+\frac{\sqrt{M_H}}{y_j^2 + y_{j+1}^2}\right)^{H-1}\right],$$
both terms of which are integrable on $(y_j, y_{j+1}) \in [-R_H, R_H]^2$ (by $w = y_{j+1} - y_j$ for the first and polar coordinates $r^2 = y_j^2 + y_{j+1}^2$ for the second). Hence $g_H \in L^1(\mathcal{U}_H)$.

**Pointwise limit and DCT.** As $\varepsilon \downarrow 0$, for every fixed $(a, t_1, \hat{c}, \hat{S}, \hat{B}, x, y) \in \mathcal{U}_H$, $s_1 \to y_2/x_1$, $s_k = \frac{y_{k+1}-y_k}{x_k} - \frac{y_k-y_{k-1}}{x_{k-1}}$ ($2 \le k \le H-1$), $s_H \to +y_{H-1}/x_{H-1}$, so $\|w_\varepsilon - w^0\|_2^2 \to D_0^{(H)}(a, t_1, x, y)$, and $K(w_\varepsilon)/\varepsilon \to K_0^{(H)} := K_{\mathrm{mac}}(\hat{c}, \hat{S}, \hat{B}; t_1) + \frac{1}{12}\sum_{j=1}^{H-1} x_j(y_j^2 + y_j y_{j+1} + y_{j+1}^2)$ (the cross term is $O(\varepsilon^{1/6}) \to 0$). Since the coefficient of $y_2^2$ in $D_0^{(H)}$ is at least $\frac{1}{a_1^2 x_1^2} + \frac{1}{a_2^2}(\frac{1}{x_1} + \frac{1}{x_2})^2 > 0$ and $K_{\mathrm{mac}}$ is positive definite in $(\hat{c}, \hat{S}, \hat{B})$, the boundary $\{D_0^{(H)} = \frac{1}{9}\} \cup \{K_0^{(H)} = 1\}$ has measure $0$. The limit set $\{D_0^{(H)} < \frac{1}{9},\; K_0^{(H)} < 1\}$ is open and contains $((1,\dots,1), 0, 0, 0, 0, (1,\dots,1), (0,\dots,0))$. By DCT, $\mathrm{vol}(\{K \le \varepsilon\} \cap W)/\varepsilon^{(2H+5)/6} \to C_{\mathrm{vol}}(H) \in (0, \infty)$, proving Part 1 with $c_0(H) := C_{\mathrm{vol}}(H)/\mathrm{vol}(W)$.

---

### Part D.2: Proof of Evidence Lower Bound ($F_n - n S_n \le \frac{2H+5}{6}\log n - \frac{H-2}{3}\log\log n + O_p(1)$)

On $\Omega_<$, change variables from $(a, t_1, c, S, B, \delta_1, \dots, \delta_{H-1}, h_2, \dots, h_{H-1})$ to $(a, t_1, c, S, B, \delta, u_1, \dots, u_{H-2}, \tilde{y}_2, \dots, \tilde{y}_{H-1})$ via
$$\delta := \delta_{H-1}, \qquad u_j := \frac{\delta_j}{\delta} \;\;(1 \le j \le H-2), \qquad \tilde{y}_k := \frac{h_k}{\delta} \;\;(2 \le k \le H-1).$$
The absolute Jacobian from $(u,\delta,\tilde y)$ to the gaps and heights is $\delta^{H-2} \cdot \delta^{H-2} = \delta^{2H-4}$, so multiplying by $\prod_{j=1}^{H-1} \delta_j^{-1} = \delta^{-(H-1)}\prod_{j=1}^{H-2} u_j^{-1}$ gives total Jacobian
$$J_{\mathrm{tot}}(u, \delta) \;=\; \frac{\delta^{H-3}}{\prod_{j=1}^{H-2} u_j}.$$
Set $\delta_- := n^{-1/3}$, $\delta_+ := 2 n^{-1/3}(\log n)^{1/3}$, $r_H := \frac{1}{100 H}$, and define the sub-box $B_n(H)$ by:
- $a_j \in [1 - \frac{1}{10 H},\; 1 + \frac{1}{10 H}]$ ($1 \le j \le H$),
- $t_1 \in [-\frac{1}{10 H},\; \frac{1}{10 H}]$,
- $u_j \in [\frac{1}{4}, \frac{1}{2}]$ ($1 \le j \le H-2$),
- $\tilde{y}_k \in [-r_H, r_H]$ ($2 \le k \le H-1$),
- $c, S, B \in [-n^{-1/2}, n^{-1/2}]$,
- $\delta \in [\delta_-, \delta_+]$.

**Sub-box inclusion $B_n(H) \subset W$.** For all $n$ large enough that $\delta_+ \le \frac{1}{10 H^2}$, $\delta_+ \ge 2\delta_-$, and $2 n^{-1/6} \le r_H$:
- $c^2 \le n^{-1} < 10^{-4}$ and $\sum_{j=1}^H (a_j - 1)^2 \le \frac{1}{100 H} \le \frac{1}{300}$.
- For every $j$, $|t_j| \le \frac{1}{10 H} + (1 + \frac{H-2}{2})\delta_+ \le \frac{1}{10 H} + \frac{H}{2}\cdot\frac{1}{10 H^2} = \frac{3}{20 H}$, and $a_j \le \frac{11}{10}$, so $\sum_{j=1}^H b_j^2 \le H (\frac{11}{10})^2 (\frac{3}{20 H})^2 < \frac{3}{100 H} \le \frac{1}{100}$.
- By Lemma 1.1(3), for $2 \le k \le H-1$, $|s_k| \le 4(2 r_H) + 4(2 r_H) = 16 r_H = \frac{16}{100 H}$ (with $u_{H-1} := 1$); and since $\Delta = (1 + \sum_{j=1}^{H-2} u_j)\delta \ge n^{-1/3}$, $|m_0| \le 2 n^{-1/6} \le r_H$, so $|s_1|, |s_H| \le 5 r_H < \frac{16}{100 H}$. Since $a_j \ge \frac{9}{10}$, $\sum_{j=1}^H v_j^2 \le H (\frac{10}{9})^2 (\frac{16}{100 H})^2 < \frac{0.04}{H} < 0.02$.

Thus $\|w - w^0\|_2^2 < 0.0001 + 0.0034 + 0.01 + 0.02 < 0.04 < \frac{1}{9}$, so $B_n(H) \subset W$.

**Decoupling and conditional Chebyshev bound.** On $B_n(H)$, the bump $b = \sum_{k=2}^{H-1} \delta \tilde{y}_k \Lambda_k$ is supported on $[t_1, t_H]$ of length $\Delta \le \frac{H}{2}\delta_+$ and satisfies $|b(x)| \le r_H \delta_+$ everywhere. Apply Lemma 1.3 with $h := \delta_+ / 8$ and $K_0 := \sqrt{2\log(16/\eta)}$. On $E_{\mathrm{max}}(K_0) \cap E_{\mathrm{unif}}(h)$:
- $\mathrm{Macro} = \langle\varepsilon, M\rangle_n - \frac{1}{2}\|M\|_n^2 \ge -4 K_0 - \frac{9}{2}$.
- Since $\Delta \le \frac{H}{2}\delta_+$, covering $[t_1, t_H]$ by cells of length $h' \in (\frac{h}{2}, h]$ yields $N([t_1, t_H]) \le (\frac{H\delta_+}{2 h'} + 2) n h' = \frac{H}{2} n\delta_+ + 2 n h' \le (\frac{H}{2} + \frac{1}{4}) n\delta_+ \le H n \delta_+$ (as $H \ge 3$), so $|\langle M, b\rangle_n| \le (3 n^{-1/2})(r_H \delta_+)(H n \delta_+) = \frac{3}{100} n^{1/2}\delta_+^2 = O(n^{-1/6}(\log n)^{2/3}) \le 1$ for all sufficiently large $n$.

Define
$$g(t_1; u, \delta) := \int_{[-r_H, r_H]^{H-2}} \exp\!\left(\langle\varepsilon, b\rangle_n - \frac{1}{2}\|b\|_n^2\right) d\tilde{y}, \quad G_n(u, \delta) := \int_{-\frac{1}{10 H}}^{\frac{1}{10 H}} g(t_1; u, \delta)\,dt_1, \quad J_n := \int_{\delta_-}^{\delta_+} \int_{[\frac{1}{4}, \frac{1}{2}]^{H-2}} G_n(u, \delta)\,\frac{\delta^{H-3}}{\prod_{j=1}^{H-2} u_j}\,du\,d\delta.$$
Conditional on $X^n \in E_{\mathrm{unif}}(h)$:
- *Mean:* $\mathbb{E}_\varepsilon[G_n(u, \delta) \mid X^n] = \mu_H := \frac{1}{5 H}(2 r_H)^{H-2}$, hence
  $$\mathbb{E}_\varepsilon[J_n \mid X^n] \;=\; \mu_H (\log 2)^{H-2}\,\frac{\delta_+^{H-2} - \delta_-^{H-2}}{H-2} \;\ge\; c_H'\,\delta_+^{H-2} \;=\; c_H' 2^{H-2}\, n^{-\frac{H-2}{3}}(\log n)^{\frac{H-2}{3}}$$
  (using $\delta_+ \ge 2\delta_-$ so $\delta_+^{H-2} - \delta_-^{H-2} \ge \frac{1}{2}\delta_+^{H-2}$).
- *Variance:* Whenever $|t_1 - t_1'| > \frac{H}{2}\delta$, $\mathrm{supp}(b_{t_1})$ and $\mathrm{supp}(b_{t_1'})$ are disjoint, so $\mathrm{Cov}_\varepsilon(g(t_1), g(t_1') \mid X^n) = 0$. When $|t_1 - t_1'| \le \frac{H}{2}\delta$,
  $$\mathbb{E}_\varepsilon[g(t_1)^2 \mid X^n] = \iint_{([-r_H, r_H]^{H-2})^2} e^{\langle b_{\tilde{y}}, b_{\tilde{y}'}\rangle_n}\,d\tilde{y}\,d\tilde{y}' \le (2 r_H)^{2(H-2)} \exp\!\left(\max_{\tilde{y}}\|b_{\tilde{y}}\|_n^2\right).$$
  On $E_{\mathrm{unif}}(h)$, $\|b_{\tilde{y}}\|_n^2 \le r_H^2 \delta_+^2 \cdot H n \delta_+ = H \cdot \frac{1}{10^4 H^2}\cdot 8\log n = \frac{8}{10^4 H}\log n < \frac{1}{10}\log n$, so $\exp(\max \|b_{\tilde{y}}\|_n^2) \le n^{0.1}$. Integrating over $|t_1 - t_1'| \le \frac{H}{2}\delta$ (area at most $\frac{1}{5 H}\cdot H\delta_+ = \frac{1}{5}\delta_+$) gives $\mathrm{Var}_\varepsilon(G_n(u, \delta) \mid X^n) \le \frac{1}{5}(2 r_H)^{2(H-2)}\,\delta_+ n^{0.1}$. By Cauchy–Schwarz over $(u, \delta)$ against the positive measure $\frac{\delta^{H-3}}{\prod u_j} du\,d\delta$,
  $$\frac{\mathrm{Var}_\varepsilon(J_n \mid X^n)}{(\mathbb{E}_\varepsilon[J_n \mid X^n])^2} \;\le\; \frac{\sup_{u, \delta} \mathrm{Var}_\varepsilon(G_n(u, \delta) \mid X^n)}{\mu_H^2} \;\le\; 5 H^2 \delta_+ n^{0.1} \;=\; 10 H^2 n^{-7/30}(\log n)^{1/3} \;\longrightarrow\; 0.$$

By conditional Chebyshev and the union bound on $E_{\mathrm{max}}(K_0) \cap E_{\mathrm{unif}}(h) \cap \{J_n \ge \frac{1}{2}\mathbb{E}_\varepsilon[J_n \mid X^n]\}$, for all sufficiently large $n$ we obtain with probability at least $1 - \eta$:
$$Z_n \;\ge\; c(H, \eta)\, n^{-3/2} \cdot n^{-\frac{H-2}{3}}(\log n)^{\frac{H-2}{3}} \;=\; c(H, \eta)\, n^{-\frac{2H+5}{6}}(\log n)^{\frac{H-2}{3}}.$$

---

### Part D.3: Proof of Evidence Upper Bound ($F_n - n S_n \ge \frac{2H+5}{6}\log n - \frac{H-2}{3}\log\log n + O_p(1)$)

By $S_H$ symmetry, $Z_n = \frac{H!}{\mathrm{vol}(W)} Z_n^{(<)}$. Pass to Lemma 1.1's coordinates $(a, t_1, c, S, B, \delta, h)$ on $W \cap \Omega_<$, where $a \in [\frac{2}{3}, \frac{4}{3}]^H$ (volume $(\frac{2}{3})^H$), $\delta = (\delta_1, \dots, \delta_{H-1}) \in (0, 1)^{H-1}$, $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$, and $h = (h_2, \dots, h_{H-1}) \in \mathcal{H}(\delta) := \{h : |h_{j+1} - h_j| \le C_H \delta_j \;\forall 1 \le j \le H-1\}$ (with $h_1 = h_H = 0$, $C_H = \frac{4(H-2)}{9}$, by Lemma 1.1(4)).

**Step 1: High-probability event at mesh $h_{\mathrm{grid}} := \frac{1}{32}\sqrt{\frac{\log n}{n}}$.**
Set $\delta_+ := n^{-1/3}(\log n)^{1/3}$ and $h_{\mathrm{grid}} := \frac{1}{32}\sqrt{\frac{\log n}{n}}$. Let $K_0 := \sqrt{2\log(16/\eta)}$ and define
$$E_{\mathrm{good}}(K_0) \;:=\; E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h_{\mathrm{grid}}) \cap E_{\mathrm{max}}(K_0) \cap E_{\mathrm{scan}}.$$
By Lemma 1.3(a), since $M_{h_{\mathrm{grid}}} \le 65\sqrt{n}$ and $n h_{\mathrm{grid}} / 32 = \frac{1}{1024}\sqrt{n\log n}$, we have $\mathbb{P}(E_{\mathrm{unif}}(h_{\mathrm{grid}})^c) \le 130\sqrt{n}\,e^{-\frac{1}{1024}\sqrt{n\log n}} \to 0$, so $\mathbb{P}(E_{\mathrm{good}}(K_0)^c) \le \eta/2$ for all $n \ge N_0(\eta)$.

Applying exact empirical Gram–Schmidt of $b = \sum_{k=2}^{H-1} h_k \Lambda_k$ against $\mathrm{span}(\Phi)$ (exactly as in Theorem C Step 1) and integrating $\tilde{\theta} \in \mathbb{R}^3$ gives, pointwise on $E_{\mathrm{good}}(K_0)$,
$$Z_n^{(<)} \;\le\; C_{\mathrm{mac}}(H, K_0)\, n^{-3/2} \int_{[-1/2, 1/2]} dt_1 \int_{\{\delta_j>0:\,t_1+\sum_j\delta_j\le1/2\}} \frac{d\delta_1 \cdots d\delta_{H-1}}{\delta_1 \cdots \delta_{H-1}} \int_{\mathcal{H}(\delta)} \exp\!\left(\langle\varepsilon, b_\perp(h)\rangle_n - \frac{1}{2}\|b_\perp(h)\|_n^2\right) dh_2 \cdots dh_{H-1}.$$
We keep this knot constraint whenever applying a bound to an empirical Gram matrix or an interval count. After taking conditional expectations we may extend a nonnegative deterministic bound on the gaps to the whole cube.

**Step 2: Tight-edge spanning-forest partition of $(0, 1)^{H-1}$.**
For each $\delta \in (0, 1)^{H-1}$ and each interior vertex $k \in \{2, \dots, H-1\}$, define
$$D_k(\delta) \;:=\; \max(\delta_{k-1}, \delta_k, \delta_+) \in [\delta_+, 1], \qquad \sigma_k(\delta) \;:=\; \sqrt{\frac{\log n}{n D_k(\delta)}} \;=\; \delta_+^{3/2} D_k(\delta)^{-1/2} \;\in\; \left[\sqrt{\frac{\log n}{n}},\; \delta_+\right].$$
Set $\sigma_1 := \sigma_H := +\infty$, and for each edge $j \in \{1, \dots, H-1\}$ define the threshold $\tau_j(\delta) := \min(\sigma_j(\delta), \sigma_{j+1}(\delta)) \in [\sqrt{\frac{\log n}{n}}, \delta_+]$. Partition $(0, 1)^{H-1}$ into the $2^{H-1}$ disjoint regions $R_T := \{\delta \in (0, 1)^{H-1} : T(\delta) = T\}$ indexed by the set of **tight edges**
$$T(\delta) \;:=\; \bigl\{j \in \{1, \dots, H-1\} : \delta_j < \tau_j(\delta)\bigr\}, \qquad L(\delta) \;:=\; \{1, \dots, H-1\} \setminus T(\delta).$$
Observe two immediate properties:
1. Every tight edge $j \in T$ satisfies $\delta_j < \tau_j(\delta) \le \delta_+$.
2. Every **loose edge** $j \in L$ satisfies $\delta_j \ge \tau_j(\delta) \ge \sqrt{\frac{\log n}{n}} = 32 h_{\mathrm{grid}}$.

**Case 1: $T = \{1, \dots, H-1\}$ ($L = \emptyset$).**
Here every $\delta_j < \delta_+$. For fixed $\delta \in R_{\{1,\dots,H-1\}}$, pick an index $j^*$ maximizing $\delta_j$. Deleting constraint $j^*$ from $\mathcal{H}(\delta)$ leaves $H - 2$ independent edge-difference bounds $|h_{j+1} - h_j| \le C_H \delta_j$ ($j \neq j^*$) forming a spanning path from $h_1 = 0$ and $h_H = 0$ to all $H - 2$ interior heights with unit Jacobian; hence $\mathrm{vol}_{H-2}(\mathcal{H}(\delta)) \le (2 C_H)^{H-2} \prod_{j \neq j^*} \delta_j = (2 C_H)^{H-2} \frac{\prod_{j=1}^{H-1} \delta_j}{\max_j \delta_j}$. Bounding $\mathbf{1}_{E_{\mathrm{good}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}}}$ and taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ (exact mean $1$ for every $h$) yields
$$\mathbb{E}\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(R_{\{1,\dots,H-1\}})\right] \;\le\; C_{\mathrm{mac}}(H, K_0)(2 C_H)^{H-2}\, n^{-3/2} \int_{(0, \delta_+)^{H-1}} \frac{d\delta}{\max_j \delta_j} \;=\; \frac{H-1}{H-2} C_{\mathrm{mac}}(H, K_0)(2 C_H)^{H-2}\, n^{-3/2} \delta_+^{H-2},$$
which equals $O\bigl(n^{-\frac{2H+5}{6}} (\log n)^{\frac{H-2}{3}}\bigr)$.

**Case 2: $T \subsetneq \{1, \dots, H-1\}$ ($L \neq \emptyset$).**
Write $L = \{j_1 < j_2 < \cdots < j_{q+1}\}$ with $q := |L| - 1 = H - 2 - |T| \ge 0$. The linear forest $(\{1, \dots, H\}, T)$ partitions $\{1, \dots, H\}$ into:
- $C_{\mathrm{left}} = \{1, \dots, j_1\}$ (pinned to $h_1 = 0$),
- $q$ **free components** $C_m^{\mathrm{free}} = \{a_m, \dots, b_m\}$ ($m = 1, \dots, q$, where $a_m := j_m + 1$ and $b_m := j_{m+1}$), and
- $C_{\mathrm{right}} = \{j_{q+1} + 1, \dots, H\}$ (pinned to $h_H = 0$).

Change variables from $(h_2, \dots, h_{H-1})$ to the $q$ collective heights $\zeta_m := h_{a_m}$ ($m = 1, \dots, q$) and $|T|$ internal differences $d_j := h_{j+1} - h_j$ ($j \in T$). On each block ($C_{\mathrm{left}} \setminus \{1\}$, $C_m^{\mathrm{free}}$, $C_{\mathrm{right}} \setminus \{H\}$), the inverse map is triangular with $\pm 1$ on the diagonal, so the total Jacobian is identically $1$, and
$$b(x) \;=\; \sum_{m=1}^q \zeta_m \Psi_m(x) + \sum_{j \in T} d_j \Upsilon_j(x), \qquad \Psi_m(x) \;:=\; \sum_{k=a_m}^{b_m} \Lambda_k(x).$$
Each $\Psi_m$ is the flat-top trapezoid supported on $[t_{a_m - 1}, t_{b_m + 1}]$ of length $S_m := \delta_{a_m - 1} + (t_{b_m} - t_{a_m}) + \delta_{b_m} \ge \delta_{a_m - 1} + \delta_{b_m} \ge 32 h_{\mathrm{grid}}$, equal to $1$ on $[t_{a_m}, t_{b_m}]$ and affine on the two flanking loose edges $[t_{a_m - 1}, t_{a_m}]$ and $[t_{b_m}, t_{b_m + 1}]$.

**Step 3: Diagonal empirical Gram lower bound and scan bound on $G_n^{\mathrm{free}}$.**
Assume $X^n \in E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h_{\mathrm{grid}})$. For any $\zeta = (\zeta_1, \dots, \zeta_q)^\top \in \mathbb{R}^q$, set $b_0 := \sum_{m=1}^q \zeta_m \Psi_m$. The open intervals $\{(t_j, t_{j+1}) : j \in L\}$ and $\{(t_{a_m}, t_{b_m}) : 1 \le m \le q,\; b_m > a_m\}$ are pairwise disjoint.
- On every loose edge $(t_j, t_{j+1})$ ($j \in L$), we have $\delta_j \ge 32 h_{\mathrm{grid}} > 16 h_{\mathrm{grid}}$, so Lemma 1.3(c) (quarter-pairing) gives $\sum_{X_i \in (t_j, t_{j+1})} b_0(X_i)^2 \ge \frac{1}{512} n \delta_j (b_0(t_j)^2 + b_0(t_{j+1})^2)$.
- On every flat top $(t_{a_m}, t_{b_m})$, $b_0 \equiv \zeta_m$, so $\sum_{X_i \in (t_{a_m}, t_{b_m})} b_0(X_i)^2 = N((t_{a_m}, t_{b_m})) \zeta_m^2$.

Summing over all pairwise-disjoint intervals gives
$$\|b_0\|_n^2 \;\ge\; \sum_{m=1}^q \left[\frac{1}{512} n(\delta_{a_m - 1} + \delta_{b_m}) + N\bigl((t_{a_m}, t_{b_m})\bigr)\right] \zeta_m^2.$$
For each $m$: if $t_{b_m} - t_{a_m} \ge \frac{1}{3} S_m$, then $t_{b_m} - t_{a_m} \ge \frac{32}{3} h_{\mathrm{grid}} > 4 h_{\mathrm{grid}}$, so Lemma 1.3(c) gives $N((t_{a_m}, t_{b_m})) \ge \frac{1}{24} n S_m \ge \frac{1}{768} n S_m$; otherwise $\delta_{a_m - 1} + \delta_{b_m} \ge \frac{2}{3} S_m$, so $\frac{1}{512} n(\delta_{a_m - 1} + \delta_{b_m}) \ge \frac{1}{768} n S_m$. Combined with Lemma 1.3(b) on $E_{\mathrm{end}}$, the $q \times q$ empirical Gram matrix $G_n^{\mathrm{free}}$ of $(\Psi_{1,\perp}, \dots, \Psi_{q,\perp})$ satisfies
$$G_n^{\mathrm{free}} \;\succeq\; c_{\mathrm{diag}}\, n \cdot \mathrm{diag}(S_1, \dots, S_q), \qquad c_{\mathrm{diag}} \;:=\; \frac{1}{1809 \cdot 768} = \frac{1}{1389312}.$$
Next, let $U_n^{\mathrm{free}} := (\langle\varepsilon, \Psi_{1,\perp}\rangle_n, \dots, \langle\varepsilon, \Psi_{q,\perp}\rangle_n)^\top$ and $\hat{Z}_{\mathrm{free}} := (G_n^{\mathrm{free}})^{-1/2} U_n^{\mathrm{free}} \in \mathbb{R}^q$. Each trapezoid decomposes pointwise as $\Psi_m(x) = r_L(x; t_{a_m - 1}, t_{a_m}) + \mathbf{1}_{(t_{a_m}, t_{b_m}]}(x) + r_R(x; t_{b_m}, t_{b_m + 1})$, supported inside $\mathrm{supp}(\Psi_m)$ of length $S_m \ge 32 h_{\mathrm{grid}}$. On $E_{\mathrm{good}}(K_0)$, Lemma 1.3(c)–(d) gives $N(\mathrm{supp}(\Psi_m)) \le 2 n S_m$, so:
- $|\langle\varepsilon, \Psi_m\rangle_n| \le \sqrt{6\log n}(\sqrt{N_L} + \sqrt{N_{\mathrm{mid}}} + \sqrt{N_R}) \le \sqrt{18\log n}\,\sqrt{N(\mathrm{supp}(\Psi_m))} \le 6\sqrt{\log n}\,\sqrt{n S_m}$;
- $|\langle\varepsilon, \pi_{\Phi}(\Psi_m)\rangle_n| \le 300 K_0 \|\Psi_m\|_n \le 300 K_0 \sqrt{2 n S_m}$.

Hence for $n \ge 10$, $|\langle\varepsilon, \Psi_{m,\perp}\rangle_n| \le (6 + 425 K_0)\sqrt{n S_m \log n}$, and therefore
$$\|\hat{Z}_{\mathrm{free}}\|_2^2 \;=\; (U_n^{\mathrm{free}})^\top (G_n^{\mathrm{free}})^{-1} U_n^{\mathrm{free}} \;\le\; \frac{1}{c_{\mathrm{diag}} n}\sum_{m=1}^q \frac{\langle\varepsilon, \Psi_{m,\perp}\rangle_n^2}{S_m} \;\le\; q\,\frac{(6 + 425 K_0)^2}{c_{\mathrm{diag}}}\log n.$$
Thus $\|\hat{Z}_{\mathrm{free}}\|_2 \le A_n(H, K_0) := C_A(H, K_0)\sqrt{\log n}$ uniformly on $E_{\mathrm{good}}(K_0)$.

**Step 4: Second-stage Gram–Schmidt and conditional independence.**
Project each $\Upsilon_{j,\perp}$ ($j \in T$) onto $\mathrm{span}(\Psi_{1,\perp}, \dots, \Psi_{q,\perp})^\perp$ in $L^2(\mathbb{P}_n)$, writing $\Upsilon_{j,\perp} = \Upsilon_{j,\perp\perp} + \sum_{m=1}^q \beta_{j, m}\Psi_{m,\perp}$. Shifting $\tilde{\zeta}_m := \zeta_m + \sum_{j \in T} d_j \beta_{j, m}$ (Jacobian $1$) and extending $\tilde{\zeta}$ to $\mathbb{R}^q$ while retaining $|d_j| \le C_H \delta_j$ for $j \in T$ gives an exact orthogonal splitting of the exponent into $\tilde{\zeta}^\top U_n^{\mathrm{free}} - \frac{1}{2}\tilde{\zeta}^\top G_n^{\mathrm{free}}\tilde{\zeta}$ plus $\langle\varepsilon, b_{\mathrm{diff}}\rangle_n - \frac{1}{2}\|b_{\mathrm{diff}}\|_n^2$ (where $b_{\mathrm{diff}} := \sum_{j \in T} d_j \Upsilon_{j,\perp\perp}$). Integrating $\tilde{\zeta} \in \mathbb{R}^q$ yields $\frac{(2\pi)^{q/2}}{\sqrt{\det G_n^{\mathrm{free}}}} e^{\frac{1}{2}\|\hat{Z}_{\mathrm{free}}\|_2^2}$.

Because $b_{\mathrm{diff}} \perp \mathrm{span}(\Psi_{1,\perp}, \dots, \Psi_{q,\perp})$ in $\mathbb{R}^n$, conditional on $X^n \in E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h_{\mathrm{grid}})$, the standard Gaussian vector $\hat{Z}_{\mathrm{free}} \sim \mathcal{N}(0, I_q)$ and the Gaussian variable $\langle\varepsilon, b_{\mathrm{diff}}\rangle_n$ are **independent**. Using $\mathbf{1}_{E_{\mathrm{good}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}} \cap E_{\mathrm{unif}}(h_{\mathrm{grid}})}\mathbf{1}_{\{\|\hat{Z}_{\mathrm{free}}\|_2 \le A_n(H, K_0)\}}$, taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ gives $\frac{\omega_q A_n(H, K_0)^q}{(2\pi)^{q/2}} \cdot 1$, while integrating $d_j \in [-C_H \delta_j, C_H \delta_j]$ ($j \in T$) gives $(2 C_H)^{|T|} \prod_{j \in T} \delta_j$, cancelling $\prod_{j \in T} \delta_j$ in the Jacobian denominator. Using $\sqrt{\det G_n^{\mathrm{free}}} \ge (c_{\mathrm{diag}} n)^{q/2}\prod_{m=1}^q S_m^{1/2}$:
$$\mathbb{E}\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(R_T)\right] \;\le\; C_T(H, K_0)\, n^{-3/2} \cdot \left(\frac{\sqrt{\log n}}{\sqrt{n}}\right)^q \int_{R_T} \left(\prod_{j \in T} d\delta_j\right)\left(\prod_{j \in L} \frac{d\delta_j}{\delta_j}\right) \frac{1}{\prod_{m=1}^q S_m^{1/2}}$$
(with the standard empty-product convention $\prod_{m=1}^0 (\cdots) = 1$ and $\omega_0 = 1$ when $q = 0$, i.e. $|L| = 1$).

**Step 5: Scale-invariant reduction to a finite $n$-independent integral $I_T(H)$.**
Rescale $\delta_j = \delta_+ s_j$ ($j = 1, \dots, H-1$). Since $\frac{\sqrt{\log n}}{\sqrt{n}} = \delta_+^{3/2}$, the powers of $\delta_+$ collect to
$$\delta_+^{3q/2} \cdot \delta_+^{|T|} \cdot \delta_+^{-q/2} \;=\; \delta_+^{|T| + q} \;=\; \delta_+^{H - 2} \;=\; n^{-\frac{H - 2}{3}}(\log n)^{\frac{H - 2}{3}}.$$
Meanwhile, setting $\tilde{\sigma}_k(s) := \max(s_{k-1}, s_k, 1)^{-1/2}$ ($2 \le k \le H-1$) and $\tilde{\sigma}_1 = \tilde{\sigma}_H = +\infty$, an enlarged rescaled region $\tilde{R}_T := \{s \in (0, \infty)^{H-1} : s_j < \min(\tilde{\sigma}_j, \tilde{\sigma}_{j+1}) \;\forall j \in T,\; s_j \ge \min(\tilde{\sigma}_j, \tilde{\sigma}_{j+1}) \;\forall j \in L\}$ contains the rescaled domain after discarding its upper cutoffs, and using $S_m/\delta_+ \ge s_{j_m} + s_{j_{m+1}}$ we obtain
$$\mathbb{E}\!\left[\mathbf{1}_{E_{\mathrm{good}}(K_0)} Z_n(R_T)\right] \;\le\; C_T(H, K_0)\, n^{-\frac{2H + 5}{6}}(\log n)^{\frac{H - 2}{3}}\, I_T(H),$$
where
$$I_T(H) \;:=\; \int_{\tilde{R}_T} \left(\prod_{j \in T} ds_j\right)\left(\prod_{j \in L} \frac{ds_j}{s_j}\right) \frac{1}{\prod_{m=1}^q (s_{j_m} + s_{j_{m+1}})^{1/2}}.$$

**Step 6: Proof that $I_T(H) < \infty$ for every $T \subsetneq \{1, \dots, H-1\}$.**
Partition $\tilde{R}_T$ further according to the set of **big edges** $B := \{j \in L : s_j \ge 1\}$ and **small loose edges** $U := L \setminus B = \{j \in L : s_j < 1\}$. Note that $B$ must be nonempty: if $B = \emptyset$, then $s_j < 1$ for all $j$, so $\tilde{\sigma}_k = 1$ for all $2 \le k \le H-1$, forcing $T = \{1, \dots, H-1\}$ and $L = \emptyset$, contradiction. Fix a nonempty $B\subseteq L$ and define $N_B(j) := \{b \in B : |b - j| = 1\}$ for each edge $j$ on this subregion. We integrate the tight edges first. Before integrating the small loose edges we bound all free-component factors pointwise using their big neighbors. We integrate the big edges last.
1. *Tight edges $t \in T$:* Since $s_t < \min(\tilde{\sigma}_t, \tilde{\sigma}_{t+1}) \le \min(\{1\} \cup \{s_b^{-1/2} : b \in N_B(t)\})$ and $|N_B(t)| \le 2$, integrating $ds_t$ yields at most $\prod_{b \in N_B(t)} s_b^{-1/4}$ (using $s_b^{-1/2} \le s_b^{-1/4}$ if $|N_B(t)| = 1$ and $\min(s_{b_1}^{-1/2}, s_{b_2}^{-1/2}) \le s_{b_1}^{-1/4} s_{b_2}^{-1/4}$ if $|N_B(t)| = 2$).
2. *Small loose edges $u \in U$:* Because $s_u < 1$ and $s_u \ge \min(\tilde{\sigma}_u, \tilde{\sigma}_{u+1}) = \max(s_{u-1}, s_u, s_{u+1}, 1)^{-1/2}$ (with $s_0 := s_H := 0$), we necessarily have $N_B(u) \neq \emptyset$ and $s_u \ge (\max_{b \in N_B(u)} s_b)^{-1/2}$. Once the component factors in item 3 have been bounded, integrating $\frac{ds_u}{s_u}$ over $[(\max_{b \in N_B(u)} s_b)^{-1/2}, 1]$ yields $\frac{1}{2}\log(\max_{b \in N_B(u)} s_b) \le \frac{1}{2}\sum_{b \in B} \log(e s_b)$.
3. *Free-component factors $(s_{j_m} + s_{j_{m+1}})^{-1/2}$ ($m = 1, \dots, q$):*
   - If $j_m \in B, j_{m+1} \in B$: $(s_{j_m} + s_{j_{m+1}})^{-1/2} \le s_{j_m}^{-1/4} s_{j_{m+1}}^{-1/4}$.
   - If $j_m \in B, j_{m+1} \in U$: $(s_{j_m} + s_{j_{m+1}})^{-1/2} \le s_{j_m}^{-1/2}$.
   - If $j_m \in U, j_{m+1} \in B$: $(s_{j_m} + s_{j_{m+1}})^{-1/2} \le s_{j_{m+1}}^{-1/2}$.
   - If $j_m \in U, j_{m+1} \in U$: every edge strictly between $j_m$ and $j_{m+1}$ lies in $T$ (hence $< 1$), so $j_m + 1 \notin B$ and $j_{m+1} - 1 \notin B$. Item 2 gives a big neighbor to each small loose edge. With the two inward neighbors excluded, we must have $N_B(j_m) = \{j_m - 1\}$ and $N_B(j_{m+1}) = \{j_{m+1} + 1\}$, so $s_{j_m} \ge s_{j_m - 1}^{-1/2}$ and $s_{j_{m+1}} \ge s_{j_{m+1} + 1}^{-1/2}$. By AM–GM,
     $$(s_{j_m} + s_{j_{m+1}})^{-1/2} \;\le\; \bigl(2\sqrt{s_{j_m} s_{j_{m+1}}}\bigr)^{-1/2} \;\le\; s_{j_m - 1}^{+1/8}\, s_{j_{m+1} + 1}^{+1/8}.$$

Now tally the exponent of $s_b$ for each $b \in B$ contributed by its right neighbor $b + 1$ (if $b \le H - 2$) and its left neighbor $b - 1$ (if $b \ge 2$):
- If $b + 1 \in T$: item (1) contributes $-1/4$ to $b$, and no $(U, U)$ pair can have $j_m - 1 = b$ (since $b + 1 \notin U$); net $\le -1/4$.
- If $b + 1 \in B$: the $(B, B)$ pair $(b, b + 1)$ in item (3) contributes $-1/4$ to $b$, and no $(U, U)$ pair has $j_m - 1 = b$; net $\le -1/4$.
- If $b + 1 \in U$: the $(B, U)$ pair $(b, b + 1)$ in item (3) contributes $-1/2$ to $b$, while at most one $(U, U)$ pair (namely the unique pair with $j_m = b + 1$, if it exists) can contribute $+1/8$ to $b$; net $\le -\frac{1}{2} + \frac{1}{8} = -\frac{3}{8} < -\frac{1}{4}$.

Symmetrically, if $b \ge 2$, the left neighbor $b - 1$ contributes net exponent $\le -1/4$ to $b$. A $(U,U)$ pair assigns its two positive $1/8$ powers to the big edges immediately outside its two endpoints, $j_m-1$ and $j_{m+1}+1$. Each such power has already been counted on the side facing the adjacent small loose edge. Any other power contributed by a free-component factor is nonpositive. Because $H \ge 3$, every $b \in \{1, \dots, H-1\}$ has at least one neighbor ($b \ge 2$ or $b \le H - 2$), so every $b \in B$ carries net exponent $\le -1/4$ in addition to $\frac{ds_b}{s_b}$. Therefore,
$$I_{T, B}(H) \;\le\; \int_{[1, \infty)^{|B|}} \left(\frac{1}{2}\sum_{b' \in B} \log(e s_{b'})\right)^{|U|} \prod_{b \in B} s_b^{-5/4}\,ds_b \;<\; \infty.$$
Summing over the finitely many pairs $(T, B)$ and applying Markov's inequality on $E_{\mathrm{good}}(K_0)$ yields $Z_n = O_p\bigl(n^{-\frac{2H+5}{6}}(\log n)^{\frac{H-2}{3}}\bigr)$, completing the proof of Theorem D. $\square$

---

## 6. Theorem E: Active-Truth Refutation at $r = 1, H = 4$ [(iii)]

One active hinge can coexist with the three moving knots. On the ball below the active knot stays separated from the others, and two additional regular coordinates change the leading coefficient of $\log n$ by one.

**Theorem E (Active-Truth Refutation at $r = 1, H = 4$) [(iii)].**
Let $r = 1$, $H = 4$, and
$$w^0 \;:=\; \Bigl(0,\; \bigl(1, \tfrac{1}{2}, 1\bigr),\; (1, 0, 0),\; (1, 0, 0),\; (1, 0, 0)\Bigr) \in \mathbb{R}^{13},$$
so $f_{w^0}(x) = (x + \frac{1}{2})_+$ on $[-1, 1]$. Take $W := \overline{B_{1/10}(w^0)}$ and $\varphi \equiv 1/\mathrm{vol}(W)$. Then:
1. *(Display 1)* There exists $c_0^{\mathrm{act}} \in (0, \infty)$ such that $\int_{\{K \le \varepsilon\} \cap W} \varphi(w)\,dw = c_0^{\mathrm{act}}\,\varepsilon^{17/6}(1 + o(1))$, so $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = (\frac{17}{6}, 1)$.
2. *(Exact two-sided free-energy expansion)* $F_n = n S_n + \frac{17}{6}\log n - \frac{1}{3}\log\log n + O_p(1)$.

*Proof.* On $W = \overline{B_{1/10}(w^0)}$:
- Unit 1 satisfies $a_1 \in [0.9, 1.1]$, $b_1 \in [0.4, 0.6]$, $v_1 \in [0.9, 1.1]$, so $t_1 := -b_1/a_1 \in [-\frac{2}{3}, -\frac{4}{11}] \subset [-0.67, -0.36]$ and $s_1 := a_1 v_1 \in [0.81, 1.21]$. Write $\eta_1 := s_1 - 1 \in [-0.19, 0.21]$ and $\xi_1 := t_1 + \frac{1}{2} \in [-\frac{1}{6}, \frac{3}{22}]$.
- Units $j \in \{2, 3, 4\}$ satisfy $a_j \in [0.9, 1.1]$, $|b_j| \le 0.1$, $|v_j| \le 0.1$, so $t_j := -b_j/a_j \in [-\frac{1}{9}, \frac{1}{9}] \subset [-0.12, 0.12]$ and $|s_j| \le 0.11$.

Thus Unit 1 is strictly separated from Units $2, 3, 4$ on all of $W$. By $S_3$ symmetry of Units $2, 3, 4$, restrict to $t_2 < t_3 < t_4$ (factor $6$), set $\delta_1 := t_3 - t_2 > 0$, $\delta_2 := t_4 - t_3 > 0$, and apply Lemma 1.1 to Units $2, 3, 4$ to write
$$\Delta_w(x) := f_w(x) - f_{w^0}(x) = M_4(x) + g_{\xi_1}(x) + \tilde{h}\,\tau_{t_2, \delta_1, \delta_2}(x),$$
where $M_4(x) := c + \eta_1(x - t_1)_+ + S \phi_S(x; t_2, t_4) + B \phi_B(x; t_2, t_4)$, $g_{\xi_1}(x) := (x - t_1)_+ - (x + \frac{1}{2})_+$, and the Jacobian from $w$ to $(a_1, a_2, a_3, a_4, \xi_1, \eta_1, t_2, c, S, B, \delta_1, \delta_2, \tilde{h})$ is $\frac{1}{\delta_1 \delta_2}$.

**Coercivity on three fixed disjoint exterior intervals.** Define $I_1 := [-1, -\frac{2}{3}]$, $I_2 := [-0.36, -0.12]$, and $I_3 := [\frac{1}{2}, 1]$. All three intervals are pairwise disjoint and disjoint from $(t_2, t_4) \subset [-0.12, 0.12]$:
- On $I_1$: $M_4 + g_{\xi_1} = c$.
- On $I_2$: $g_{\xi_1}(x) = -\xi_1$, so $M_4 + g_{\xi_1} = \alpha_2 + \eta_1 x$ where $\alpha_2 := c - \xi_1 - \eta_1 t_1$.
- On $I_3$: $M_4 + g_{\xi_1} = \alpha_3 + S_3 x$ where $\alpha_3 := \alpha_2 + B$ and $S_3 := \eta_1 + S$.
- On $(t_2, t_4)$: $M_4 + g_{\xi_1}$ is affine with $|M_4(x) + g_{\xi_1}(x)| \le |c| + |\xi_1| + |\eta_1| + |S| + |B|$ (since $0 < t_4 - t_1 < 0.8 < 1$), so $(M_4 + g_{\xi_1})^2 \le 5(c^2 + \eta_1^2 + \xi_1^2 + S^2 + B^2)$.

Let $E_{\mathrm{end}}^{\mathrm{act}}$ be the intersection of $E_{\mathrm{end}}$ (on $I_3$, Lemma 1.3) with the analogous Hoeffding-concentrated event on $I_1$ ($N(I_1) \ge \frac{n}{12}$, true mean $\frac{n}{6}$) and $I_2$ ($N(I_2) \in [0.09 n, 0.15 n]$, $|\bar{x}_2 + 0.24| \le 0.02$, $v_2 \ge 0.002$, true mean $0.12 n$, population conditional mean $-0.24$ and variance $0.0048$). By Hoeffding's inequality, $\mathbb{P}((E_{\mathrm{end}}^{\mathrm{act}})^c) \le C e^{-c n} \to 0$. On $E_{\mathrm{end}}^{\mathrm{act}}$:
- $\sum_{I_1} (M_4 + g_{\xi_1})^2 \ge \frac{n}{12} c^2$;
- on $I_2$, $|\bar{x}_2| \le \frac{1}{3}$ and $v_2 \ge \frac{1}{500}$ give $\frac{1}{2} v_2 \eta_1^2 \ge \frac{1}{120}(\eta_1 \bar{x}_2)^2$, so $\sum_{I_2} (M_4 + g_{\xi_1})^2 \ge \frac{n}{12}(\frac{1}{121}\alpha_2^2 + \frac{1}{1000}\eta_1^2) = \frac{n}{1452}\alpha_2^2 + \frac{n}{12000}\eta_1^2$;
- on $I_3$, $|\bar{x}_3| \le 1$ and $v_3 \ge \frac{1}{100}$ give $\sum_{I_3} (M_4 + g_{\xi_1})^2 \ge \frac{n}{1608}\alpha_3^2 + \frac{n}{1600} S_3^2$.

Write $Q=c^2+\eta_1^2+\xi_1^2+S^2+B^2$. The identities $\xi_1=c-\alpha_2-\eta_1t_1$, $S=S_3-\eta_1$ and $B=\alpha_3-\alpha_2$ give
$$Q\le 4c^2+6\eta_1^2+5\alpha_2^2+2S_3^2+2\alpha_3^2.$$
Multiplication by $10^{-5}n$ leaves each coefficient below its respective lower bound above. Thus
$$\sum_{X_i \in I_1 \cup I_2 \cup I_3} (M_4 + g_{\xi_1})^2 \;\ge\; 10^{-5}\, n\bigl(c^2 + \eta_1^2 + \xi_1^2 + S^2 + B^2\bigr).$$
Splitting this exterior sum in half and combining with $\sum_{(t_2, t_4)} (M_4 + g_{\xi_1})^2 \le 5 n(c^2 + \eta_1^2 + \xi_1^2 + S^2 + B^2)$ via $\kappa a^2 + (a+b)^2 \ge \frac{\kappa}{1+\kappa} b^2$ ($\kappa = 10^{-6}$) yields, on $E_{\mathrm{end}}^{\mathrm{act}}$ uniformly over all $(t_1, t_2, t_3, t_4)$,
$$\|M_4 + g_{\xi_1} + \tilde{h}\tau\|_n^2 \;\ge\; \frac{1}{2}\cdot 10^{-5}\, n\bigl(c^2 + \eta_1^2 + \xi_1^2 + S^2 + B^2\bigr) + \frac{1}{10^6 + 1}\tilde{h}^2 \|\tau\|_n^2. \tag{E.1}$$
For the population estimate write $dP=dx/2$, $A=M_4+g_{\xi_1}$, $J=(t_2,t_4)$, and $E=\int_{I_1\cup I_2\cup I_3} A^2\,dP$. The three masses are $1/6,\,0.12,\,1/4$. On $I_2,I_3$ the conditional means are $-0.24,\,3/4$ and the conditional variances are $0.24^2/12,\,0.5^2/12$. For a line $\alpha+s x$ on either interval its conditional second moment is $(\alpha+s\bar x)^2+vs^2$. Applying the two square completions above with these means, variances and masses gives
$$E\ge c^2/12+\alpha_2^2/1452+\eta_1^2/12000+\alpha_3^2/1608+S_3^2/1600\ge10^{-5}Q.$$
Since $P(J)=(\delta_1+\delta_2)/2\le1/9$ and $A^2\le5Q$ on $J$, we have $E/2\ge\kappa\int_J A^2\,dP$ with $\kappa=9\cdot10^{-6}$. Retain the first half of $E$ and use the other half to complete the square on $J$. With $2K=\int(A+\tilde h\tau)^2\,dP$ this gives
$$2K\ge \tfrac12\,10^{-5}Q+\frac{\kappa}{1+\kappa}\,\tilde h^2\int_J\tau^2\,dP.$$
The tent rises linearly from zero to one and falls linearly to zero, so $\int_J\tau^2\,dP=(\delta_1+\delta_2)/6$. Using $\kappa/(1+\kappa)\ge 2/(10^6+1)$ gives
$$K(w) \;\ge\; \frac{1}{4}\cdot 10^{-5}\bigl(c^2 + \eta_1^2 + \xi_1^2 + S^2 + B^2\bigr) + \frac{1}{6(10^6 + 1)}\tilde{h}^2(\delta_1 + \delta_2). \tag{E.2}$$

**Proof of Part 1 (Display 1).** Rescale $(c, \eta_1, \xi_1, S, B) = \varepsilon^{1/2}(\hat{c}, \hat{\eta}_1, \hat{\xi}_1, \hat{S}, \hat{B})$ and $(\delta_1, \delta_2, \tilde{h}) = \varepsilon^{1/3}(x_1, x_2, y)$. The Jacobian factor is $\varepsilon^{5/2} \cdot \varepsilon^{1/3} = \varepsilon^{17/6}$. By (E.2) and $|s_3| \le 0.11 \implies |y| \le 0.11 \frac{x_1 x_2}{x_1 + x_2}$, the rescaled indicator divided by $x_1 x_2$ is dominated uniformly in $\varepsilon$ by an integrable function identically to Theorem A Step 1. As $\varepsilon \downarrow 0$, on the interval between $-\frac{1}{2}$ and $t_1 = -\frac{1}{2} + \varepsilon^{1/2}\hat{\xi}_1$ we have $|g_{\xi_1}(x)| \le \varepsilon^{1/2}|\hat{\xi}_1|$ on length $\varepsilon^{1/2}|\hat{\xi}_1|$, contributing $O(\varepsilon^{3/2}) = o(\varepsilon)$ to $K(w_\varepsilon)$; hence $K(w_\varepsilon)/\varepsilon \to K_{\mathrm{mac}}^{(5)}(\hat{c}, \hat{\eta}_1, \hat{\xi}_1, \hat{S}, \hat{B}; t_2) + \frac{1}{12} y^2(x_1 + x_2)$, where $K_{\mathrm{mac}}^{(5)}$ is the strictly positive-definite quadratic form of $\hat{c} + \hat{\eta}_1(x + \frac{1}{2})_+ - \hat{\xi}_1 \mathbf{1}_{\{x > -\frac{1}{2}\}} + (\hat{S}x + \hat{B})\mathbf{1}_{\{x > t_2\}}$ (strictly positive definite by (E.2)). The limiting squared radius includes the active-unit contribution $(a_1-1)^2+(a_1/2-1/2)^2+(1/a_1-1)^2$. The spare-unit contribution is $D_0$ of Theorem A with indices shifted by one and common knot $t_2$. Its coefficient of $y^2$ is positive, so the radius boundary is null by slicing in $y$. The energy boundary is null by slicing in $\hat c$. At $a_j=1$, $t_2=0$, $x_1=x_2=1$ and all rescaled coefficients and $y$ zero, both inequalities are strict, hence they hold on an open set of positive measure. DCT yields $\mathrm{vol}(\{K \le \varepsilon\} \cap W)/\mathrm{vol}(W) = c_0^{\mathrm{act}}\,\varepsilon^{17/6}(1 + o(1))$ with $0 < c_0^{\mathrm{act}} < \infty$.

**Proof of Part 2a (Evidence lower bound).** Use Theorem B's Jacobian-$1$ tent coordinates $(t_2, \delta, u, \tilde{s}_1)$ on Units $2, 3, 4$, and restrict to the sub-box $B_n^{\mathrm{act}}$:
- $a_1, a_2, a_3, a_4 \in [0.99, 1.01]$, $t_2 \in [-0.01, 0.01]$, $u \in [\frac{1}{4}, \frac{1}{2}]$, $\tilde{s}_1 \in [-0.01, 0.01]$, $\delta \in [n^{-1/3}, 10 n^{-1/3}(\log n)^{1/3}]$,
- $(c, \eta_1, \xi_1, S, B) \in [-n^{-1/2}, n^{-1/2}]^5$ (volume $32 n^{-5/2}$).

Here $b_1=a_1(1/2-\xi_1)$ and $v_1=(1+\eta_1)/a_1$, so their deviations from $1/2$ and $1$ are at most $0.005+1.01 n^{-1/2}$ and $(0.01+n^{-1/2})/0.99$. For the spare units $|b_j|\le1.01(0.01+1.5\delta_+)$, where $\delta_+=10n^{-1/3}(\log n)^{1/3}$. The three slope formulas in Theorem B give $|s_j|\le0.015+O(n^{-1/6})$, hence $|v_j|\le(0.015+O(n^{-1/6}))/0.99$. For large $n$ all thirteen coordinate perturbations are at most $0.02$. Thus $\|w - w^0\|_2^2 \le 13(0.02)^2 = 0.0052 < \frac{1}{100} = R^2$ and $B_n^{\mathrm{act}} \subset W$. Using the exact integral identities $(x - t_1)_+ = \int_{t_1}^1 \mathbf{1}_{\{x \ge t\}}\,dt$ and $g_{\xi_1}(x) = -\int_{-1/2}^{t_1} \mathbf{1}_{\{x \ge t\}}\,dt$ (for all $x \in [-1, 1]$), we have $|M_4(x) + g_{\xi_1}(x)| \le 6 n^{-1/2}$ and $|\langle \varepsilon, M_4 + g_{\xi_1}\rangle_n| \le 7 n^{-1/2} M_n$, so on $E_{\mathrm{max}}(K_0)$ the macro term is bounded below by $-7 K_0 - 18$ uniformly on $B_n^{\mathrm{act}}$. The cross term with $\psi_{t_2, u, \delta}$ is $O(n^{-1/6}(\log n)^{2/3}) = o(1)$ on $E_{\mathrm{unif}}(\delta_+/8)$, and the tent integral $J_n$ concentrates around $\mathbb{E}_\varepsilon[J_n \mid X^n] \asymp n^{-1/3}(\log n)^{1/3}$ by the exact Chebyshev calculation of Theorem B Step 3 (with $(0.01)^2 \cdot 500\log n = 0.05\log n < \frac{1}{3}\log n$). Multiplying $32 n^{-5/2}$ by $J_n$ yields $Z_n \ge c(\eta)\, n^{-17/6}(\log n)^{1/3}$ with probability $\ge 1 - \eta$.

**Proof of Part 2b (Evidence upper bound).** Set $\delta_+ := n^{-1/3}(\log n)^{1/3}$, $h := \delta_+/8$, $K_0 := \sqrt{2\log(16/\eta)}$, and $E_{\mathrm{good}}^{\mathrm{act}}(K_0) := E_{\mathrm{end}}^{\mathrm{act}} \cap E_{\mathrm{unif}}(h) \cap E_{\mathrm{max}}(K_0) \cap E_{\mathrm{scan}}$. Fix $(t_1, t_2, \delta_1, \delta_2)$ and let $\mathcal{V}_4 := \mathrm{span}(\Phi_4)$ where $\Phi_4 := (1, (x - t_1)_+, \phi_S, \phi_B)^\top$. At a fixed admissible knot $t_1$, the same exterior calculation applies to $M_4$ alone. Set the additive function $g_{\xi_1}$ to zero in that calculation while keeping the knot fixed, so that $\alpha_2=c-\eta_1t_1$, $\alpha_3=\alpha_2+B$ and $S_3=\eta_1+S$. The exterior estimate then controls $c^2+\eta_1^2+S^2+B^2$ with constant $10^{-5}n$. Thus the Gram matrix $G_n^{(4)}$ satisfies $G_n^{(4)}\succeq10^{-5}n I_4$. For $U_n^{(4)}=\sum_i\varepsilon_i\Phi_4(X_i)$, Lemma 1.3(d) and $|\langle\varepsilon,(x-t_1)_+\rangle_n|\le(1-t_1)M_n\le2M_n$ give $\|U_n^{(4)}\|_2^2\le10M_n^2$. In particular $\|(G_n^{(4)})^{-1/2}U_n^{(4)}\|_2\le1000K_0$ on the good event. Projecting both $g_{\xi_1}$ and $\tau$ onto $\mathcal{V}_4^\perp$ (shifting $(c, \eta_1, S, B) \in \mathbb{R}^4$ with Jacobian $1$) and integrating out $\mathbb{R}^4$ gives $\le C_4(K_0) n^{-2}$ on $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$, leaving
$$\int_{-1/6\le\xi_1\le3/22} d\xi_1 \int_{\mathcal{T}_{\mathrm{act}}} \frac{dt_2\,d\delta_1\,d\delta_2}{\delta_1 \delta_2} \int_{|\tilde{h}| \le 0.11\min(\delta_1, \delta_2)} \exp\!\left(\langle\varepsilon, g_{\xi_1,\perp} + \tilde{h}\tau_\perp\rangle_n - \frac{1}{2}\|g_{\xi_1,\perp} + \tilde{h}\tau_\perp\|_n^2\right) d\tilde{h}.$$
Here $\mathcal T_{\mathrm{act}}$ consists of ordered spare knots in $[-1/9,1/9]$. The slice $\xi_1=0$ has measure zero and may be omitted throughout the integral. All projections are at fixed admissible knots. The following estimates hold on the indicated design or noise events.
1. The exterior calculation and square completion in (E.1) hold for arbitrary real macro coefficients and tent height at fixed knots. Minimizing over the four coefficients, and also over the height for the second projection, gives $\|g_{\xi_1,\perp}\|_n^2 \ge c_g n \xi_1^2$, $\|g_{\xi_1,\perp\perp}\|_n^2 \ge c_g n \xi_1^2$ (where $g_{\xi_1,\perp\perp} := g_{\xi_1,\perp} - \mathrm{proj}_{\tau_\perp}(g_{\xi_1,\perp})$). Applying the same square completion with the additive function $g_{\xi_1}$ omitted and unit tent height gives $\|\tau_\perp\|_n^2 \ge c_\tau \|\tau\|_n^2$, with $c_g := 5 \times 10^{-6}$ and $c_\tau := (10^6 + 1)^{-1}$.
2. Since $|g_{\xi_1}(x)| \le |\xi_1|$, $\|\Phi_4(x)\|_2 \le 3$, and $(G_n^{(4)})^{-1} \preceq 10^5 n^{-1} I_4$, the projection $\pi_{\mathcal{V}_4}(g_{\xi_1})$ has coefficient norm $\le 3 \times 10^5 |\xi_1|$, so $|g_{\xi_1,\perp}(x)| \le C_p |\xi_1|$ everywhere ($C_p := 10^6$). Hence $|\langle g_{\xi_1,\perp}, \tau_\perp\rangle_n| = |\langle g_{\xi_1,\perp}, \tau\rangle_n| \le C_p |\xi_1| N([t_2, t_4]) \le C_p' |\xi_1| n \delta$ (for $\delta \ge \delta_+$) and $\le C_p' |\xi_1| n \delta_+$ (for $\delta \le \delta_+$).
3. On $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$, $|\langle \varepsilon, g_{\xi_1,\perp}\rangle_n| \le |\langle\varepsilon, g_{\xi_1}\rangle_n| + |\langle\varepsilon, \pi_{\mathcal{V}_4}(g_{\xi_1})\rangle_n| \le K_0\sqrt{n}|\xi_1| + \sqrt{10^5 \cdot 10}\,K_0 \cdot \|g_{\xi_1}\|_n \le 1001 K_0\sqrt{n}|\xi_1| =: C_g(K_0)\sqrt{n}|\xi_1|$.

Now partition $\mathcal{T}_{\mathrm{act}}$ into $\mathcal{R}_{1+2}$, $\mathcal{R}_{3a}$, $\mathcal{R}_{3b}$ as in Theorem C Step 2:
- **On $\mathcal{R}_{1+2}$ ($\delta \le \delta_+$) and $\mathcal{R}_{3a}$ ($\delta > \delta_+,\; u \le u_{\max}(\delta)$):** Decompose $g_{\xi_1,\perp} + \tilde{h}\tau_\perp = (1 + \tilde{h}\gamma) g_{\xi_1,\perp} + \tilde{h}\tau_{\perp\perp}$, where $\gamma := \langle \tau_\perp, g_{\xi_1,\perp}\rangle_n / \|g_{\xi_1,\perp}\|_n^2$ and $\tau_{\perp\perp} \perp \mathrm{span}(\mathcal{V}_4, g_{\xi_1,\perp})$. By facts (1)–(2), $|\tilde{h}\gamma| \le C_1 \frac{u \delta (\delta \vee \delta_+)}{|\xi_1|}$ (where $C_1 := 0.11 C_p' / c_g$). Split $\xi_1$ at $\xi_* := 2 C_1 u \delta (\delta \vee \delta_+)$:
  - *For $|\xi_1| > \xi_*$:* $|\tilde{h}\gamma| \le \frac{1}{2}$, so $1 + \tilde{h}\gamma \in [\frac{1}{2}, \frac{3}{2}]$, and pointwise on $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$,
    $$(1 + \tilde{h}\gamma)\langle\varepsilon, g_{\xi_1,\perp}\rangle_n - \frac{1}{2}(1 + \tilde{h}\gamma)^2\|g_{\xi_1,\perp}\|_n^2 \;\le\; \frac{3}{2} C_g(K_0)\sqrt{n}|\xi_1| - \frac{1}{8} c_g n \xi_1^2.$$
    Integrating the exponential of this deterministic bound over $\xi_1 \in \mathbb{R}$ gives $\le C_2(K_0) n^{-1/2}$, while taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ on the remaining factor $\exp(\tilde{h}\langle\varepsilon, \tau_{\perp\perp}\rangle_n - \frac{1}{2}\tilde{h}^2 \|\tau_{\perp\perp}\|_n^2)$ yields identically $1$. Integrating $(u, \delta)$ over $\mathcal{R}_{1+2} \cup \mathcal{R}_{3a}$ as in Theorem C Step 3 gives $O(n^{-2}\cdot n^{-1/2}\cdot n^{-1/3}(\log n)^{1/3}) = O(n^{-17/6}(\log n)^{1/3})$.
  - *For $|\xi_1| \le \xi_*$:* Bound $\mathbf{1}_{E_{\mathrm{good}}^{\mathrm{act}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}}^{\mathrm{act}} \cap E_{\mathrm{unif}}(h)}$ and take $\mathbb{E}_\varepsilon[\exp(\langle\varepsilon, g_{\xi_1,\perp} + \tilde{h}\tau_\perp\rangle_n - \frac{1}{2}\|g_{\xi_1,\perp} + \tilde{h}\tau_\perp\|_n^2) \mid X^n] = 1$. On $\mathcal{R}_{1+2}$, $\xi_* \le 2 C_1 \delta_+^2 = O(n^{-2/3}(\log n)^{2/3}) \ll n^{-1/2}$, giving $o(n^{-17/6}(\log n)^{1/3})$. On $\mathcal{R}_{3a}$, integrating $2\xi_* \cdot 0.22 u\delta \cdot \frac{du\,d\delta}{u\delta} = 0.44\cdot 2 C_1 u \delta^2\,du\,d\delta$ yields
    $$\int_{\delta_+}^1 \delta^2\left(\int_0^{u_{\max}(\delta)} u\,du\right) d\delta \;=\; \frac{1}{2}\int_{\delta_+}^1 \frac{\log n}{n \delta}\,d\delta \;=\; O\!\left(\frac{(\log n)^2}{n}\right) \;\ll\; n^{-5/6}(\log n)^{1/3}.$$
- **On $\mathcal{R}_{3b}$ ($\delta > \delta_+,\; u > u_{\max}(\delta)$):** Orthogonalize in the opposite order: write $g_{\xi_1,\perp} + \tilde{h}\tau_\perp = g_{\xi_1,\perp\perp} + \tilde{h}'\tau_\perp$ with $\tilde{h}' := \tilde{h} + \langle g_{\xi_1,\perp}, \tau_\perp\rangle_n / \|\tau_\perp\|_n^2$, and extend $\tilde{h}'$ to $\mathbb{R}$. Integrating $\tilde{h}' \in \mathbb{R}$ produces $\frac{\sqrt{2\pi}}{\|\tau_\perp\|_n} e^{\frac{1}{2}\hat{Z}_4^2}$, where $\hat Z_4=\langle\varepsilon,\tau_\perp\rangle_n/\|\tau_\perp\|_n$. The half of the longer tent edge adjoining its peak has length $\delta/2>4h$ and contains at least $n\delta/16$ observations. On it $\tau\ge1/2$, hence $\|\tau_\perp\|_n^2\ge c_\tau n\delta/64$. The two ramp scan bounds and $N([t_2,t_4])\le3n\delta$ give $|\langle\varepsilon,\tau\rangle_n|\le6\sqrt{n\delta\log n}$. The projection term is at most $1000K_0\|\tau\|_n$ by the four-dimensional score bound. Dividing by $\|\tau_\perp\|_n\ge\sqrt{c_\tau}\|\tau\|_n$ for this last term gives, uniformly on the good event,
  $$|\hat Z_4|\le A_n^{\mathrm{act}}(K_0):=C_A'(K_0)\sqrt{\log n},\qquad C_A'(K_0)=(48+1000K_0)/\sqrt{c_\tau}.$$
  At each fixed admissible parameter on the design event, $\hat Z_4$ is conditionally standard normal. By facts (1)–(2), the normalized correlation satisfies
  $$\frac{|\langle g_{\xi_1,\perp}, \tau_\perp\rangle_n|}{\|g_{\xi_1,\perp\perp}\|_n \|\tau_\perp\|_n} \;\le\; \frac{C_p' |\xi_1| n \delta}{\sqrt{c_g n \xi_1^2}\,\sqrt{\frac{c_\tau}{64} n \delta}} \;=\; C_{\mathrm{cor}}\sqrt{\delta},$$
  so on $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$, the standardized variable $Z_g := \langle\varepsilon, g_{\xi_1,\perp\perp}\rangle_n / \|g_{\xi_1,\perp\perp}\|_n$ satisfies $|Z_g| \le \frac{C_g(K_0)}{\sqrt{c_g}} + C_{\mathrm{cor}}\sqrt{\delta}\,A_n^{\mathrm{act}}(K_0)$. Split $\mathcal{R}_{3b}$ at $\delta \le \frac{1}{\log n}$ vs $\delta > \frac{1}{\log n}$:
  - *Sub-region $\delta \le \frac{1}{\log n}$:* Here $\sqrt{\delta}\,A_n^{\mathrm{act}}(K_0) \le C_A'(K_0)$, so $|Z_g| \le C_3(K_0) = O(1)$ uniformly. Pointwise on $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$, completing the square gives $\langle\varepsilon, g_{\xi_1,\perp\perp}\rangle_n - \frac{1}{2}\|g_{\xi_1,\perp\perp}\|_n^2 \le C_3(K_0)\|g_{\xi_1,\perp\perp}\|_n - \frac{1}{2}\|g_{\xi_1,\perp\perp}\|_n^2 = C_3(K_0)^2 - (\frac{1}{2}\|g_{\xi_1,\perp\perp}\|_n - C_3(K_0))^2 - \frac{1}{4}\|g_{\xi_1,\perp\perp}\|_n^2 \le C_3(K_0)^2 - \frac{1}{4} c_g n \xi_1^2$. Integrating $\xi_1 \in \mathbb{R}$ gives $\le C_4'(K_0) n^{-1/2}$ deterministically, and taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ on $e^{\frac{1}{2}\hat{Z}_4^2}\mathbf{1}_{\{|\hat{Z}_4| \le A_n^{\mathrm{act}}\}}$ and integrating $(u, \delta)$ as in Theorem C Step 4 gives $O(n^{-2} \cdot n^{-1/2} \cdot n^{-1/3}(\log n)^{1/3}) = O(n^{-17/6}(\log n)^{1/3})$.
  - *Sub-region $\delta > \frac{1}{\log n}$:* Split $\xi_1$ at $\xi_{\mathrm{cut}} := C_5(K_0) n^{-1/2}\sqrt{\log n}$, taking $C_5(K_0)$ at least $\sqrt{40/c_g}$ and at least $\frac{4}{\sqrt{c_g}}\bigl(\frac{C_g(K_0)}{\sqrt{c_g}} + C_{\mathrm{cor}} C_A'(K_0)\bigr)$.
    - For $|\xi_1| \le \xi_{\mathrm{cut}}$: since $g_{\xi_1,\perp\perp} \perp \tau_\perp$, $\langle\varepsilon, g_{\xi_1,\perp\perp}\rangle_n$ and $\hat{Z}_4$ are conditionally independent given $X^n$, so taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ gives exact $1$ for the $g_{\xi_1,\perp\perp}$ factor and $\sqrt{\frac{2}{\pi}} A_n^{\mathrm{act}}(K_0)$ for the $\hat{Z}_4$ factor. Integrating $|\xi_1| \le \xi_{\mathrm{cut}}$ (length $2\xi_{\mathrm{cut}} = O(n^{-1/2}\sqrt{\log n})$) and $\int_{1/\log n}^1 \delta^{-3/2}\log(\delta/\delta_+)\,d\delta = O((\log n)^{3/2})$ yields $O(n^{-2} \cdot n^{-1/2}\sqrt{\log n} \cdot n^{-1/2}\sqrt{\log n} \cdot (\log n)^{3/2}) = O(n^{-3}(\log n)^{5/2}) = o(n^{-17/6}(\log n)^{1/3})$.
    - For $|\xi_1| > \xi_{\mathrm{cut}}$: $|Z_g| \le \frac{1}{4}\sqrt{c_g n}\,|\xi_1| \le \frac{1}{4}\|g_{\xi_1,\perp\perp}\|_n$, so $Z_g \|g_{\xi_1,\perp\perp}\|_n - \frac{1}{2}\|g_{\xi_1,\perp\perp}\|_n^2 \le -\frac{1}{4} c_g n \xi_1^2 \le -\frac{1}{4} c_g C_5^2 \log n$. The choice of $C_5$ therefore bounds the residual likelihood ratio by $n^{-10}$ on the good event. Before integrating the remaining kernel, retain $\mathbf1_{\{|\hat Z_4|\le A_n^{\mathrm{act}}\}}$ and take conditional expectation at fixed knots. Then $\mathbb E[e^{\hat Z_4^2/2}\mathbf1_{\{|\hat Z_4|\le A_n^{\mathrm{act}}\}}\mid X^n]=\sqrt{2/\pi}\,A_n^{\mathrm{act}}$. The $\xi_1$ interval has bounded length. Together with $\|\tau_\perp\|_n^{-1}\le C(n\delta)^{-1/2}$ and the gap integral $O((\log n)^{3/2})$ above, the resulting contribution is $O(n^{-2}n^{-10}n^{-1/2}(\log n)^2)=o(n^{-17/6}(\log n)^{1/3})$.

Applying Markov's inequality on $E_{\mathrm{good}}^{\mathrm{act}}(K_0)$ gives $Z_n = O_p(n^{-17/6}(\log n)^{1/3})$, completing Theorem E. $\square$

---

## 7. Theorem F. Widths one and two on the interior balls [(iii)]

On the interior balls $W=\overline{B_{1/3}(w^0)}$ around $w^0=(0,(1,0,0)^H)$ with uniform prior, $H=3$ is the first width at which the two displays fail to share their exponents.

**Theorem F (Positive Asymptotics on the Interior Balls at $r = 1, H = 1$ and $r = 1, H = 2$) [(iii)].**
Fix $r = 1$, $w^0 = (0, (1, 0, 0)^H) \in \mathbb{R}^{3H+1}$, $W = \overline{B_{1/3}(w^0)}$, and $\varphi \equiv 1/\mathrm{vol}(W)$.
1. **($H = 1$)** Both Display 1 and Display 2 hold with $(\lambda, m) = (1, 1)$: there exists $c_0^{(1)} \in (0, \infty)$ such that $\int_{\{K \le \varepsilon\} \cap W} \varphi\,dw = c_0^{(1)}\,\varepsilon(1 + o(1))$ and $F_n = n S_n + \log n + O_p(1)$.
2. **($H = 2$)** Both Display 1 and Display 2 hold with $(\lambda, m) = (\frac{3}{2}, 2)$: there exists $c_0^{(2)} \in (0, \infty)$ such that $\int_{\{K \le \varepsilon\} \cap W} \varphi\,dw = c_0^{(2)}\,\varepsilon^{3/2}\log(1/\varepsilon)(1 + o(1))$ and $F_n = n S_n + \frac{3}{2}\log n - \log\log n + O_p(1)$.

*Proof of Part 1 ($H = 1$).* On $W = \overline{B_{1/3}(w^0)}$, $a_1 \in [\frac{2}{3}, \frac{4}{3}]$, $t_1 = -b_1/a_1 \in [-\frac{1}{2}, \frac{1}{2}]$, $s_1 = a_1 v_1 \in [-\frac{4}{9}, \frac{4}{9}]$, and $f_w(x) = c + s_1 (x - t_1)_+$ with unit Jacobian $(b_1, v_1) \mapsto (t_1, s_1)$.
- *Coercivity:* On $[-1, -\frac{1}{2}]$, $f_w = c$; on $[\frac{1}{2}, 1]$, $f_w = c + s_1(x - t_1)$. Both the population Gram matrix $G_{\mathrm{pop}}^{(1)}(t_1)$ and (on $E_{\mathrm{end}}$ of Lemma 1.3) the empirical Gram matrix $G_n^{(1)}(t_1)$ of $(1, (x - t_1)_+)$ are uniformly positive definite: $4 K(w) \ge \frac{1}{2} c^2 + \frac{1}{192} s_1^2$, and on $E_{\mathrm{end}}$, $G_n^{(1)}(t_1) \succeq \frac{n}{1600} I_2$ (using $\sum_{[\frac{1}{2}, 1]} (c + s_1(X_i - t_1))^2 \ge N_R v_R s_1^2 \ge \frac{n}{800} s_1^2$ and $\sum_{[-1, -\frac{1}{2}]} c^2 \ge \frac{n}{8} c^2$).
- *Display 1:* Rescaling $(c, s_1) = \varepsilon^{1/2}(\hat{c}, \hat{s}_1)$ extracts $\varepsilon^1$ with bounded support $(a_1, t_1, \hat{c}, \hat{s}_1) \in [\frac{2}{3}, \frac{4}{3}] \times [-\frac{1}{2}, \frac{1}{2}] \times [-30, 30]^2$, and DCT immediately yields $\mathrm{vol}(\{K \le \varepsilon\} \cap W) = C_{\mathrm{vol}}^{(1)}\,\varepsilon(1 + o(1))$ with $C_{\mathrm{vol}}^{(1)} > 0$.
- *Display 2 (lower bound):* Restrict to $a_1 \in [0.95, 1.05]$, $t_1 \in [-0.05, 0.05]$, $(c, s_1) \in [-n^{-1/2}, n^{-1/2}]^2$ (strictly inside $W$ for large $n$). Since $(x - t_1)_+ = \int_{t_1}^1 \mathbf{1}_{\{x \ge t\}}\,dt$, on $E_{\mathrm{max}}(K_0)$ we have $\langle\varepsilon, f_w\rangle_n - \frac{1}{2}\|f_w\|_n^2 \ge -3 K_0 - 5$, giving $Z_n \ge c(K_0) n^{-1}$.
- *Display 2 (upper bound):* Extending $(c, s_1)$ to $\mathbb{R}^2$ at each fixed $(a_1, t_1)$, on $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$ we have $G_n^{(1)}(t_1) \succeq \frac{n}{1600} I_2$ and $\|U_n^{(1)}(t_1)\|_2^2 \le 5 M_n^2 \le 5 K_0^2 n$, so the 2D Gaussian integral is bounded uniformly by $3200\pi e^{4000 K_0^2} n^{-1}$. Integrating over $a_1 \in [\frac{2}{3}, \frac{4}{3}]$ and $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$ yields $Z_n \le C'(K_0) n^{-1}$ on $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$, hence $F_n = n S_n + \log n + O_p(1)$.

*Proof of Part 2 ($H = 2$).* By $S_2$ symmetry, restrict to $t_1 < t_2$ (factor $2$), set $\delta := t_2 - t_1 \in (0, 1]$, and change variables $(s_1, s_2) \mapsto (S, B)$ where $S := s_1 + s_2$ and $B := -(s_1 t_1 + s_2 t_2)$. The exact inverse is
$$s_1 = \frac{B + S t_2}{\delta}, \qquad s_2 = \frac{-B - S t_1}{\delta}, \qquad \left|\det \frac{\partial(s_1, s_2)}{\partial(S, B)}\right| = \frac{1}{\delta},$$
and $f_w(x) = c + S\phi_S(x; t_1, t_2) + B\phi_B(x; t_1, t_2) = M(x)$ identically on $[-1, 1]$ (with $b=0$). By the exterior-interval proof of Lemma 1.2, which uses only the two exterior knots when $b\equiv0$, $K(w) \ge \frac{1}{3072}(c^2 + S^2 + B^2)$ globally on $W$.

- *Display 1:* Rescale $(c, S, B) = \varepsilon^{1/2}(\hat{c}, \hat{S}, \hat{B})$ (extracting $\varepsilon^{3/2}$) and split $\delta \in (0, 1]$ at $\varepsilon^{1/2}$:
  - For $\delta \in (0, \varepsilon^{1/2}]$: $|s_1| \le \frac{4}{9}$ implies $|\hat{B} + \hat{S} t_2| \le \frac{4}{9}\varepsilon^{-1/2}\delta$, so for fixed $(a_1, a_2, t_1, \delta, \hat{c}, \hat{S})$ the $\hat{B}$-interval has length at most $\frac{8}{9}\varepsilon^{-1/2}\delta$. Integrating $\frac{8}{9}\varepsilon^{-1/2}\delta \cdot \frac{d\delta}{\delta}$ over $(0, \varepsilon^{1/2}]$ gives $\frac{8}{9}$, so the total contribution of $\delta \le \varepsilon^{1/2}$ is $O(\varepsilon^{3/2}) = o(\varepsilon^{3/2}\log(1/\varepsilon))$.
  - For $\delta \in [\varepsilon^{1/2}, 1]$: substitute $\delta = \varepsilon^{\theta/2}$ with $\theta \in [0, 1]$, so $|d\delta|/\delta = \frac{1}{2}\log(1/\varepsilon)\,d\theta$. The integrand is dominated by the constant indicator of the compact box $(a_1, a_2, t_1, \hat{c}, \hat{S}, \hat{B}, \theta) \in [\frac{2}{3}, \frac{4}{3}]^2 \times [-\frac{1}{2}, \frac{1}{2}] \times [-\sqrt{3072}, \sqrt{3072}]^3 \times [0, 1]$. For every fixed $\theta \in (0, 1)$, as $\varepsilon \downarrow 0$ we have $\delta = \varepsilon^{\theta/2} \to 0$ and $\varepsilon^{1/2}/\delta = \varepsilon^{(1-\theta)/2} \to 0$, so $t_2 \to t_1$, $s_1, s_2 \to 0$, $\|w_\varepsilon - w^0\|_2^2 \to (a_1 - 1)^2 + (a_2 - 1)^2 + (a_1^2 + a_2^2) t_1^2$, and $K(w_\varepsilon)/\varepsilon \to K_{\mathrm{mac}}(\hat{c}, \hat{S}, \hat{B}; t_1)$. By DCT,
    $$\frac{\mathrm{vol}(\{K \le \varepsilon\} \cap W)}{\varepsilon^{3/2}\log(1/\varepsilon)} \;\longrightarrow\; C_{\mathrm{vol}}^{(2)} \;:=\; \int_{\{(a_1-1)^2+(a_2-1)^2+(a_1^2+a_2^2)t_1^2 < 1/9\}} \frac{\frac{4}{3}\pi \cdot 2^{3/2}}{\sqrt{\det G_{\mathrm{mac}}(t_1)}}\,da_1\,da_2\,dt_1 \in (0, \infty),$$
    where factor $2$ from $S_2$ symmetry cancels the $\frac{1}{2}$ from $|d\delta|/\delta = \frac{1}{2}\log(1/\varepsilon)\,d\theta$.
- *Display 2 (lower bound):* Restrict to the sub-box $a_1, a_2 \in [0.95, 1.05]$, $t_1 \in [-0.03, 0.03]$, $\delta \in [100 n^{-1/2}, 0.05]$, and $(c, S, B) \in [-n^{-1/2}, n^{-1/2}]^3$. On this box $|s_1|, |s_2| \le \frac{2 n^{-1/2}}{100 n^{-1/2}} = 0.02$, so $\|w - w^0\|_2^2 < 0.015 < \frac{1}{9}$ for large $n$. On $E_{\mathrm{max}}(K_0)$, $\langle\varepsilon, M\rangle_n - \frac{1}{2}\|M\|_n^2 \ge -4 K_0 - \frac{9}{2}$ uniformly, so integrating against $\frac{d\delta}{\delta}$ gives
  $$Z_n \;\ge\; \frac{1}{\mathrm{vol}(W)}\cdot (0.1)^2 \cdot (0.06) \cdot (8 n^{-3/2})\, e^{-4K_0 - 9/2}\int_{100 n^{-1/2}}^{0.05} \frac{d\delta}{\delta} \;=\; c(K_0)\, n^{-3/2}\log n \bigl(1 - o(1)\bigr).$$
- *Display 2 (upper bound):* Split $\delta \in (0, 1]$ at $n^{-1/2}$.
  - On $\delta \in [n^{-1/2}, 1]$: on $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$, extending $(c, S, B)$ to $\mathbb{R}^3$ gives the uniform 3D Gaussian bound $\le C_{\mathrm{mac}}(K_0) n^{-3/2}$ from Theorem C Step 1. Integrating over $t_1 \in [-\frac{1}{2}, \frac{1}{2}]$ and $\delta \in [n^{-1/2}, 1]$ against $\frac{d\delta}{\delta}$ yields $\le \frac{1}{2} C_{\mathrm{mac}}(K_0) n^{-3/2}\log n$.
  - On $\delta \in (0, n^{-1/2})$: change variables from $(c, S, B)$ to $(c, S, s_1)$ via $B = s_1 \delta - S t_2$, which has $|\frac{\partial B}{\partial s_1}| = \delta$ and cancels the $\frac{1}{\delta}$ Jacobian. Then $f_w(x) = c + S(x - t_2)_+ + s_1 \delta \phi_B(x; t_1, t_2)$ with $|s_1| \le \frac{4}{9}$. Project $s_1 \delta \phi_B$ onto $\mathrm{span}(1, (x - t_2)_+)^\perp$ in $L^2(\mathbb{P}_n)$ (shifting $(c, S) \in \mathbb{R}^2$ with Jacobian $1$). On $E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)$, integrating $(\tilde{c}, \tilde{S}) \in \mathbb{R}^2$ gives $\le 3200\pi e^{4000 K_0^2} n^{-1}$ uniformly (from Part 1 above). Bounding $\mathbf{1}_{E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)} \le \mathbf{1}_{E_{\mathrm{end}}}$ and taking $\mathbb{E}_\varepsilon[\cdot \mid X^n]$ on the remaining orthogonal factor $\exp(s_1 \delta \langle\varepsilon, \phi_{B,\perp}\rangle_n - \frac{1}{2}(s_1\delta)^2 \|\phi_{B,\perp}\|_n^2)$ gives identically $1$; integrating over $|s_1| \le \frac{4}{9}$ and $\delta \in (0, n^{-1/2})$ yields $\frac{8}{9} n^{-1/2}$, hence $\mathbb{E}[\mathbf{1}_{E_{\mathrm{end}} \cap E_{\mathrm{max}}(K_0)} Z_n(\delta < n^{-1/2})] \le C_2(K_0) n^{-3/2} = o(n^{-3/2}\log n)$.

By Markov's inequality, $Z_n = O_p(n^{-3/2}\log n)$, and combining lower and upper bounds yields $F_n = n S_n + \frac{3}{2}\log n - \log\log n + O_p(1)$. $\square$

---

## 8. Open Extensions and Conjectures [(iv)]

The following extensions go beyond what is proved in Sections 2–7 and are therefore explicitly labelled **(iv) conjecture**:

1. **Unrestricted / boundary-knot domains at $r = 1, H \in \{1, 2\}$ [(iv)]:** When $W$ allows knots $t_j$ to reach $\pm 1$ or enter the dead-hinge cone $\{b < -|a|\}$ (e.g., $W = [-1, 1]^4$ at $H = 1$ with dead cone $(\frac{1}{2}, 1)$, or $a \in [1, 2], t \in [-1, 1]$ with boundary spike $(\frac{5}{6}, 1)$, or active hinge $f_{w^0}(x) = x_+$ at $H = 1$ with $(\frac{3}{2}, 1)$), we conjecture that both Display 1 and Display 2 still hold because only $O(1)$ boundary endpoints exist (no continuum of disjoint interior spikes). Proving Display 2 uniformly across boundary-spike and dead-cone strata is left open here.
2. **General active truths at $r = 1$ with $k$ active hinges and $H - k \ge 3$ spare units [(iv)]:** Extending Theorem E from $k = 1, H = 4$ to any $k \ge 1$ separated active hinges plus $H - k \ge 3$ zero-output units on a sufficiently small ball $W = \overline{B_R(w^0)}$, we conjecture Display 1 holds with $(\lambda_{\mathrm{vol}}, m_{\mathrm{vol}}) = (\frac{2k + 3}{2} + \frac{H - k - 2}{3}, 1)$ and the free energy satisfies $F_n = n S_n + \lambda_{\mathrm{vol}}\log n - \frac{H - k - 2}{3}\log\log n + O_p(1)$.
3. **Higher input dimensions $r\ge2$ [(iv)].** Whether there are compact-domain examples with a multiplicity mismatch in higher dimensions, and which widths and log-log coefficients occur, remain open here.

---

## References

- J.-M. Azaïs, E. Gassiat, and C. Mercadier (2006), *Asymptotic distribution and local power of the log-likelihood ratio test for mixtures: bounded and unbounded cases*, Bernoulli 12(5), 775–799.
- P. J. Bickel and H. Chernoff (1993), *Asymptotic distribution of the likelihood ratio statistic in a prototypical non regular problem*, in *Statistics and Probability: A Raghu Raj Bahadur Festschrift*, Wiley Eastern, 83–96.
- K. Fukumizu (2003), *Likelihood ratio of unidentifiable models and multilayer neural networks*, Annals of Statistics 31(3), 833–851.
- L. Dümbgen and V. G. Spokoiny (2001), *Multiscale testing of qualitative hypotheses*, Annals of Statistics 29, 124–152.
- H. P. Chan and G. Walther (2013), *Detection with the scan and the average likelihood ratio*, Statistica Sinica 23, 409–428.
- E. V. Burnaev and G. K. Golubev (2017), *On One Problem in Multichannel Signal Detection*, Problems of Information Transmission 53(4).
- J. A. Hartigan (1985), *A failure of likelihood asymptotics for normal mixtures*, in *Proceedings of the Berkeley Conference in Honor of Jerzy Neyman and Jack Kiefer*, Vol. 2, 807–810.
- W. Hoeffding (1963), *Probability inequalities for sums of bounded random variables*, Journal of the American Statistical Association 58(301), 13–30.
- P. Lévy (1937), *Théorie de l'addition des variables aléatoires*, Gauthier-Villars.
- J.-M. Lion and J.-P. Rolin (1998), *Intégration des fonctions sous-analytiques et volumes des sous-ensembles sous-analytiques*, Annales de l'Institut Fourier 48(3), 755–767.
- X. Liu and Y. Shao (2004), *Asymptotics for the likelihood ratio test in a two-component normal mixture model*, Journal of Statistical Planning and Inference 123(1), 61–81.
- S. Nagayasu and S. Watanabe (2023), *Bayesian free energy of deep ReLU neural network in overparametrized cases*, arXiv:2303.15739.
- S. Watanabe (2009), *Algebraic Geometry and Statistical Learning Theory*, Cambridge University Press.

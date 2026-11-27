#import "@preview/arkheion:0.1.3": arkheion, arkheion-appendices

#show: arkheion.with(
  title: "Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic Volatility with Quadratic Drift",
  authors: (
    (name: "Gemini 4 Neon", email: "", affiliation: ""),
    (name: "Huayang WU", email: "huayang.bryan.wu[at]outlook.com", affiliation: ""),
  ),
  abstract: [
    We settle Conjecture 4.5 of Sepp and Rakhmonov (2026) on the necessity of the quadratic-damping threshold $kappa_2 >= beta$ for the asset price to be a true martingale in the rough log-normal stochastic volatility model with Riemann--Liouville fractional kernel $K(t) = t^(H-1\/2)\/Gamma(H+1\/2)$. Using a quadratic test function $phi(u) = (T-u)^2$ paired with the first-kind resolvent of $K$, a constant-drift Cameron--Martin tilt, and a Doléans--Dade exponential supermartingale that absorbs the quadratic variation without moment assumptions, we prove unconditionally that $EE_QQ[S_T] < S_0$ for every $T > 0$ whenever $beta > kappa_2$ and $H in (0, 1\/2]$. The argument bypasses the $K(0) = infinity$ obstruction of differential Feller tests, requires neither strict positivity of the volatility nor $L log L$ integrability, and simultaneously yields a self-contained unified proof of the classical diffusion result at $H = 1\/2$ (Sepp and Rakhmonov, 2023, Theorem 3.7).
  ],
  keywords: ("Rough volatility", "Stochastic Volterra equations", "Strict local martingales", "Quadratic drift", "Test-function method"),
  date: "November 26, 2026",
)

#show link: underline
#set par(justify: true)

// Helper for theorem-like blocks
#let thmblock(title, body) = block(
  width: 100%,
  inset: (left: 8pt, top: 6pt, bottom: 6pt, right: 6pt),
  stroke: (left: 1.5pt + luma(100)),
  [
    *#title.* #body
  ]
)

= Introduction

In a recent paper, #cite(<sepp2026rough>, form: "prose") extend the log-normal stochastic volatility model with quadratic drift of #cite(<sepp2023lognormal>, form: "prose") to a rough Volterra framework. Under the pricing measure $QQ$ with zero interest rates, the forward price $S_t$ and instantaneous volatility $sigma_t$ satisfy
$
  (dif S_t) / S_t &= sigma_t dif W_t^((0)), \
  sigma_t &= sigma_0 + integral_0^t K(t-s) [ (kappa_1 + kappa_2 sigma_s)(theta - sigma_s) dif s + beta sigma_s dif W_s^((0)) + epsilon.alt sigma_s dif W_s^((1)) ],
$ <eq:model>
where $W^((0)), W^((1))$ are independent Brownian motions, $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $beta in RR$, $epsilon.alt >= 0$, and $K$ is the Riemann--Liouville fractional kernel
$
  K(t) = t^(H - 1/2) / Gamma(H + 1/2) = t^(alpha - 1) / Gamma(alpha), quad H in (0, 1/2], quad alpha := H + 1/2 in (1/2, 1].
$ <eq:kernel>
Setting $theta.alt := sqrt(beta^2 + epsilon.alt^2)$ and $theta.alt dif W_t^sigma := beta dif W_t^((0)) + epsilon.alt dif W_t^((1))$, the drift polynomial takes the form $c_0 + c_1 sigma - kappa_2 sigma^2$ with $c_0 := kappa_1 theta >= 0$ and $c_1 := kappa_2 theta - kappa_1 in RR$.

A central question for derivative pricing under positive spot--volatility correlation ($beta > 0$) is when the discounted price $S$ is a true $QQ$-martingale rather than a strict local martingale (a financial bubble). #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) prove that $kappa_2 >= beta$ is *sufficient* for $S$ to be a true $QQ$-martingale on every finite horizon $[0, T]$ for all $H in (0, 1\/2]$. For smooth finite exponential mixtures $K^N(t) = sum_(i=1)^N w_i e^(-x_i t)$ (where $K^N(0) < infinity$), they also prove *necessity* #cite(<sepp2026rough>, supplement: [Proposition 4.4]) by invoking the differential semimartingale decomposition of #cite(<bondi2026feller>, form: "prose")\; see also #cite(<guyon2026martingale>, form: "prose"). Because the singular fractional kernel satisfies $K(0) = infinity$ for $H < 1\/2$, the volatility $sigma_t$ is not a semimartingale and differential Feller tests do not apply. #cite(<sepp2026rough>, form: "prose") therefore leave the converse open as *Conjecture 4.5*: for $H in (0, 1\/2)$, does $beta > kappa_2$ imply $EE_QQ[S_T] < S_0$ for every $T > 0$?

In this note we prove Conjecture 4.5 in full, and simultaneously recover the classical $H = 1\/2$ diffusion case #cite(<sepp2023lognormal>, supplement: [Theorem 3.7]) within a single unified framework. Our proof combines four elementary ingredients:
+ *Share-measure reduction*: assuming $EE_QQ[S_T] = S_0$ yields an equivalent measure $hat(QQ) tilde QQ$ under which the quadratic drift flips sign to $+q hat(sigma)_s^2$ with $q := beta - kappa_2 > 0$.
+ *Constant-drift Cameron--Martin tilt*: tilting $hat(QQ)$ by $exp(M hat(B)_T - 1/2 M^2 T)$ shifts the linear drift $c_1 |-> c_1 + theta.alt M -> +infinity$ on $[0, T]$ with zero support-theorem machinery, handling arbitrarily small $T > 0$ and arbitrarily strong linear mean reversion $c_1 < 0$.
+ *First-kind resolvent and quadratic test function*: convolving with the first-kind resolvent $L$ turns $hat(sigma)$ into a genuine continuous semimartingale $Z_t = (L * (hat(sigma) - sigma_0))_t$ even when $K(0) = infinity$. In the spirit of the Mitidieri--Pohozaev test-function method #cite(<mitidieri2001apriori>), testing $dif Z_u$ against $phi(u) = (T - u)^2$ works uniformly for all $H in (0, 1\/2]$ and confines the negative linear term to a shrinking endpoint layer $[T - delta_M, T]$ whose tail vanishes as $M -> infinity$.
+ *Doléans--Dade exponential supermartingale*: choosing $lambda = q \/ (theta.alt^2 T^2)$ absorbs the entire quadratic variation $1/2 lambda^2 chevron.l cal(M) chevron.r_T$ into half of the positive quadratic drift, yielding a deterministic pathwise lower bound that contradicts Fatou's lemma $EE_(hat(QQ)_M)[cal(E)_T(-lambda cal(M))] <= 1$ with no moment or $L log L$ assumptions.

= Main Result

#thmblock([Theorem 1 (Unified Martingale Necessity for All $H in (0, 1\/2]$)])[
  Let $(S, sigma)$ be the unique continuous global non-negative solution of @eq:model with kernel @eq:kernel for any $H in (0, 1\/2]$, $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $epsilon.alt >= 0$, and $beta in RR$ (so that $c_0 = kappa_1 theta >= 0$; see #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2])). If $beta > kappa_2$, then
  $
    EE_QQ[S_T] < S_0 quad "for every " T > 0.
  $ <eq:strict-local>
]

Combining Theorem 1 with #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) gives the complete characterization of martingality across the entire Hurst range $H in (0, 1\/2]$:

#thmblock("Corollary 2 (Exact Martingality Boundary)")[
  Under the parameter assumptions of Theorem 1, for every $H in (0, 1\/2]$ and every $T > 0$, the forward price $S$ in @eq:model is a true $QQ$-martingale on $[0, T]$ if and only if $kappa_2 >= beta$.
]

*Remark (Positivity and boundary-drift assumptions).* Theorem 1 does not rely on strict positivity of $sigma_t$ (#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])); it requires only almost-sure non-negativity $sigma_t >= 0$, which is already established in #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]). Moreover, the condition $c_0 >= 0$ is convenient rather than essential: if a continuous non-negative solution exists with $c_0 < 0$ and $EE_QQ[S_T] = S_0$, then the supermartingale property implies $EE_QQ[S_t] = S_0$ for all $t in (0, T]$; since $3 - alpha < 3$ for every $alpha in (1\/2, 1]$, choosing $t in (0, T]$ sufficiently small ensures $2 sigma_0 t^(3 - alpha) \/ Gamma(4 - alpha) + c_0 t^3 \/ 3 > 0$, and the same proof on $[0, t]$ yields a contradiction.

= Proof of Theorem 1

Fix $H in (0, 1\/2]$, set $alpha := H + 1\/2 in (1\/2, 1]$, and let $q := beta - kappa_2 > 0$. Since $kappa_2 >= 0$, we have $beta > 0$ and hence $theta.alt = sqrt(beta^2 + epsilon.alt^2) >= beta > 0$. Suppose for contradiction that there exists $T > 0$ such that $EE_QQ[S_T] = S_0$.

== Step 1: Share measure and constant-drift Cameron--Martin tilt

Since $sigma$ is continuous on $[0, T]$ $QQ$-a.s., we have $integral_0^T sigma_s^2 dif s < infinity$ $QQ$-a.s., so $S\/S_0 = cal(E)(integral_0^(dot.c) sigma_s dif W_s^((0)))$ is a strictly positive continuous $QQ$-local martingale and hence a $QQ$-supermartingale. The assumption $EE_QQ[S_T\/S_0] = 1$ therefore implies that $S\/S_0$ is a true $QQ$-martingale on $[0, T]$. Define the equivalent probability measure $hat(QQ) tilde QQ$ on $cal(F)_T$ by $dif hat(QQ)\/dif QQ |_(cal(F)_T) := S_T\/S_0$. By Girsanov's theorem,
$
  hat(B)_t := W_t^sigma - (beta / theta.alt) integral_0^t sigma_s dif s, quad t in [0, T],
$
is a standard $hat(QQ)$-Brownian motion, and $hat(sigma) := sigma$ is a $hat(QQ)$-a.s. continuous, finite, non-negative process on $[0, T]$ solving
$
  hat(sigma)_t = sigma_0 + integral_0^t K(t-s) [ c_0 + c_1 hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t K(t-s) theta.alt hat(sigma)_s dif hat(B)_s.
$

Now fix an arbitrary constant $M > 0$ such that $A_M := c_1 + theta.alt M > 0$, and define a second equivalent probability measure $hat(QQ)_M tilde hat(QQ)$ on $cal(F)_T$ via
$
  (dif hat(QQ)_M) / (dif hat(QQ)) bar_(cal(F)_T) := exp( M hat(B)_T - 1/2 M^2 T ).
$
Because $M$ is deterministic, Novikov's condition holds trivially, so $hat(QQ)_M$ is a genuine probability measure equivalent to $QQ$ on $cal(F)_T$, and $hat(B)_t^M := hat(B)_t - M t$ is a standard $hat(QQ)_M$-Brownian motion. By invariance of stochastic integrals under equivalent changes of measure, under $hat(QQ)_M$ the same continuous non-negative process $hat(sigma)$ satisfies
$
  hat(sigma)_t = sigma_0 + integral_0^t K(t-s) [ c_0 + A_M hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t K(t-s) theta.alt hat(sigma)_s dif hat(B)_s^M, quad t in [0, T].
$ <eq:tilted>

== Step 2: First-kind resolvent and quadratic test-function identity

Define the continuous $hat(QQ)_M$-semimartingale $Z$ on $[0, T]$ with $Z_0 = 0$ by
$
  Z_t := integral_0^t [ c_0 + A_M hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t theta.alt hat(sigma)_s dif hat(B)_s^M,
$
so that $hat(sigma) - sigma_0 = K * dif Z$ by @eq:tilted. Let $L$ be the non-negative resolvent of the first kind of $K$ (satisfying $K * L equiv 1$ and $L([0, T]) < infinity$):
$
  L(dif s) = cases(
    s^(-alpha) / Gamma(1 - alpha) dif s & "if " alpha in (1/2, 1),
    delta_0(dif s) & "if " alpha = 1.
  )
$
For each $n >= 1$, let $tau_n := inf{ t in [0, T] : hat(sigma)_t >= n } and T$, and consider the stopped semimartingale $Z_t^(tau_n) := Z_(t and tau_n)$ together with the convolved process $X_t^((n)) := (K * dif Z^(tau_n))_t$. Because $hat(sigma)_s <= n$ on $[0, tau_n]$, the drift and diffusion integrands of $Z^(tau_n)$ are uniformly bounded; applying the stochastic Fubini lemma of #cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6]) yields $(L * X^((n)))_t = ((L * K) * dif Z^(tau_n))_t = Z_t^(tau_n)$ for all $t in [0, T]$, $hat(QQ)_M$-a.s. By locality of the stochastic integral, on the event ${tau_n = T}$ we have $X_u^((n)) = hat(sigma)_u - sigma_0$ and $Z_u^(tau_n) = Z_u$ for every $u in [0, T]$. Since $hat(sigma)$ is continuous on $[0, T]$ $hat(QQ)_M$-a.s., we have $union.big_(n >= 1) {tau_n = T}$ of full $hat(QQ)_M$-measure, which gives the pathwise inversion
$
  Z_t = (L * (hat(sigma) - sigma_0))_t = integral_([0, t]) (hat(sigma)_(t-r) - sigma_0) L(dif r), quad forall t in [0, T], quad hat(QQ)_M"-a.s."
$ <eq:Z-inv>

Next, introduce the deterministic quadratic test function $phi(u) := (T - u)^2$ on $[0, T]$ and the continuous $hat(QQ)_M$-local martingale
$
  cal(M)_t := integral_0^t (T - u)^2 theta.alt hat(sigma)_u dif hat(B)_u^M, quad chevron.l cal(M) chevron.r_t = theta.alt^2 integral_0^t (T - u)^4 hat(sigma)_u^2 dif u.
$
Since $phi(T) = 0$, $phi'(u) = -2(T - u)$, and $Z_0 = 0$, Itô's integration-by-parts formula gives $hat(QQ)_M$-a.s.:
$
  integral_0^T (T - u)^2 dif Z_u = 2 integral_0^T (T - u) Z_u dif u.
$ <eq:ibp>
Evaluating the right-hand side of @eq:ibp via @eq:Z-inv and Fubini's theorem (valid pathwise since $hat(sigma)$ is continuous on $[0, T]$ and $L([0, T]) < infinity$), and changing variables $s = u - r$ ($r = u - s in [0, u]$) for the time coordinate of $hat(sigma)_s - sigma_0$, produces the *exact same formula* for both $alpha < 1$ and $alpha = 1$:
- For $alpha in (1\/2, 1)$:
  $
    2 integral_s^T (T - u) (u - s)^(-alpha) / Gamma(1 - alpha) dif u = 2 (T - s)^(2 - alpha) / Gamma(1 - alpha) Beta(2, 1 - alpha) = 2 (T - s)^(2 - alpha) / Gamma(3 - alpha).
  $
- For $alpha = 1$ ($H = 1\/2$, $L = delta_0$): $2 (T - s) = 2 (T - s)^(2 - 1) \/ Gamma(3 - 1)$.

Integrating the constant $-sigma_0$ term gives $integral_0^T 2 (T - s)^(2 - alpha)\/Gamma(3 - alpha) dif s = 2 T^(3 - alpha)\/Gamma(4 - alpha)$. Substituting into @eq:ibp and isolating $-cal(M)_T$ yields the exact pathwise identity ($hat(QQ)_M$-a.s.):
$
  -cal(M)_T = (2 sigma_0 T^(3 - alpha)) / Gamma(4 - alpha) + (c_0 T^3) / 3 + integral_0^T [ & q (T - u)^2 hat(sigma)_u^2 \
    & + ( A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) ) hat(sigma)_u ] dif u.
$ <eq:pathwise>

== Step 3: Doléans--Dade exponential supermartingale

Set $lambda := q \/ (theta.alt^2 T^2) > 0$. For each $n >= 1$, the stopped quadratic variation satisfies $chevron.l cal(M) chevron.r_(tau_n) <= theta.alt^2 n^2 T^5 \/ 5 < infinity$, so by Novikov's condition the stopped Doléans--Dade exponential $cal(E)_(t and tau_n)(-lambda cal(M)) := exp(-lambda cal(M)_(t and tau_n) - 1/2 lambda^2 chevron.l cal(M) chevron.r_(t and tau_n))$ is a true $hat(QQ)_M$-martingale with $EE_(hat(QQ)_M)[cal(E)_(tau_n)(-lambda cal(M))] = 1$. Since $tau_n = T$ for large $n$ almost surely and $cal(E) > 0$, Fatou's lemma yields
$
  EE_(hat(QQ)_M)[ exp( -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T ) ] <= 1.
$ <eq:fatou>

On $[0, T]$, we have $(T - u)^4 <= T^2 (T - u)^2$, hence by our choice of $lambda$:
$
  1/2 lambda^2 chevron.l cal(M) chevron.r_T &= 1/2 lambda^2 theta.alt^2 integral_0^T (T - u)^4 hat(sigma)_u^2 dif u \
  &<= 1/2 lambda^2 theta.alt^2 T^2 integral_0^T (T - u)^2 hat(sigma)_u^2 dif u = (lambda q) / 2 integral_0^T (T - u)^2 hat(sigma)_u^2 dif u.
$
Combining this bound with @eq:pathwise and dropping $c_0 T^3 \/ 3 >= 0$ gives, $hat(QQ)_M$-a.s.,
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ & (2 sigma_0 T^(3 - alpha)) / Gamma(4 - alpha) + integral_0^T ( q/2 (T - u)^2 hat(sigma)_u^2 \
    & + ( A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) ) hat(sigma)_u ) dif u ].
$ <eq:exp-lower>

== Step 4: Endpoint boundary-layer splitting and contradiction as $M -> infinity$

Define the boundary-layer thickness
$
  delta_M := ( 2 / (A_M Gamma(3 - alpha)) )^(1 / alpha) = ( 2 / ((c_1 + theta.alt M) Gamma(5/2 - H)) )^(1 / (H + 1/2)).
$
Choose $M$ large enough so that $A_M > 0$ and $delta_M <= T$, and split $[0, T] = [0, T - delta_M] union [T - delta_M, T]$:
- *Main interval $[0, T - delta_M]$*: For $T - u >= delta_M$, we have $A_M (T - u)^alpha >= 2 \/ Gamma(3 - alpha)$, so
  $
    A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) = (T - u)^(2 - alpha) ( A_M (T - u)^alpha - 2 / Gamma(3 - alpha) ) >= 0.
  $
  Since $hat(sigma)_u >= 0$, the entire integrand on $[0, T - delta_M]$ is non-negative and may be dropped.
- *Endpoint layer $[T - delta_M, T]$*: Dropping $A_M (T - u)^2 hat(sigma)_u >= 0$ and completing the square pointwise in $x = hat(sigma)_u$,
  $
    q/2 (T - u)^2 x^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) x >= - (2 (T - u)^(2 - 2 alpha)) / (q Gamma(3 - alpha)^2).
  $
  Since $alpha = H + 1\/2 <= 1$, the exponent satisfies $2 - 2 alpha = 1 - 2 H >= 0$ for *every* $H in (0, 1\/2]$, so the right-hand side is integrable on $[T - delta_M, T]$ with exact value
  $
    - 2 / (q Gamma(3 - alpha)^2) integral_(T - delta_M)^T (T - u)^(1 - 2 H) dif u = - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2).
  $

Substituting both estimates into @eq:exp-lower gives the deterministic pathwise lower bound ($hat(QQ)_M$-a.s.):
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ (2 sigma_0 T^(5/2 - H)) / Gamma(7/2 - H) - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2) ].
$ <eq:final-bound>
At the classical diffusion endpoint $H = 1\/2$ ($alpha = 1$), @eq:final-bound specializes cleanly to
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda ( sigma_0 T^2 - 4 / (q A_M) ).
$
For every $H in (0, 1\/2]$, we have $2 - 2 H >= 1 > 0$, so $delta_M^(2 - 2 H) -> 0$ as $M -> infinity$, whereas the first term $2 sigma_0 T^(5/2 - H) \/ Gamma(7/2 - H) > 0$ is independent of $M$. Choosing $M$ sufficiently large makes the right-hand side of @eq:final-bound strictly positive, say $>= epsilon.alt_0 > 0$. Taking expectations in @eq:fatou yields
$
  1 < e^(epsilon.alt_0) <= EE_(hat(QQ)_M)[ exp( -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T ) ] <= 1,
$
a contradiction. Hence $EE_QQ[S_T] < S_0$ for every $T > 0$. #h(1fr) $square$

= Quantitative Illustration and Remarks

To illustrate how explicitly the contradiction threshold in @eq:final-bound behaves even at very short maturities and under strong linear mean reversion, @tbl:params evaluates the required shift $M$, boundary-layer thickness $delta_M$, leading positive term $"LHS" = 2 sigma_0 T^(5/2 - H)\/Gamma(7/2 - H)$, and negative tail bound for the strong-mean-reversion benchmark of #cite(<sepp2026rough>, form: "prose", supplement: [Table 3]): $sigma_0 = 0.5$, $theta = 0.4$, $kappa_1 = 2.0$, $kappa_2 = 0$, $beta = 0.6$, $epsilon.alt = 0.8$ (so $c_1 = -2.0$, $q = 0.6$, $theta.alt = 1.0$) at $T = 0.01$ years ($approx 3.65$ days).

#figure(
  table(
    align: (center, right, right, right, right, right),
    columns: (auto, auto, auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*$H$*], [*$M$*], [*$delta_M$*], [*LHS*], [*Tail bound*], [*Margin (LHS $-$ Tail)*],
    [$0.10$], [$2.00 times 10^2$], [$3.29 times 10^(-4)$], [$5.32 times 10^(-6)$], [$6.45 times 10^(-7)$], [$+4.67 times 10^(-6)$],
    [$0.25$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.24 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.30 times 10^(-6)$],
    [$0.40$], [$1.96 times 10^4$], [$3.50 times 10^(-5)$], [$2.87 times 10^(-5)$], [$1.14 times 10^(-5)$], [$+1.73 times 10^(-5)$],
    [$0.50$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.00 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.50 times 10^(-5)$],
  ),
  caption: [Explicit contradiction parameters in @eq:final-bound at $T = 0.01$ years for $sigma_0 = 0.5$, $c_1 = -2.0$, $q = 0.6$, $theta.alt = 1.0$ across $H in (0, 1\/2]$.]
) <tbl:params>

Two concluding remarks are in order:
+ *General completely monotone kernels*: The proof relies only on $K in L^2([0, T])$ admitting a non-negative finite first-kind resolvent $L$ on $[0, T]$ (satisfying $K * L equiv 1$) such that the induced kernel weight $W_2(s) := 2 integral_([0, T - s]) (T - s - u) L(dif u)$ satisfies (i) $integral_0^T W_2(s) dif s > 0$, (ii) $sup_(s in [0, T - delta]) W_2(s) \/ (T - s)^2 < infinity$ for every $delta in (0, T)$, and (iii) $integral_0^T W_2(s)^2 \/ (T - s)^2 dif s < infinity$. Under these conditions, for any $delta in (0, T)$ choosing $A_M >= sup_(s in [0, T - delta]) W_2(s) \/ (T - s)^2$ makes the main-interval integrand non-negative, while absolute continuity of the Lebesgue integral forces the endpoint tail $integral_(T - delta)^T W_2(s)^2 \/ (2 q (T - s)^2) dif s -> 0$ as $delta arrow.b 0$. In particular, any singular kernel with $W_2(s) = O((T - s)^(2 - alpha))$ as $s arrow.t T$ for some $alpha < 3\/2$ (including the entire range $alpha in (1\/2, 1]$) is covered, complementing #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4]) and the smooth-kernel criteria of #cite(<guyon2026martingale>, form: "prose").
+ *Remaining open questions*: Our proof settles Conjecture 4.5 (martingale necessity) without addressing #cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3]) (almost-sure strict positivity of $sigma_t$ for $H < 1\/2$) or the stationary distribution under quadratic drift, both of which remain open.

#bibliography("bibliography.bib", title: "References")
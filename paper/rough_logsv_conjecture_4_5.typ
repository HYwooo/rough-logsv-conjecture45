#import "@preview/arkheion:0.1.3": arkheion, arkheion-appendices
#import "figures.typ": fig-boundary-layer, fig-tail-scaling

#show: arkheion.with(
  title: "Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic Volatility with Quadratic Drift",
  authors: (
    (name: "Huayang WU", email: "huayang.bryan.wu[at]outlook.com", affiliation: ""),
  ),
  abstract: [
    We settle Conjecture 4.5 of Sepp and Rakhmonov (2026) on the necessity of the quadratic-damping threshold $kappa_2 >= beta$ for the asset price to be a true martingale in the rough log-normal stochastic volatility model with Riemann--Liouville fractional kernel $K(t) = t^(H-1\/2)\/Gamma(H+1\/2)$. By pairing a quadratic test function $phi(u) = (T-u)^2$ with the first-kind resolvent of $K$, a constant-drift Cameron--Martin tilt, and a Doléans--Dade exponential supermartingale that absorbs the quadratic variation, we prove that $EE_QQ[S_T] < S_0$ for every $T > 0$ whenever $beta > kappa_2$ and $H in (0, 1\/2]$. The proof bypasses the $K(0) = infinity$ obstruction of differential Feller tests, requires no moment, $L log L$, or strict-positivity assumptions on the volatility, and recovers the classical diffusion result at $H = 1\/2$ (Sepp and Rakhmonov, 2023, Theorem 3.7) by the same argument. We also extend the method to a general theorem covering every non-zero completely monotone $L^2$ kernel (including Gamma tempered power-law kernels, finite and infinite exponential mixtures, and shifted power-law kernels) and contrast its scope with differential and Markovian explosion criteria.
  ],
  keywords: ("Rough volatility", "Stochastic Volterra equations", "Strict local martingales", "Quadratic drift", "Completely monotone kernels", "Test-function method"),
  date: "November 27, 2026",
)

#show link: underline
#set par(justify: true)
#show table: set par(justify: false)

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

#cite(<sepp2026rough>, form: "prose") extend the log-normal stochastic volatility model with quadratic drift of #cite(<sepp2023lognormal>, form: "prose") to a rough Volterra framework. Under the pricing measure $QQ$ with zero interest rates, the forward price $S_t$ and instantaneous volatility $sigma_t$ satisfy
$
  (dif S_t) / S_t &= sigma_t dif W_t^((0)), \
  sigma_t &= sigma_0 + integral_0^t K(t-s) [ (kappa_1 + kappa_2 sigma_s)(theta - sigma_s) dif s + beta sigma_s dif W_s^((0)) + epsilon.alt sigma_s dif W_s^((1)) ],
$ <eq:model>
where $W^((0)), W^((1))$ are independent Brownian motions, $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $beta in RR$, $epsilon.alt >= 0$, and $K$ is the Riemann--Liouville fractional kernel
$
  K(t) = t^(H - 1/2) / Gamma(H + 1/2) = t^(alpha - 1) / Gamma(alpha), quad H in (0, 1/2], quad alpha := H + 1/2 in (1/2, 1].
$ <eq:kernel>
Setting $theta.alt := sqrt(beta^2 + epsilon.alt^2)$ and $theta.alt dif W_t^sigma := beta dif W_t^((0)) + epsilon.alt dif W_t^((1))$, the drift polynomial takes the form $c_0 + c_1 sigma - kappa_2 sigma^2$ with $c_0 := kappa_1 theta >= 0$ and $c_1 := kappa_2 theta - kappa_1 in RR$.

Under positive spot--volatility correlation ($beta > 0$), a key pricing question is whether the discounted price $S$ is a true $QQ$-martingale rather than a strict local martingale (a financial bubble). #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) prove that $kappa_2 >= beta$ is sufficient for $S$ to be a true $QQ$-martingale on every finite horizon $[0, T]$ for all $H in (0, 1\/2]$. For smooth finite exponential mixtures $K^N(t) = sum_(i=1)^N w_i e^(-x_i t)$ (where $K^N(0) < infinity$), they also prove necessity #cite(<sepp2026rough>, supplement: [Proposition 4.4]) by invoking the differential semimartingale decomposition of #cite(<bondi2026feller>, form: "prose")\; see also #cite(<guyon2026martingale>, form: "prose"). Because the singular fractional kernel satisfies $K(0) = infinity$ for $H < 1\/2$, the volatility $sigma_t$ is not a semimartingale and differential Feller tests do not apply. #cite(<sepp2026rough>, form: "prose") therefore leave the converse open as *Conjecture 4.5*: for $H in (0, 1\/2)$, does $beta > kappa_2$ imply $EE_QQ[S_T] < S_0$ for every $T > 0$?

In this paper we prove Conjecture 4.5, recover the classical $H = 1\/2$ diffusion case #cite(<sepp2023lognormal>, supplement: [Theorem 3.7]) by the same argument, and establish a general necessity theorem for all non-zero completely monotone $L^2$ Volterra kernels. The proof combines four ingredients:
+ *Share-measure reduction*: assuming $EE_QQ[S_T] = S_0$ yields an equivalent measure $hat(QQ) tilde QQ$ under which the quadratic drift flips sign to $+q hat(sigma)_s^2$, where $q := beta - kappa_2 > 0$.
+ *Constant-drift Cameron--Martin tilt*: tilting $hat(QQ)$ by $exp(M hat(B)_T - 1/2 M^2 T)$ shifts the linear drift $c_1 |-> c_1 + theta.alt M -> +infinity$ on $[0, T]$ without support theorems, covering arbitrarily small $T > 0$ and strong linear mean reversion $c_1 < 0$.
+ *First-kind resolvent and quadratic test function*: convolving with the first-kind resolvent $L$ turns $hat(sigma)$ into a continuous semimartingale $Z_t = (L * (hat(sigma) - sigma_0))_t$ even when $K(0) = infinity$. In the spirit of the Mitidieri--Pohozaev test-function method #cite(<mitidieri2001apriori>), testing $dif Z_u$ against $phi(u) = (T - u)^2$ applies across all $H in (0, 1\/2]$ and confines the negative linear term to a shrinking layer $[T - delta_M, T]$ whose tail vanishes as $M -> infinity$.
+ *Doléans--Dade exponential supermartingale*: choosing $lambda = q \/ (theta.alt^2 T^2)$ absorbs the quadratic variation $1/2 lambda^2 chevron.l cal(M) chevron.r_T$ into half of the positive quadratic drift. The resulting deterministic lower bound contradicts Fatou's lemma $EE_(hat(QQ)_M)[cal(E)_T(-lambda cal(M))] <= 1$ without moment or $L log L$ assumptions.

= Main Result

#thmblock([Theorem 1 (Unified Martingale Necessity for All $H in (0, 1\/2]$)])[
  Let $(S, sigma)$ be the unique continuous global non-negative solution of @eq:model with kernel @eq:kernel for any $H in (0, 1\/2]$, $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $epsilon.alt >= 0$, and $beta in RR$ (so that $c_0 = kappa_1 theta >= 0$; see #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2])). If $beta > kappa_2$, then
  $
    EE_QQ[S_T] < S_0 quad "for every " T > 0.
  $ <eq:strict-local>
]

Combining Theorem 1 with #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) gives the characterization of martingality across the full Hurst range $H in (0, 1\/2]$:

#thmblock("Corollary 2 (Exact Martingality Boundary)")[
  Under the parameter assumptions of Theorem 1, for every $H in (0, 1\/2]$ and every $T > 0$, the forward price $S$ in @eq:model is a true $QQ$-martingale on $[0, T]$ if and only if $kappa_2 >= beta$.
]

*Remark (Positivity and boundary-drift assumptions).* Theorem 1 does not rely on strict positivity of $sigma_t$ (#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])); it requires only almost-sure non-negativity $sigma_t >= 0$, which is already established in #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]). Moreover, the condition $c_0 >= 0$ is convenient rather than essential. If a continuous non-negative solution exists with $c_0 < 0$ and $EE_QQ[S_T] = S_0$, then the supermartingale property gives $EE_QQ[S_t] = S_0$ for all $t in (0, T]$. Since $3 - alpha < 3$ for every $alpha in (1\/2, 1]$, choosing $t in (0, T]$ sufficiently small ensures $2 sigma_0 t^(3 - alpha) \/ Gamma(4 - alpha) + c_0 t^3 \/ 3 > 0$, and applying the same proof on $[0, t]$ yields a contradiction.

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
Because $M$ is deterministic, Novikov's condition holds, so $hat(QQ)_M$ is a probability measure equivalent to $QQ$ on $cal(F)_T$ and $hat(B)_t^M := hat(B)_t - M t$ is a standard $hat(QQ)_M$-Brownian motion. By invariance of stochastic integrals under equivalent changes of measure, under $hat(QQ)_M$ the same continuous non-negative process $hat(sigma)$ satisfies
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
For each $n >= 1$, let $tau_n := inf{ t in [0, T] : hat(sigma)_t >= n } and T$, and define the stopped semimartingale $Z_t^(tau_n) := Z_(t and tau_n)$ and convolved process $X_t^((n)) := (K * dif Z^(tau_n))_t$. Because $hat(sigma)_s <= n$ on $[0, tau_n]$, the drift and diffusion integrands of $Z^(tau_n)$ are uniformly bounded. Applying the stochastic Fubini lemma of #cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6]) yields $(L * X^((n)))_t = ((L * K) * dif Z^(tau_n))_t = Z_t^(tau_n)$ for all $t in [0, T]$, $hat(QQ)_M$-a.s. By locality of the stochastic integral, on the event ${tau_n = T}$ we have $X_u^((n)) = hat(sigma)_u - sigma_0$ and $Z_u^(tau_n) = Z_u$ for every $u in [0, T]$. Since $hat(sigma)$ is continuous on $[0, T]$ $hat(QQ)_M$-a.s., the union $union.big_(n >= 1) {tau_n = T}$ has full $hat(QQ)_M$-measure, giving the pathwise inversion
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
Evaluating the right-hand side of @eq:ibp via @eq:Z-inv and Fubini's theorem (valid pathwise since $hat(sigma)$ is continuous on $[0, T]$ and $L([0, T]) < infinity$), and changing variables $s = u - r$ ($r = u - s in [0, u]$) for the time coordinate of $hat(sigma)_s - sigma_0$, produces the same formula for both $alpha < 1$ and $alpha = 1$:
- For $alpha in (1\/2, 1)$:
  $
    2 integral_s^T (T - u) (u - s)^(-alpha) / Gamma(1 - alpha) dif u = 2 (T - s)^(2 - alpha) / Gamma(1 - alpha) Beta(2, 1 - alpha) = 2 (T - s)^(2 - alpha) / Gamma(3 - alpha).
  $
- For $alpha = 1$ ($H = 1\/2$, $L = delta_0$): $2 (T - s) = 2 (T - s)^(2 - 1) \/ Gamma(3 - 1)$.

Integrating the constant $-sigma_0$ term gives $integral_0^T 2 (T - s)^(2 - alpha)\/Gamma(3 - alpha) dif s = 2 T^(3 - alpha)\/Gamma(4 - alpha)$. Substituting into @eq:ibp and isolating $-cal(M)_T$ yields the pathwise identity ($hat(QQ)_M$-a.s.):
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
  Since $hat(sigma)_u >= 0$, the integrand on $[0, T - delta_M]$ is non-negative and may be dropped.
- *Endpoint layer $[T - delta_M, T]$*: Dropping $A_M (T - u)^2 hat(sigma)_u >= 0$ and completing the square pointwise in $x = hat(sigma)_u$,
  $
    q/2 (T - u)^2 x^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) x >= - (2 (T - u)^(2 - 2 alpha)) / (q Gamma(3 - alpha)^2).
  $
  Since $alpha = H + 1\/2 <= 1$, the exponent satisfies $2 - 2 alpha = 1 - 2 H >= 0$ for every $H in (0, 1\/2]$, so the right-hand side is integrable on $[T - delta_M, T]$ with exact value
  $
    - 2 / (q Gamma(3 - alpha)^2) integral_(T - delta_M)^T (T - u)^(1 - 2 H) dif u = - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2).
  $

Substituting both estimates into @eq:exp-lower gives the deterministic pathwise lower bound ($hat(QQ)_M$-a.s.):
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ (2 sigma_0 T^(5/2 - H)) / Gamma(7/2 - H) - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2) ].
$ <eq:final-bound>
@fig:boundary-layer illustrates how increasing $M$ shifts the zero crossing $T - delta_M$ toward $T$ and compresses the negative layer $[T - delta_M, T]$.

#figure(
  fig-boundary-layer(lang: "en"),
  caption: [Linear weight $c_M(u) = A_M (T - u)^2 - 2 (T - u)^(2 - alpha) \/ Gamma(3 - alpha)$ on $[0, T]$ for $T = 1$, $H = 0.25$ ($alpha = 0.75$), and three drift shifts $A_M in {2.2, 3.8, 7.0}$. On $[0, T - delta_M]$, $c_M(u) >= 0$; the negative endpoint layer $[T - delta_M, T]$ (shaded) contracts to zero as $M -> infinity$.]
) <fig:boundary-layer>

At the classical diffusion endpoint $H = 1\/2$ ($alpha = 1$), @eq:final-bound specializes to
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda ( sigma_0 T^2 - 4 / (q A_M) ).
$
For every $H in (0, 1\/2]$, we have $2 - 2 H >= 1 > 0$, so $delta_M^(2 - 2 H) -> 0$ as $M -> infinity$, whereas the first term $2 sigma_0 T^(5/2 - H) \/ Gamma(7/2 - H) > 0$ is independent of $M$. Choosing $M$ sufficiently large makes the right-hand side of @eq:final-bound strictly positive, say $>= epsilon.alt_0 > 0$. Taking expectations in @eq:fatou yields
$
  1 < e^(epsilon.alt_0) <= EE_(hat(QQ)_M)[ exp( -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T ) ] <= 1,
$
a contradiction. Hence $EE_QQ[S_T] < S_0$ for every $T > 0$. #h(1fr) $square$

= General Completely Monotone Kernels

The proof of Theorem 1 does not rely on the power-law algebra of the Riemann--Liouville kernel. The quadratic test-function mechanism extends to every Volterra kernel $K in L^2([0, T])$ admitting a non-negative finite resolvent of the first kind, and hence to all non-zero completely monotone $L^2$ kernels.

For any non-negative Borel measure $L$ on $[0, T]$ with $L([0, T]) < infinity$, define the induced quadratic kernel weight
$
  W_2(s) := 2 integral_([0, T - s]) (T - s - r) L(dif r), quad s in [0, T],
$ <eq:W2-def>
and its total mass $I_0(T) := integral_0^T W_2(s) dif s$.

#thmblock("Theorem 3 (Martingale Necessity for General Kernels with Non-Negative First-Kind Resolvent)")[
  Let $T > 0$ and let $K in L^2([0, T])$ be a kernel admitting a non-negative finite resolvent of the first kind $L$ on $[0, T]$, i.e., $L([0, T]) < infinity$ and $(K * L)(t) = integral_([0, t]) K(t - r) L(dif r) = 1$ for almost every $t in (0, T]$. Suppose $(S, sigma)$ is a continuous non-negative solution of @eq:model on $[0, T]$ with parameters $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $epsilon.alt >= 0$, and $beta > kappa_2$. Then:
  1. The induced weight @eq:W2-def automatically satisfies the three structural bounds:
     - *(i) Strictly positive leading mass*: $I_0(T) = integral_0^T W_2(s) dif s > 0$;
     - *(ii) Uniform main-interval dominance*: for every $delta in (0, T)$,
       $
         B(delta) := sup_(s in [0, T - delta]) (W_2(s)) / (T - s)^2 <= (2 L([0, T])) / delta < infinity;
       $
     - *(iii) Integrable endpoint tail*: $W_2(s) \/ (T - s) <= 2 L([0, T - s])$ for all $s in [0, T)$, whence
       $
         "Tail"(delta) := integral_(T - delta)^T (W_2(s)^2) / (2 q (T - s)^2) dif s <= (2 L([0, delta])^2 delta) / q -> 0 quad "as " delta arrow.b 0.
       $
  2. Consequently, the discounted forward price $S$ is a strict local martingale on $[0, T]$: $EE_QQ[S_T] < S_0$.
]

*Proof.* We first verify items (i)--(iii) directly from $L >= 0$ and $L([0, T]) < infinity$.

- *Verification of (i)*: Since $(K * L)(t) = 1$ for a.e. $t in (0, T]$, we must have $L([0, T\/2]) > 0$ (otherwise $K * L equiv 0$ on $(0, T\/2)$). For every $s in [0, T\/4]$ and $r in [0, T\/2]$, we have $T - s - r >= T\/4 > 0$, hence
  $
    W_2(s) >= 2 integral_([0, T\/2]) (T - s - r) L(dif r) >= T / 2 L([0, T\/2]) > 0,
  $
  and integrating over $s in [0, T\/4]$ yields $I_0(T) >= (T^2 \/ 8) L([0, T\/2]) > 0$.
- *Verification of (ii) and (iii)*: For every $s in [0, T)$ and $r in [0, T - s]$, non-negativity of $r$ gives $0 <= T - s - r <= T - s$. Integrating against $L >= 0$ yields the uniform bound
  $
    0 <= W_2(s) <= 2 (T - s) L([0, T - s]), quad s in [0, T).
  $ <eq:W2-uniform>
  Dividing @eq:W2-uniform by $(T - s)^2$ for $s in [0, T - delta]$ gives $B(delta) <= 2 L([0, T]) \/ delta < infinity$. Dividing @eq:W2-uniform by $T - s$, squaring, and integrating over $s in [T - delta, T]$ (with $v = T - s$) yields
  $
    "Tail"(delta) = integral_(T - delta)^T (W_2(s)^2) / (2 q (T - s)^2) dif s <= 2 / q integral_0^delta L([0, v])^2 dif v <= (2 L([0, delta])^2 delta) / q -> 0 quad (delta arrow.b 0),
  $
  since $L([0, delta]) <= L([0, T]) < infinity$.

We now prove $EE_QQ[S_T] < S_0$ by contradiction. Suppose $EE_QQ[S_T] = S_0$. Repeating Step 1 of Section 3 verbatim produces, for any constant $M > 0$ with $A_M := c_1 + theta.alt M > 0$, an equivalent probability measure $hat(QQ)_M tilde QQ$ and standard $hat(QQ)_M$-Brownian motion $hat(B)^M$ under which $hat(sigma)$ is continuous and non-negative on $[0, T]$ and satisfies $hat(sigma) - sigma_0 = K * dif Z$ with $Z$ given by Equation (8).

Because $K in L^2([0, T])$ and $L$ is a finite non-negative measure on $[0, T]$ with $K * L equiv 1$, the localization argument of Step 2 via $tau_n = inf{ t in [0, T] : hat(sigma)_t >= n } and T$ and #cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6]) applies unchanged and yields $Z_t = integral_([0, t]) (hat(sigma)_(t - r) - sigma_0) L(dif r)$ for all $t in [0, T]$, $hat(QQ)_M$-a.s. Integrating by parts against $phi(u) = (T - u)^2$ gives $integral_0^T (T - u)^2 dif Z_u = 2 integral_0^T (T - u) Z_u dif u$. Applying Fubini's theorem (justified pathwise by continuity of $hat(sigma)$ on $[0, T]$ and $L([0, T]) < infinity$) with $s = u - r$:
$
  2 integral_0^T (T - u) integral_([0, u]) (hat(sigma)_(u - r) - sigma_0) L(dif r) dif u &= integral_0^T (hat(sigma)_s - sigma_0) ( 2 integral_([0, T - s]) (T - s - r) L(dif r) ) dif s \
  &= integral_0^T W_2(s) (hat(sigma)_s - sigma_0) dif s.
$
Isolating $-cal(M)_T$ and combining with the Doléans--Dade supermartingale bound @eq:fatou and quadratic-variation domination $(1\/2) lambda^2 chevron.l cal(M) chevron.r_T <= (lambda q \/ 2) integral_0^T (T - u)^2 hat(sigma)_u^2 dif u$ (where $lambda = q \/ (theta.alt^2 T^2)$) gives, $hat(QQ)_M$-a.s.,
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ & sigma_0 I_0(T) + integral_0^T ( q / 2 (T - u)^2 hat(sigma)_u^2 \
    & + (A_M (T - u)^2 - W_2(u)) hat(sigma)_u ) dif u ].
$ <eq:general-exp-lower>
Now fix $delta in (0, T)$ small enough that $"Tail"(delta) <= (1\/2) sigma_0 I_0(T)$ (possible by (i) and (iii)), and choose $M > 0$ large enough that $A_M >= max{1, B(delta)}$ (possible by (ii) since $theta.alt >= beta > 0$). Splitting $[0, T] = [0, T - delta] union [T - delta, T]$:
- On $[0, T - delta]$, $A_M (T - u)^2 - W_2(u) >= (B(delta) - W_2(u) \/ (T - u)^2)(T - u)^2 >= 0$, so the entire integrand is non-negative and dropped.
- On $[T - delta, T]$, dropping $A_M (T - u)^2 hat(sigma)_u >= 0$ and completing the square pointwise in $x = hat(sigma)_u$ gives
  $
    q / 2 (T - u)^2 x^2 - W_2(u) x >= - (W_2(u)^2) / (2 q (T - u)^2),
  $
  whose integral over $[T - delta, T]$ is $-"Tail"(delta)$.

Substituting into @eq:general-exp-lower yields
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda ( sigma_0 I_0(T) - "Tail"(delta) ) >= 1/2 lambda sigma_0 I_0(T) =: epsilon.alt_0 > 0, quad hat(QQ)_M"-a.s."
$
Exponentiating and taking expectations in @eq:fatou gives $1 < e^(epsilon.alt_0) <= 1$, a contradiction. Hence $EE_QQ[S_T] < S_0$. #h(1fr) $square$

Recall that a kernel $K : (0, infinity) -> [0, infinity)$ is *completely monotone* if it is $C^infinity$ on $(0, infinity)$ with $(-1)^k K^((k))(t) >= 0$ for all $t > 0$ and $k >= 0$. By the classical theorem of #cite(<gripenberg1990volterra>, form: "prose", supplement: [Theorem 5.5.4]), every non-zero completely monotone kernel $K in L^1_"loc"(RR_+)$ admits a unique non-negative resolvent of the first kind $L$ with $L([0, T]) < infinity$ for every $T > 0$. Theorem 3 therefore yields:

#thmblock("Corollary 4 (All Non-Zero Completely Monotone L² Kernels)")[
  Let $K in L^2_"loc"(RR_+)$ be any non-zero completely monotone kernel, and assume @eq:model admits a continuous global non-negative solution $(S, sigma)$ with $sigma_0 > 0$, $theta > 0$, $kappa_1 >= 0$, $kappa_2 >= 0$, $epsilon.alt >= 0$, and $beta > kappa_2$. Then $EE_QQ[S_T] < S_0$ for every $T > 0$.
]

== Explicit Verification for Financial Volatility Kernels

We illustrate Theorem 3 and Corollary 4 on three canonical kernel families used in rough and multifactor stochastic volatility modeling.

*Example 1 (Gamma / tempered power-law kernel).* Consider the exponentially damped fractional kernel
$
  K_(alpha, eta)(t) := t^(alpha - 1) e^(-eta t) / Gamma(alpha), quad alpha = H + 1/2 in (1/2, 1), quad eta > 0,
$ <eq:gamma-kernel>
which combines rough short-time behavior ($K_(alpha, eta)(0) = infinity$) with exponential long-memory truncation. Its Laplace transform is $hat(K)_(alpha, eta)(zeta) = (zeta + eta)^(-alpha)$, so the Laplace transform of its first-kind resolvent satisfies
$
  hat(L)_(alpha, eta)(zeta) = (zeta + eta)^alpha / zeta = (zeta + eta)^(alpha - 1) + eta (zeta + eta)^(alpha - 1) / zeta.
$
Inverting term by term yields the strictly positive resolvent density
$
  L_(alpha, eta)(dif r) = ell_(alpha, eta)(r) dif r, quad ell_(alpha, eta)(r) := r^(-alpha) e^(-eta r) / Gamma(1 - alpha) + eta integral_0^r u^(-alpha) e^(-eta u) / Gamma(1 - alpha) dif u.
$
Changing order of integration in @eq:W2-def gives, for $v := T - s in [0, T]$, the exact weight
$
  W_2(T - v) = 1 / Gamma(1 - alpha) integral_0^v [ 2(v - u) + eta (v - u)^2 ] u^(-alpha) e^(-eta u) dif u.
$ <eq:W2-gamma>
In particular, $W_2(T - v) = (2 v^(2 - alpha)) \/ Gamma(3 - alpha) + O(v^(3 - alpha))$ as $v arrow.b 0$, so the endpoint tail decays at the exact same rate $O(M^(-(2 - 2 H) \/ (H + 1\/2)))$ as the untempered Riemann--Liouville kernel while $I_0(T)$ strictly increases with $eta$ (see @tbl:general-kernels).

*Example 2 (Finite and infinite exponential mixtures; multi-scale rough kernels).* By Bernstein's theorem, every non-zero completely monotone kernel admits the Laplace representation
$
  K_mu(t) = integral_([0, infinity)) e^(-x t) mu(dif x),
$
where $mu$ is a non-zero non-negative Radon measure on $[0, infinity)$. The condition $K_mu in L^2_"loc"(RR_+)$ is equivalent to $integral_([0, infinity)) (1 + x)^(-1\/2) mu(dif x) < infinity$, under which Corollary 4 applies directly:
- *Finite exponential mixtures (Markovian lifts)*: Taking $mu = sum_(i=1)^N w_i delta_(x_i)$ with $w_i > 0, x_i >= 0$ yields $K^N(t) = sum_(i=1)^N w_i e^(-x_i t)$. For the single-factor kernel $K(t) = w e^(-x t)$, the first-kind resolvent is explicit: $L(dif r) = w^(-1) delta_0(dif r) + (x \/ w) dif r$, giving
  $
    W_2(s) = (2 (T - s) + x (T - s)^2) / w, quad I_0(T) = T^2 / w + (x T^3) / (3 w),
  $
  and for $A_M > x\/w$ the crossing occurs at $delta_M = 2 \/ (w A_M - x)$ with exact tail bound
  $
    "Tail"(delta_M) = 1 / (2 q w^2) ( 4 delta_M + 2 x delta_M^2 + (x^2 delta_M^3) / 3 ).
  $
  For general $N >= 1$, Corollary 4 recovers #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4]) without invoking multidimensional Itô-diffusion explosion tests.
- *Infinite mixtures and multi-scale rough kernels*: Whenever $mu([0, infinity)) = infinity$ with $integral_([0, infinity)) (1 + x)^(-1\/2) mu(dif x) < infinity$, we have $K_mu(0) = infinity$ yet $K_mu in L^2([0, T])$. This includes two-scale fractional kernels $K(t) = w_1 t^(alpha_1 - 1)\/Gamma(alpha_1) + w_2 t^(alpha_2 - 1)\/Gamma(alpha_2)$ ($1\/2 < alpha_1 < alpha_2 <= 1, w_1, w_2 > 0$) used to fit short-dated skew alongside long-dated term structure. Even though $L$ has no elementary closed form, Corollary 4 establishes $EE_QQ[S_T] < S_0$ unconditionally.

*Example 3 (Shifted power-law kernel).* The regularized power-law kernel
$
  K_(alpha, epsilon)(t) := (t + epsilon)^(alpha - 1) = 1 / Gamma(1 - alpha) integral_0^infinity x^(-alpha) e^(-epsilon x) e^(-x t) dif x, quad alpha in (1/2, 1), quad epsilon > 0,
$
is smooth and completely monotone ($K_(alpha, epsilon)(0) = epsilon^(alpha - 1) < infinity$), and is widely used as a smooth proxy for rough volatility. Corollary 4 covers every $epsilon > 0$ and connects to the singular limit $epsilon arrow.b 0$ (Theorem 1) by the same proof.

= Comparison with Existing Methods and Quantitative Illustrations

== Scope Comparison with Differential and Markovian Criteria

To situate Theorem 1 and Theorem 3 within the recent Volterra martingality literature, @tbl:comparison contrasts our test-function approach with the classical diffusion test of #cite(<sepp2023lognormal>, form: "prose"), the Feller/Khasminskii explosion criteria of #cite(<bondi2026feller>, form: "prose"), the Volterra martingality framework of #cite(<guyon2026martingale>, form: "prose"), and the finite-mixture converse of #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4]).

#figure(
  table(
    align: (left, left, left, left),
    columns: (auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*Method / Reference*], [*Admissible Kernels for Necessity*], [*Key Mechanism*], [*Regularity & Structural Needs*],
    [Sepp & Rakhmonov #cite(<sepp2023lognormal>)], [Constant ($H = 1\/2$)], [1D Feller explosion test], [Markovian diffusion; Itô generator],
    [Bondi & Pulido #cite(<bondi2026feller>)], [Nonsingular ($K(0) < infinity$, $K in W^(1,1)$) & finite $K^N$], [Semimartingale Feller / Khasminskii test], [Semimartingale state or $N$-dim lift],
    [Guyon et al. #cite(<guyon2026martingale>)], [Smooth kernels (sufficiency allows rough $K$)], [Explosion criterion for smooth Volterra SDEs], [Smooth $K$; growth Assumption 1.2 fails for $kappa_2 > 0$],
    [Sepp & Rakhmonov #cite(<sepp2026rough>, supplement: [Prop. 4.4])], [Positive finite mixtures $K^N$], [Differential reduction via #cite(<bondi2026feller>)], [$K^N(0) < infinity$],
    [*This paper (Thm. 3 / Cor. 4)*], [*All non-zero completely monotone $K in L^2$ (both $K(0) < infinity$ and $K(0) = infinity$)*], [*First-kind resolvent + quadratic test function + Cameron--Martin tilt + Doléans--Dade supermartingale*], [*Only $sigma_t >= 0$ a.s. & $L >= 0$ finite; no semimartingale, strict positivity, or $L log L$*],
  ),
  caption: [Comparison of martingale necessity (strict local martingality) criteria for log-normal Volterra stochastic volatility models.]
) <tbl:comparison>

*Methodological boundaries.* While Theorem 3 removes the $K(0) < infinity$ barrier and unifies smooth and singular completely monotone kernels, two structural boundaries define its natural scope:
1. *Sign of the first-kind resolvent*: The uniform bound @eq:W2-uniform and the non-negativity of the dropped integrand on $[0, T - delta]$ rely on $L >= 0$ (guaranteed for all completely monotone kernels) and $hat(sigma)_u >= 0$. For oscillatory or non-completely-monotone kernels whose first-kind resolvent changes sign, $W_2(s)$ can become negative and the comparison sign is no longer preserved.
2. *Drift--diffusion growth balance*: Absorbing $(1\/2) lambda^2 chevron.l cal(M) chevron.r_T$ into $(q\/2) integral_0^T (T - u)^2 hat(sigma)_u^2 dif u$ relies on the share-measure quadratic drift $+q hat(sigma)^2$ matching the quadratic variation order $theta.alt^2 hat(sigma)^2$. Models whose volatility diffusion grows strictly faster than the square root of the tilted drift would require alternative test functions or localization techniques.

== Quantitative Illustrations

To illustrate the contradiction threshold in @eq:final-bound at short maturity and under strong linear mean reversion, @tbl:params evaluates the required shift $M$, boundary-layer thickness $delta_M$, leading positive term $"LHS" = 2 sigma_0 T^(5/2 - H)\/Gamma(7/2 - H)$, and negative tail bound for the strong-mean-reversion benchmark of #cite(<sepp2026rough>, form: "prose", supplement: [Table 3]): $sigma_0 = 0.5$, $theta = 0.4$, $kappa_1 = 2.0$, $kappa_2 = 0$, $beta = 0.6$, $epsilon.alt = 0.8$ (so $c_1 = -2.0$, $q = 0.6$, $theta.alt = 1.0$) at $T = 0.01$ years ($approx 3.65$ days).

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

@fig:tail-scaling shows the log--log decay of the endpoint tail bound against the $M$-independent threshold $"LHS"_H$ for the benchmark parameters of @tbl:params.

#figure(
  fig-tail-scaling(lang: "en"),
  caption: [Decay of the endpoint tail bound $delta_M^(2 - 2 H) \/ (q (1 - H) Gamma(5\/2 - H)^2)$ as a function of $M$ for the parameters of @tbl:params (solid lines, plotted on $delta_M <= T$), compared against the $M$-independent leading term $"LHS"_H$ (dashed lines). Marked points correspond to the choices of $M$ in @tbl:params.]
) <fig:tail-scaling>

To illustrate Theorem 3 beyond the pure Riemann--Liouville family, @tbl:general-kernels evaluates the leading term $"LHS" = sigma_0 I_0(T)$, crossing thickness $delta_M$, and endpoint tail bound for the Gamma (tempered power-law) kernel @eq:gamma-kernel at $H = 0.25$ (via @eq:W2-gamma) and the single-factor exponential kernel $K(t) = e^(-x t)$ (Example 2) under the same benchmark parameters ($T = 0.01$, $sigma_0 = 0.5$, $c_1 = -2.0$, $q = 0.6$, $theta.alt = 1.0$).

#figure(
  table(
    align: (left, center, right, right, right, right, right),
    columns: (auto, auto, auto, auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*Kernel Family*], [*Decay*], [*$M$*], [*$delta_M$*], [*LHS*], [*Tail bound*], [*Margin*],
    [Gamma ($H = 0.25$)], [$eta = 0$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.24 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.30 times 10^(-6)$],
    [Gamma ($H = 0.25$)], [$eta = 5$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.25 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.44 times 10^(-6)$],
    [Gamma ($H = 0.25$)], [$eta = 20$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.30 times 10^(-5)$], [$3.12 times 10^(-6)$], [$+9.86 times 10^(-6)$],
    [Gamma ($H = 0.25$)], [$eta = 50$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.38 times 10^(-5)$], [$3.13 times 10^(-6)$], [$+1.07 times 10^(-5)$],
    [Exponential $e^(-x t)$], [$x = 0$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.00 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.50 times 10^(-5)$],
    [Exponential $e^(-x t)$], [$x = 5$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.08 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.59 times 10^(-5)$],
    [Exponential $e^(-x t)$], [$x = 20$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.33 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.84 times 10^(-5)$],
    [Exponential $e^(-x t)$], [$x = 50$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.83 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+3.34 times 10^(-5)$],
  ),
  caption: [Contradiction parameters of Theorem 3 at $T = 0.01$ years ($sigma_0 = 0.5$, $c_1 = -2.0$, $q = 0.6$, $theta.alt = 1.0$) for the Gamma kernel $K_(0.75, eta)$ and single-factor exponential kernel $e^(-x t)$. Increasing exponential damping enlarges the leading term $"LHS"$ while changing the short-layer tail only slightly.]
) <tbl:general-kernels>

As @tbl:general-kernels shows, introducing exponential tempering ($eta > 0$ or $x > 0$) adds a non-negative integral component to the first-kind resolvent $L$, which strictly enlarges the global mass $I_0(T)$ (and hence $"LHS"$) while affecting the thin endpoint layer $[T - delta_M, T]$ only at higher order $O(eta delta_M)$, strictly widening the contradiction margin.

*Remaining open questions.* Our results settle Conjecture 4.5 (martingale necessity) for the fractional kernel and all non-zero completely monotone $L^2$ kernels without addressing #cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3]) (almost-sure strict positivity of $sigma_t$ for $H < 1\/2$) or the stationary distribution under quadratic drift, both of which remain open.

*Acknowledgments.* The author acknowledges Google's large language model Gemini 4 Neon #cite(<google2026gemini>) for assistance with proof drafting, Typst typesetting, and auxiliary Lean 4 formalization.

#bibliography("bibliography.bib", title: "References")

#import "figures.typ": fig-boundary-layer, fig-tail-scaling

#set document(
  title: "具有二次漂移的粗糙对数正态随机波动率模型鞅性必要条件猜想的证明",
  author: ("Huayang WU",),
)

#set page(
  paper: "a4",
  margin: (x: 2.3cm, y: 2.3cm),
  numbering: "1",
)

#set text(
  font: ("New Computer Modern", "Noto Serif SC"),
  size: 10.5pt,
  lang: "zh",
  region: "cn",
)

#set par(
  justify: true,
  leading: 0.72em,
  spacing: 0.9em,
)

#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)", supplement: [式])
#show heading: it => {
  set text(font: ("New Computer Modern", "Noto Serif SC"), weight: "bold")
  v(0.5em)
  it
  v(0.3em)
}

#show link: underline

#let thmblock(title, body) = block(
  width: 100%,
  inset: (left: 8pt, top: 6pt, bottom: 6pt, right: 6pt),
  stroke: (left: 1.5pt + luma(100)),
  [
    *#title。* #body
  ]
)

// 标题与作者区
#align(center)[
  #text(size: 14.5pt, weight: "bold")[
    具有二次漂移的粗糙对数正态随机波动率模型\
    鞅性必要条件猜想的证明
  ]
  #v(0.8em)
  #text(size: 10.5pt)[
    Huayang WU（`huayang.bryan.wu[at]outlook.com`）
  ]
  #v(0.4em)
  #text(size: 9.5pt, fill: luma(80))[2026 年 11 月 26 日]
]

#v(0.6em)

// 摘要与关键词
#block(
  width: 100%,
  inset: (x: 10pt, y: 8pt),
  fill: luma(248),
  radius: 3pt,
)[
  #set text(size: 9.5pt)
  *摘要：* 本文完整证明了 Sepp 与 Rakhmonov（2026）关于带 Riemann--Liouville 分数阶核 $K(t) = t^(H-1\/2)\/Gamma(H+1\/2)$ 的粗糙对数正态随机波动率模型鞅性必要条件的猜想 4.5，即二次阻尼阈值 $kappa_2 >= beta$ 是资产价格成为真鞅的必要条件。通过将二次检验函数 $phi(u) = (T-u)^2$ 与核函数 $K$ 的第一类预解核配对，结合常漂移 Cameron--Martin 测度变换以及吸收二次变差的 Doléans--Dade 指数上鞅，我们证明：只要 $beta > kappa_2$ 且 $H in (0, 1\/2]$，对任意 $T > 0$ 均有 $EE_QQ[S_T] < S_0$。该证明绕开了微分 Feller 检验在 $K(0) = infinity$ 处的奇性障碍，不需要对波动率施加严格正性、矩条件或 $L log L$ 可积性假设，并由同一论证统一推得 $H = 1\/2$ 时的经典扩散情形（Sepp 与 Rakhmonov，2023，定理 3.7）。

  #v(0.35em)
  *关键词：* 粗糙波动率；随机 Volterra 方程；严格局部鞅；二次漂移；检验函数法
]

#v(0.4em)

= 引言

#cite(<sepp2026rough>, form: "prose") 将 #cite(<sepp2023lognormal>, form: "prose") 提出的具有二次漂移的对数正态随机波动率模型推广至粗糙 Volterra 框架。在零利率定价测度 $QQ$ 下，远期价格 $S_t$ 与瞬时波动率 $sigma_t$ 满足
$
  (dif S_t) / S_t &= sigma_t dif W_t^((0)), \
  sigma_t &= sigma_0 + integral_0^t K(t-s) [ (kappa_1 + kappa_2 sigma_s)(theta - sigma_s) dif s + beta sigma_s dif W_s^((0)) + epsilon.alt sigma_s dif W_s^((1)) ],
$ <eq:model>
其中 $W^((0)), W^((1))$ 为相互独立的标准布朗运动，$sigma_0 > 0$，$theta > 0$，$kappa_1 >= 0$，$kappa_2 >= 0$，$beta in RR$，$epsilon.alt >= 0$，$K$ 为 Riemann--Liouville 分数阶核：
$
  K(t) = t^(H - 1/2) / Gamma(H + 1/2) = t^(alpha - 1) / Gamma(alpha), quad H in (0, 1/2], quad alpha := H + 1/2 in (1/2, 1].
$ <eq:kernel>
令 $theta.alt := sqrt(beta^2 + epsilon.alt^2)$ 及 $theta.alt dif W_t^sigma := beta dif W_t^((0)) + epsilon.alt dif W_t^((1))$，则漂移多项式可写为 $c_0 + c_1 sigma - kappa_2 sigma^2$，其中 $c_0 := kappa_1 theta >= 0$，$c_1 := kappa_2 theta - kappa_1 in RR$。

在正的现货--波动率相关性（$beta > 0$）情形下，衍生品定价的一个关键问题是判定贴现资产价格 $S$ 究竟是真 $QQ$-鞅还是严格局部鞅（即存在金融泡沫）。#cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) 证明了对于所有 $H in (0, 1\/2]$，条件 $kappa_2 >= beta$ 足以保证 $S$ 在任意有限期限 $[0, T]$ 上为真 $QQ$-鞅。对于光滑的有限指数和核 $K^N(t) = sum_(i=1)^N w_i e^(-x_i t)$（此时 $K^N(0) < infinity$），他们还利用 #cite(<bondi2026feller>, form: "prose") 的微分半鞅分解证明了该条件的必要性 #cite(<sepp2026rough>, supplement: [Proposition 4.4])；另参见 #cite(<guyon2026martingale>, form: "prose")。然而，当 $H < 1\/2$ 时奇异分数阶核满足 $K(0) = infinity$，波动率过程 $sigma_t$ 不再是半鞅，微分 Feller 检验不再适用。因此 #cite(<sepp2026rough>, form: "prose") 将其逆命题作为*猜想 4.5（Conjecture 4.5）*保留：对 $H in (0, 1\/2)$，当 $beta > kappa_2$ 时，是否对任意 $T > 0$ 均有 $EE_QQ[S_T] < S_0$？

本文证明了猜想 4.5，并由同一论证直接涵盖 $H = 1\/2$ 的经典扩散情形 #cite(<sepp2023lognormal>, supplement: [Theorem 3.7])。证明结合了以下四个核心步骤：
+ *计价单位测度归约*：反设 $EE_QQ[S_T] = S_0$，可得等价测度 $hat(QQ) tilde QQ$，使二次漂移项反号为 $+q hat(sigma)_s^2$，其中 $q := beta - kappa_2 > 0$。
+ *常漂移 Cameron--Martin 倾斜*：通过密度 $exp(M hat(B)_T - 1/2 M^2 T)$ 构造倾斜测度 $hat(QQ)_M$，无需支集定理即可将线性漂移系数推移至 $c_1 |-> c_1 + theta.alt M -> +infinity$，从而自然处理任意短期限 $T > 0$ 与任意强的线性均值回归（$c_1 < 0$）。
+ *第一类预解核与二次检验函数*：即使 $K(0) = infinity$，将 $hat(sigma) - sigma_0$ 与第一类预解核 $L$ 作卷积仍可得到连续半鞅 $Z_t = (L * (hat(sigma) - sigma_0))_t$。借鉴 Mitidieri--Pohozaev 检验函数思想 #cite(<mitidieri2001apriori>)，用 $phi(u) = (T - u)^2$ 检验 $dif Z_u$ 可对全体 $H in (0, 1\/2]$ 统一处理，并将负线性项限制在随 $M -> infinity$ 收缩至零的端点边界层 $[T - delta_M, T]$ 内。
+ *Doléans--Dade 指数上鞅吸收*：选取 $lambda = q \/ (theta.alt^2 T^2)$，将二次变差项 $1/2 lambda^2 chevron.l cal(M) chevron.r_T$ 完全吸收进半数正二次漂移项中，从而在不依赖任何矩假设或 $L log L$ 条件的前提下，获得与 Fatou 引理 $EE_(hat(QQ)_M)[cal(E)_T(-lambda cal(M))] <= 1$ 矛盾的确定性逐轨下界。

= 主要结果

#thmblock([定理 1（适用于全体 $H in (0, 1\/2]$ 的统一鞅性必要条件）])[
  设 $(S, sigma)$ 为由 @eq:model 与核函数 @eq:kernel 定义的唯一连续全局非负解，其中 $H in (0, 1\/2]$，$sigma_0 > 0$，$theta > 0$，$kappa_1 >= 0$，$kappa_2 >= 0$，$epsilon.alt >= 0$ 且 $beta in RR$（于是 $c_0 = kappa_1 theta >= 0$；参见 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2])）。若 $beta > kappa_2$，则
  $
    EE_QQ[S_T] < S_0, quad forall T > 0.
  $ <eq:strict-local>
]

将定理 1 与 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) 结合，即可得到整个 Hurst 区间 $H in (0, 1\/2]$ 上的真鞅刻画边界：

#thmblock("推论 2（精确鞅性边界）")[
  在定理 1 的参数假设下，对任意 $H in (0, 1\/2]$ 与任意 $T > 0$，@eq:model 中的远期价格 $S$ 在 $[0, T]$ 上为真 $QQ$-鞅当且仅当 $kappa_2 >= beta$。
]

*注（严格正性与边界漂移假设）。* 定理 1 并不依赖 $sigma_t$ 的严格正性（#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])），仅要求 $sigma_t >= 0$ a.s.，而这一性质已由 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]) 建立。此外，条件 $c_0 >= 0$ 仅为行文便利而非本质限制。若当 $c_0 < 0$ 时存在连续非负解且 $EE_QQ[S_T] = S_0$，则由上鞅性质对所有 $t in (0, T]$ 均有 $EE_QQ[S_t] = S_0$。由于对任意 $alpha in (1\/2, 1]$ 都有 $3 - alpha < 3$，取充分小的 $t in (0, T]$ 即可保证 $2 sigma_0 t^(3 - alpha) \/ Gamma(4 - alpha) + c_0 t^3 \/ 3 > 0$，进而在 $[0, t]$ 上沿用同一证明即可导出矛盾。

= 定理 1 的证明

固定 $H in (0, 1\/2]$，记 $alpha := H + 1\/2 in (1\/2, 1]$ 及 $q := beta - kappa_2 > 0$。由于 $kappa_2 >= 0$，有 $beta > 0$，从而 $theta.alt = sqrt(beta^2 + epsilon.alt^2) >= beta > 0$。反设存在某个 $T > 0$ 使得 $EE_QQ[S_T] = S_0$。

== 第一步：计价单位测度与常漂移 Cameron--Martin 倾斜

由于 $sigma$ 在 $[0, T]$ 上 $QQ$-a.s. 连续，故 $integral_0^T sigma_s^2 dif s < infinity$ $QQ$-a.s.，从而 $S\/S_0 = cal(E)(integral_0^(dot.c) sigma_s dif W_s^((0)))$ 是严格正连续 $QQ$-局部鞅，亦即 $QQ$-上鞅。假设 $EE_QQ[S_T\/S_0] = 1$ 蕴含 $S\/S_0$ 在 $[0, T]$ 上为真 $QQ$-鞅。由此在 $cal(F)_T$ 上定义等价概率测度 $hat(QQ) tilde QQ$，其 Radon--Nikodym 导数为 $dif hat(QQ)\/dif QQ |_(cal(F)_T) := S_T\/S_0$。由 Girsanov 定理，
$
  hat(B)_t := W_t^sigma - (beta / theta.alt) integral_0^t sigma_s dif s, quad t in [0, T],
$
为标准 $hat(QQ)$-布朗运动，且 $hat(sigma) := sigma$ 在 $[0, T]$ 上是 $hat(QQ)$-a.s. 连续、有限的非负过程，满足
$
  hat(sigma)_t = sigma_0 + integral_0^t K(t-s) [ c_0 + c_1 hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t K(t-s) theta.alt hat(sigma)_s dif hat(B)_s.
$

任取充分大的常数 $M > 0$ 使 $A_M := c_1 + theta.alt M > 0$，并在 $cal(F)_T$ 上通过下式定义第二个等价概率测度 $hat(QQ)_M tilde hat(QQ)$：
$
  (dif hat(QQ)_M) / (dif hat(QQ)) bar_(cal(F)_T) := exp( M hat(B)_T - 1/2 M^2 T ).
$
因为 $M$ 为确定性常数，Novikov 条件自动成立，故 $hat(QQ)_M$ 是与 $QQ$ 在 $cal(F)_T$ 上等价的概率测度，且 $hat(B)_t^M := hat(B)_t - M t$ 为标准 $hat(QQ)_M$-布朗运动。由随机积分在等价测度变换下的不变性，同一连续非负过程 $hat(sigma)$ 在 $hat(QQ)_M$ 下满足
$
  hat(sigma)_t = sigma_0 + integral_0^t K(t-s) [ c_0 + A_M hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t K(t-s) theta.alt hat(sigma)_s dif hat(B)_s^M, quad t in [0, T].
$ <eq:tilted>

== 第二步：第一类预解核与二次检验函数恒等式

在 $[0, T]$ 上定义满足 $Z_0 = 0$ 的连续 $hat(QQ)_M$-半鞅 $Z$：
$
  Z_t := integral_0^t [ c_0 + A_M hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t theta.alt hat(sigma)_s dif hat(B)_s^M,
$
则由 @eq:tilted 有 $hat(sigma) - sigma_0 = K * dif Z$。令 $L$ 为 $K$ 的非负第一类预解核（满足 $K * L equiv 1$ 且 $L([0, T]) < infinity$）：
$
  L(dif s) = cases(
    s^(-alpha) / Gamma(1 - alpha) dif s & "若 " alpha in (1/2, 1),
    delta_0(dif s) & "若 " alpha = 1.
  )
$
对每个 $n >= 1$，定义停时 $tau_n := inf{ t in [0, T] : hat(sigma)_t >= n } and T$，以及停过程 $Z_t^(tau_n) := Z_(t and tau_n)$ 与卷积过程 $X_t^((n)) := (K * dif Z^(tau_n))_t$。在 $[0, tau_n]$ 上因 $hat(sigma)_s <= n$，半鞅 $Z^(tau_n)$ 的漂移与扩散被积函数一致有界。应用 #cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6]) 的随机 Fubini 引理，可得对所有 $t in [0, T]$ 均有 $(L * X^((n)))_t = ((L * K) * dif Z^(tau_n))_t = Z_t^(tau_n)$，$hat(QQ)_M$-a.s.。由随机积分的局部性，在事件 ${tau_n = T}$ 上对所有 $u in [0, T]$ 均有 $X_u^((n)) = hat(sigma)_u - sigma_0$ 且 $Z_u^(tau_n) = Z_u$。又因 $hat(sigma)$ 在 $[0, T]$ 上 $hat(QQ)_M$-a.s. 连续，并集 $union.big_(n >= 1) {tau_n = T}$ 具有 $hat(QQ)_M$ 全测度，由此得到逐轨反演公式：
$
  Z_t = (L * (hat(sigma) - sigma_0))_t = integral_([0, t]) (hat(sigma)_(t-r) - sigma_0) L(dif r), quad forall t in [0, T], quad hat(QQ)_M"-a.s."
$ <eq:Z-inv>

进一步，引入 $[0, T]$ 上的确定性二次检验函数 $phi(u) := (T - u)^2$ 与连续 $hat(QQ)_M$-局部鞅
$
  cal(M)_t := integral_0^t (T - u)^2 theta.alt hat(sigma)_u dif hat(B)_u^M, quad chevron.l cal(M) chevron.r_t = theta.alt^2 integral_0^t (T - u)^4 hat(sigma)_u^2 dif u.
$
由 $phi(T) = 0$、$phi'(u) = -2(T - u)$ 及 $Z_0 = 0$，Itô 分部积分公式给出（$hat(QQ)_M$-a.s.）：
$
  integral_0^T (T - u)^2 dif Z_u = 2 integral_0^T (T - u) Z_u dif u.
$ <eq:ibp>
将 @eq:Z-inv 代入 @eq:ibp 右端并应用 Fubini 定理（因 $hat(sigma)$ 在 $[0, T]$ 上连续且 $L([0, T]) < infinity$，故逐轨成立），对 $hat(sigma)_s - sigma_0$ 的时间坐标作变量替换 $s = u - r$（即 $r = u - s in [0, u]$），对 $alpha < 1$ 与 $alpha = 1$ 均得到完全相同的积分核：
- 当 $alpha in (1\/2, 1)$ 时：
  $
    2 integral_s^T (T - u) (u - s)^(-alpha) / Gamma(1 - alpha) dif u = 2 (T - s)^(2 - alpha) / Gamma(1 - alpha) Beta(2, 1 - alpha) = 2 (T - s)^(2 - alpha) / Gamma(3 - alpha).
  $
- 当 $alpha = 1$（即 $H = 1\/2$，$L = delta_0$）时：$2 (T - s) = 2 (T - s)^(2 - 1) \/ Gamma(3 - 1)$。

对常数项 $-sigma_0$ 积分得 $integral_0^T 2 (T - s)^(2 - alpha)\/Gamma(3 - alpha) dif s = 2 T^(3 - alpha)\/Gamma(4 - alpha)$。将其代回 @eq:ibp 并整理 $-cal(M)_T$，便得到逐轨恒等式（$hat(QQ)_M$-a.s.）：
$
  -cal(M)_T = (2 sigma_0 T^(3 - alpha)) / Gamma(4 - alpha) + (c_0 T^3) / 3 + integral_0^T [ & q (T - u)^2 hat(sigma)_u^2 \
    & + ( A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) ) hat(sigma)_u ] dif u.
$ <eq:pathwise>

== 第三步：Doléans--Dade 指数上鞅估计

令 $lambda := q \/ (theta.alt^2 T^2) > 0$。对每个 $n >= 1$，停过程二次变差满足 $chevron.l cal(M) chevron.r_(tau_n) <= theta.alt^2 n^2 T^5 \/ 5 < infinity$，故由 Novikov 条件可知停过程 Doléans--Dade 指数 $cal(E)_(t and tau_n)(-lambda cal(M)) := exp(-lambda cal(M)_(t and tau_n) - 1/2 lambda^2 chevron.l cal(M) chevron.r_(t and tau_n))$ 为真 $hat(QQ)_M$-鞅，满足 $EE_(hat(QQ)_M)[cal(E)_(tau_n)(-lambda cal(M))] = 1$。由于对充分大的 $n$ 几乎必然有 $tau_n = T$ 且 $cal(E) > 0$，由 Fatou 引理得
$
  EE_(hat(QQ)_M)[ exp( -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T ) ] <= 1.
$ <eq:fatou>

在 $[0, T]$ 上有 $(T - u)^4 <= T^2 (T - u)^2$，结合 $lambda$ 的选取可得
$
  1/2 lambda^2 chevron.l cal(M) chevron.r_T &= 1/2 lambda^2 theta.alt^2 integral_0^T (T - u)^4 hat(sigma)_u^2 dif u \
  &<= 1/2 lambda^2 theta.alt^2 T^2 integral_0^T (T - u)^2 hat(sigma)_u^2 dif u = (lambda q) / 2 integral_0^T (T - u)^2 hat(sigma)_u^2 dif u.
$
将该上界与 @eq:pathwise 结合，并舍去非负项 $c_0 T^3 \/ 3 >= 0$，即得（$hat(QQ)_M$-a.s.）：
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ & (2 sigma_0 T^(3 - alpha)) / Gamma(4 - alpha) + integral_0^T ( q/2 (T - u)^2 hat(sigma)_u^2 \
    & + ( A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) ) hat(sigma)_u ) dif u ].
$ <eq:exp-lower>

== 第四步：端点边界层分解与 $M -> infinity$ 矛盾

定义边界层厚度
$
  delta_M := ( 2 / (A_M Gamma(3 - alpha)) )^(1 / alpha) = ( 2 / ((c_1 + theta.alt M) Gamma(5/2 - H)) )^(1 / (H + 1/2)).
$
取充分大的 $M$ 使得 $A_M > 0$ 且 $delta_M <= T$，并将区间分解为 $[0, T] = [0, T - delta_M] union [T - delta_M, T]$：
- *主区间 $[0, T - delta_M]$*：当 $T - u >= delta_M$ 时有 $A_M (T - u)^alpha >= 2 \/ Gamma(3 - alpha)$，故
  $
    A_M (T - u)^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) = (T - u)^(2 - alpha) ( A_M (T - u)^alpha - 2 / Gamma(3 - alpha) ) >= 0.
  $
  因 $hat(sigma)_u >= 0$，主区间上的被积函数恒非负，可直接舍去。
- *端点边界层 $[T - delta_M, T]$*：舍去 $A_M (T - u)^2 hat(sigma)_u >= 0$ 并对 $x = hat(sigma)_u$ 逐点配方，
  $
    q/2 (T - u)^2 x^2 - (2 (T - u)^(2 - alpha)) / Gamma(3 - alpha) x >= - (2 (T - u)^(2 - 2 alpha)) / (q Gamma(3 - alpha)^2).
  $
  由于 $alpha = H + 1\/2 <= 1$，指数满足 $2 - 2 alpha = 1 - 2 H >= 0$ 对所有 $H in (0, 1\/2]$ 恒成立，因此右端项在 $[T - delta_M, T]$ 上必然可积，其精确积分为
  $
    - 2 / (q Gamma(3 - alpha)^2) integral_(T - delta_M)^T (T - u)^(1 - 2 H) dif u = - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2).
  $

将两段估计代入 @eq:exp-lower，即得确定性逐轨下界（$hat(QQ)_M$-a.s.）：
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ (2 sigma_0 T^(5/2 - H)) / Gamma(7/2 - H) - delta_M^(2 - 2 H) / (q (1 - H) Gamma(5/2 - H)^2) ].
$ <eq:final-bound>
@fig:boundary-layer 直观展示了增大 $M$ 如何将零点 $T - delta_M$ 推向终点 $T$，从而不断压缩负贡献边界层 $[T - delta_M, T]$。

#figure(
  fig-boundary-layer(lang: "zh"),
  caption: [线性权重 $c_M(u) = A_M (T - u)^2 - 2 (T - u)^(2 - alpha) \/ Gamma(3 - alpha)$ 在 $[0, T]$ 上的分布（取 $T = 1$，$H = 0.25$ 即 $alpha = 0.75$，以及三组漂移强度 $A_M in {2.2, 3.8, 7.0}$）。在主区间 $[0, T - delta_M]$ 上恒有 $c_M(u) >= 0$；阴影所示的端点负层 $[T - delta_M, T]$ 随 $M -> infinity$ 收缩至零。]
) <fig:boundary-layer>

在经典扩散端点 $H = 1\/2$（$alpha = 1$）处，@eq:final-bound 简化为
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda ( sigma_0 T^2 - 4 / (q A_M) ).
$
对一切 $H in (0, 1\/2]$ 均有 $2 - 2 H >= 1 > 0$，故当 $M -> infinity$ 时 $delta_M^(2 - 2 H) -> 0$，而第一项 $2 sigma_0 T^(5/2 - H) \/ Gamma(7/2 - H) > 0$ 与 $M$ 无关。取充分大的 $M$ 可使 @eq:final-bound 右端严格为正（记其下界为 $epsilon.alt_0 > 0$）。在 @eq:fatou 中取期望可得
$
  1 < e^(epsilon.alt_0) <= EE_(hat(QQ)_M)[ exp( -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T ) ] <= 1,
$
矛盾。因此对任意 $T > 0$ 必有 $EE_QQ[S_T] < S_0$。 #h(1fr) $square$

= 数值算例与注记

为定量展示 @eq:final-bound 中的矛盾阈值在短期限与强线性均值回归下的表现，@tbl:params 采用 #cite(<sepp2026rough>, form: "prose", supplement: [Table 3]) 的强均值回归基准参数：$sigma_0 = 0.5$、$theta = 0.4$、$kappa_1 = 2.0$、$kappa_2 = 0$、$beta = 0.6$、$epsilon.alt = 0.8$（对应 $c_1 = -2.0$、$q = 0.6$、$theta.alt = 1.0$），在 $T = 0.01$ 年（约 $3.65$ 天）处给出所需漂移参数 $M$、边界层厚度 $delta_M$、正主导项 $"LHS" = 2 sigma_0 T^(5/2 - H)\/Gamma(7/2 - H)$ 以及负尾项上界。

#figure(
  table(
    align: (center, right, right, right, right, right),
    columns: (auto, auto, auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*$H$*], [*$M$*], [*$delta_M$*], [*LHS*], [*尾项界*], [*净余量 (LHS $-$ 尾项)*],
    [$0.10$], [$2.00 times 10^2$], [$3.29 times 10^(-4)$], [$5.32 times 10^(-6)$], [$6.45 times 10^(-7)$], [$+4.67 times 10^(-6)$],
    [$0.25$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.24 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.30 times 10^(-6)$],
    [$0.40$], [$1.96 times 10^4$], [$3.50 times 10^(-5)$], [$2.87 times 10^(-5)$], [$1.14 times 10^(-5)$], [$+1.73 times 10^(-5)$],
    [$0.50$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.00 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.50 times 10^(-5)$],
  ),
  caption: [强均值回归基准参数（$T = 0.01$ 年，$sigma_0 = 0.5$，$c_1 = -2.0$，$q = 0.6$，$theta.alt = 1.0$）下 @eq:final-bound 的显式阈值与余量。]
) <tbl:params>

@fig:tail-scaling 在双对数坐标下绘出了端点尾项界随 $M$ 的衰减曲线与不依赖 $M$ 的阈值 $"LHS"_H$ 之间的对比关系。

#figure(
  fig-tail-scaling(lang: "zh"),
  caption: [对应 @tbl:params 基准参数的端点尾项界 $delta_M^(2 - 2 H) \/ (q (1 - H) Gamma(5\/2 - H)^2)$ 随 $M$ 的衰减曲线（实线，仅绘制 $delta_M <= T$ 区域）与固定阈值 $"LHS"_H$（虚线）。圆点对应 @tbl:params 中选取的 $M$ 值。]
) <fig:tail-scaling>

最后给出两点注记：
+ *一般完全单调核的推广*：上述证明仅依赖核函数 $K in L^2([0, T])$ 在 $[0, T]$ 上存在满足 $K * L equiv 1$ 的非负有限第一类预解核 $L$，且导出权重 $W_2(s) := 2 integral_([0, T - s]) (T - s - u) L(dif u)$ 满足：(i) $integral_0^T W_2(s) dif s > 0$；(ii) 对任意 $delta in (0, T)$ 有 $sup_(s in [0, T - delta]) W_2(s) \/ (T - s)^2 < infinity$；以及 (iii) $integral_0^T W_2(s)^2 \/ (T - s)^2 dif s < infinity$。在这些条件下，对任意 $delta in (0, T)$ 只需取 $A_M >= sup_(s in [0, T - delta]) W_2(s) \/ (T - s)^2$ 即可保证主区间被积函数非负，同时 Lebesgue 积分的绝对连续性迫使端点尾项 $integral_(T - delta)^T W_2(s)^2 \/ (2 q (T - s)^2) dif s -> 0$（当 $delta arrow.b 0$）。特别地，任意在 $s arrow.t T$ 处满足 $W_2(s) = O((T - s)^(2 - alpha))$（$alpha < 3\/2$，涵盖整个区间 $alpha in (1\/2, 1]$）的奇异核均适用本方法，从而与 #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4]) 及 #cite(<guyon2026martingale>, form: "prose") 的光滑核判据形成互补。
+ *遗留公开问题*：本文证明了猜想 4.5（鞅性必要条件），但并未涉及 $H < 1\/2$ 时 $sigma_t$ 的几乎必然严格正性（#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])）以及二次漂移下的平稳分布问题，这两者目前仍处于开放状态。

*致谢与人工智能工具使用说明。* 作者感谢 Google 开发的大语言模型 Gemini 4 Neon #cite(<google2026gemini>) 在证明梳理、Typst 排版及 Lean 4 形式化过程中提供的辅助支持；文中全部数学推导、数值验证与最终内容均由自然人作者 Huayang WU 独立核验并承担完全学术责任。

#bibliography("bibliography.bib", title: "参考文献")

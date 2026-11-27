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
#show table: set par(justify: false)

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
  #text(size: 9.5pt, fill: luma(80))[2026 年 11 月 27 日]
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
  *摘要：* 本文完整证明了 Sepp 与 Rakhmonov（2026）关于带 Riemann--Liouville 分数阶核 $K(t) = t^(H-1\/2)\/Gamma(H+1\/2)$ 的粗糙对数正态随机波动率模型鞅性必要条件的猜想 4.5，即二次阻尼阈值 $kappa_2 >= beta$ 是资产价格成为真鞅的必要条件。通过将二次检验函数 $phi(u) = (T-u)^2$ 与核函数 $K$ 的第一类预解核配对，结合常漂移 Cameron--Martin 测度变换以及吸收二次变差的 Doléans--Dade 指数上鞅，我们证明：只要 $beta > kappa_2$ 且 $H in (0, 1\/2]$，对任意 $T > 0$ 均有 $EE_QQ[S_T] < S_0$。该证明绕开了微分 Feller 检验在 $K(0) = infinity$ 处的奇性障碍，不需要对波动率施加严格正性、矩条件或 $L log L$ 可积性假设，并由同一论证统一推得 $H = 1\/2$ 时的经典扩散情形（Sepp 与 Rakhmonov，2023，定理 3.7）。进一步地，我们将该方法推广为适用于全体非零完全单调 $L^2$ 核（涵盖 Gamma 缓和幂律核、有限与无限指数混合核以及平移幂律核）的一般性定理，并将其适用范围与微分及 Markov 型爆炸判据作了系统对比。

  #v(0.35em)
  *关键词：* 粗糙波动率；随机 Volterra 方程；严格局部鞅；二次漂移；完全单调核；检验函数法
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

本文证明了猜想 4.5，由同一论证统一涵盖 $H = 1\/2$ 的经典扩散情形 #cite(<sepp2023lognormal>, supplement: [Theorem 3.7])，并进一步建立适用于全体非零完全单调 $L^2$ Volterra 核的一般鞅性必要条件定理。证明结合了以下四个核心步骤：
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
  对任意 $H in (0, 1\/2]$、$sigma_0 > 0$、$theta > 0$、$kappa_1 >= 0$、$kappa_2 >= 0$、$epsilon.alt >= 0$、$beta in RR$ 及任意 $T > 0$，@eq:model 中的远期价格 $S$ 在 $[0, T]$ 上为真 $QQ$-鞅当且仅当 $kappa_2 >= beta$。
]

*证明。* 必要性（$kappa_2 >= beta$）由定理 1 在上述全部参数下给出。对于充分性（$kappa_2 >= beta$），#cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) 在其基本设定 $epsilon.alt > 0$ 下对所有 $H in (0, 1\/2]$ 与 $kappa_1 >= 0$ 证明了该结论（其适定性依据 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]) 仅要求 $c_0 = kappa_1 theta >= 0$ 与 $theta.alt >= 0$；在 $H = 1\/2$ 处亦参见 #cite(<sepp2023lognormal>, form: "prose", supplement: [Theorem 3.7])）。在边界 $epsilon.alt = 0$ 处：若 $beta != 0$，则 $theta.alt = abs(beta) > 0$，#cite(<sepp2026rough>, form: "prose", supplement: [Theorem 4.3]) 的证明原封不动适用；若 $beta = epsilon.alt = 0$，则 $theta.alt = 0$，由 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]) 知 $sigma$ 为 $[0, T]$ 上的确定性有界函数，故 $S$ 亦为真 $QQ$-鞅。 #h(1fr) $square$

*注（严格正性、初始波动率退化与边界漂移假设）。* 定理 1 并不依赖 $sigma_t$ 的严格正性（#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])），仅要求 $sigma_t >= 0$ a.s.，而这一性质已由 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]) 建立。需要指出的是，当 $sigma_0 = kappa_1 = 0$（即 $c_0 = 0$）时，平凡解 $sigma equiv 0$ 与 $S equiv S_0$ 在 $beta > kappa_2$ 时仍为真鞅，说明 $sigma_0 > 0$ 与 $c_0 > 0$ 不能同时省略。反之，由于 #cite(<sepp2026rough>, form: "prose", supplement: [Theorem 2.2]) 本身允许 $sigma_0 >= 0$，在 $sigma_0 = 0$ 且 $c_0 = kappa_1 theta > 0$ 下同样存在唯一的连续全局非负强解；此时只要在 @eq:exp-lower（以及定理 3 中的 @eq:general-exp-lower）中保留正常数项 $(c_0 T^3) \/ 3 > 0$，其余论证无需本质改动即可导出同样矛盾。此外，条件 $c_0 >= 0$ 仅为行文便利而非本质限制。若当 $c_0 < 0$ 时存在连续非负解且 $EE_QQ[S_T] = S_0$，则由上鞅性质对所有 $t in (0, T]$ 均有 $EE_QQ[S_t] = S_0$。由于对任意 $alpha in (1\/2, 1]$ 都有 $3 - alpha < 3$，取充分小的 $t in (0, T]$ 即可保证 $2 sigma_0 t^(3 - alpha) \/ Gamma(4 - alpha) + c_0 t^3 \/ 3 > 0$，进而在 $[0, t]$ 上沿用同一证明即可导出矛盾。

= 定理 1 的证明

固定 $H in (0, 1\/2]$，记 $alpha := H + 1\/2 in (1\/2, 1]$ 及 $q := beta - kappa_2 > 0$。由于 $kappa_2 >= 0$，有 $beta > 0$，从而 $theta.alt = sqrt(beta^2 + epsilon.alt^2) >= beta > 0$。反设存在某个 $T > 0$ 使得 $EE_QQ[S_T] = S_0$。

== 第一步：计价单位测度与常漂移 Cameron--Martin 倾斜

由于 $sigma$ 在 $[0, T]$ 上 $QQ$-a.s. 连续，故 $integral_0^T sigma_s^2 dif s < infinity$ $QQ$-a.s.，从而 $S\/S_0 = cal(E)(integral_0^(dot.c) sigma_s dif W_s^((0)))$ 是严格正连续 $QQ$-局部鞅，亦即 $QQ$-上鞅。假设 $EE_QQ[S_T\/S_0] = 1$ 蕴含 $S\/S_0$ 在 $[0, T]$ 上为真 $QQ$-鞅。由此在 $cal(F)_T$ 上定义等价概率测度 $hat(QQ) tilde QQ$，其 Radon--Nikodym 导数为 $dif hat(QQ)\/dif QQ |_(cal(F)_T) := S_T\/S_0$。由 Girsanov 定理，
$
  hat(B)_t := W_t^sigma - (beta / theta.alt) integral_0^t sigma_s dif s, quad t in [0, T],
$
为标准 $hat(QQ)$-布朗运动。对每个固定的 $t in [0, T]$，由 $sigma$ 连续性与 $K in L^2([0, T])$ 可得 $integral_0^t K(t-s)^2 sigma_s^2 dif s < infinity$ $QQ$-a.s.；经停时 $tau_n := inf{ u in [0, T] : sigma_u >= n } and T$ 局部化后，Girsanov 定理及等价测度变换下随机积分的不变性保证该 Volterra 方程对每个 $t in [0, T]$ 几乎必然保持漂移修正关系（进而由 $hat(sigma) := sigma$ 的样本路径连续性在 $[0, T]$ 上一致成立）。于是 $hat(sigma)$ 在 $[0, T]$ 上是 $hat(QQ)$-a.s. 连续、有限的非负过程，满足
$
  hat(sigma)_t = sigma_0 + integral_0^t K(t-s) [ c_0 + c_1 hat(sigma)_s + q hat(sigma)_s^2 ] dif s + integral_0^t K(t-s) theta.alt hat(sigma)_s dif hat(B)_s.
$

任取充分大的常数 $M > 0$ 使 $A_M := c_1 + theta.alt M > 0$，并在 $cal(F)_T$ 上通过下式定义第二个等价概率测度 $hat(QQ)_M tilde hat(QQ)$：
$
  (dif hat(QQ)_M) / (dif hat(QQ)) bar_(cal(F)_T) := exp( M hat(B)_T - 1/2 M^2 T ).
$
因为 $M$ 为确定性常数，Novikov 条件自动成立，故 $hat(QQ)_M$ 是与 $QQ$ 在 $cal(F)_T$ 上等价的概率测度，且 $hat(B)_t^M := hat(B)_t - M t$ 为标准 $hat(QQ)_M$-布朗运动。由同样的局部化论证与等价测度变换下随机积分的不变性，同一连续非负过程 $hat(sigma)$ 在 $hat(QQ)_M$ 下满足
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
对每个 $n >= 1$，定义停时 $tau_n := inf{ t in [0, T] : hat(sigma)_t >= n } and T$、停过程 $Z_t^(tau_n) := Z_(t and tau_n)$，以及卷积过程 $X_t^((n)) := (K * dif Z^(tau_n))_t$ 的一个联合可测修正。在 $[0, tau_n]$ 上因 $hat(sigma)_s <= n$，半鞅 $Z^(tau_n)$ 的漂移与扩散被积函数一致有界。应用 #cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6]) 的随机 Fubini 引理，可得对 Lebesgue-a.e. $t in [0, T]$ 均有 $(L * X^((n)))_t = ((L * K) * dif Z^(tau_n))_t = Z_t^(tau_n)$，$hat(QQ)_M$-a.s.。此外，由随机积分的局部性，对每个固定的 $u in [0, T]$，在事件 ${tau_n = T}$ 上 $hat(QQ)_M$-a.s. 成立 $X_u^((n)) = hat(sigma)_u - sigma_0$ 且 $Z_u^(tau_n) = Z_u$；由乘积空间 $Omega times [0, T]$ 上的 Tonelli 定理，在 ${tau_n = T}$ 上上述等式对 Lebesgue-a.e. $u in [0, T]$ 成立，$hat(QQ)_M$-a.s.。由于 $L$ 是 $[0, T]$ 上的有限非负 Borel 测度，与 $L$ 作卷积保持 Lebesgue 零测集不变（由 Tonelli 定理，即便 $L$ 在 $0$ 处含原子亦成立）。再取 $union.big_(n >= 1) {tau_n = T}$（由 $hat(sigma)$ 样本连续性知其具有 $hat(QQ)_M$ 全测度），便得对 Lebesgue-a.e. $t in [0, T]$ 成立 $Z_t = (L * (hat(sigma) - sigma_0))_t$，$hat(QQ)_M$-a.s.。最后，由于左端 $Z$ 连续，而零延拓 $u |-> (hat(sigma)_u - sigma_0) bb(1)_({u >= 0})$ 在 $RR$ 上连续（因 $hat(sigma)_0 - sigma_0 = 0$），由控制收敛定理可知右端对任意有限测度 $L$ 亦关于 $t in [0, T]$ 连续，从而得到逐轨反演公式：
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
将该上界与 @eq:pathwise 结合，即得（$hat(QQ)_M$-a.s.）：
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ & (2 sigma_0 T^(3 - alpha)) / Gamma(4 - alpha) + (c_0 T^3) / 3 + integral_0^T ( q/2 (T - u)^2 hat(sigma)_u^2 \
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

舍去非负项 $(c_0 T^3) \/ 3 >= 0$ 并将两段估计代入 @eq:exp-lower，即得确定性逐轨下界（$hat(QQ)_M$-a.s.）：
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

= 一般完全单调核

定理 1 的证明并不依赖 Riemann--Liouville 核的幂律代数结构。二次检验函数机制可无条件推广至任意存在非负有限第一类预解核的 Volterra 核 $K in L^2([0, T])$，从而涵盖全体非零完全单调 $L^2$ 核。

对 $[0, T]$ 上任意满足 $L([0, T]) < infinity$ 的非负 Borel 测度 $L$，定义其导出的二次核权重
$
  W_2(s) := 2 integral_([0, T - s]) (T - s - r) L(dif r), quad s in [0, T],
$ <eq:W2-def>
及其总质量 $I_0(T) := integral_0^T W_2(s) dif s$。

#thmblock("定理 3（具非负第一类预解核的一般核函数鞅性必要条件）")[
  设 $T > 0$，$K in L^2([0, T])$ 在 $[0, T]$ 上存在非负有限第一类预解核 $L$，即 $L([0, T]) < infinity$ 且对几乎所有 $t in (0, T]$ 满足 $(K * L)(t) = integral_([0, t]) K(t - r) L(dif r) = 1$。假设 $(S, sigma)$ 为 @eq:model 在 $[0, T]$ 上的连续非负解，且参数满足 $sigma_0 > 0$，$theta > 0$，$kappa_1 >= 0$，$kappa_2 >= 0$，$epsilon.alt >= 0$ 及 $beta > kappa_2$。则：
  1. 导出权重 @eq:W2-def 自动满足三条结构估计：
     - *(i) 严格正主导质量*：$I_0(T) = integral_0^T W_2(s) dif s > 0$；
     - *(ii) 主区间一致控制*：对任意 $delta in (0, T)$，
       $
         B(delta) := sup_(s in [0, T - delta]) (W_2(s)) / (T - s)^2 <= (2 L([0, T])) / delta < infinity;
       $
     - *(iii) 端点尾项可积衰减*：对所有 $s in [0, T)$ 均有 $W_2(s) \/ (T - s) <= 2 L([0, T - s])$，从而
       $
         "Tail"(delta) := integral_(T - delta)^T (W_2(s)^2) / (2 q (T - s)^2) dif s <= (2 L([0, delta])^2 delta) / q -> 0 quad ("当 " delta arrow.b 0).
       $
  2. 因此，贴现远期价格 $S$ 在 $[0, T]$ 上为严格局部鞅：$EE_QQ[S_T] < S_0$。
]

*证明。* 我们先由 $L >= 0$ 与 $L([0, T]) < infinity$ 直接验证性质 (i)--(iii)。

- *验证 (i)*：由于对几乎所有 $t in (0, T]$ 有 $(K * L)(t) = 1$，必有 $L([0, T\/2]) > 0$（否则在 $(0, T\/2)$ 上 $K * L equiv 0$）。对任意 $s in [0, T\/4]$ 与 $r in [0, T\/2]$，均有 $T - s - r >= T\/4 > 0$，于是
  $
    W_2(s) >= 2 integral_([0, T\/2]) (T - s - r) L(dif r) >= T / 2 L([0, T\/2]) > 0,
  $
  在 $s in [0, T\/4]$ 上积分即得 $I_0(T) >= (T^2 \/ 8) L([0, T\/2]) > 0$。
- *验证 (ii) 与 (iii)*：对任意 $s in [0, T)$ 与 $r in [0, T - s]$，由 $r >= 0$ 有 $0 <= T - s - r <= T - s$。对 $L >= 0$ 积分即得一致上界：
  $
    0 <= W_2(s) <= 2 (T - s) L([0, T - s]), quad s in [0, T).
  $ <eq:W2-uniform>
  在 $s in [0, T - delta]$ 上将 @eq:W2-uniform 两边除以 $(T - s)^2$ 即得 $B(delta) <= 2 L([0, T]) \/ delta < infinity$。将 @eq:W2-uniform 两边除以 $T - s$、平方并在 $s in [T - delta, T]$ 上积分（令 $v = T - s$），可得
  $
    "Tail"(delta) = integral_(T - delta)^T (W_2(s)^2) / (2 q (T - s)^2) dif s <= 2 / q integral_0^delta L([0, v])^2 dif v <= (2 L([0, delta])^2 delta) / q -> 0 quad (delta arrow.b 0),
  $
  这里用到了 $L([0, delta]) <= L([0, T]) < infinity$。

接下来用反证法证明 $EE_QQ[S_T] < S_0$。反设 $EE_QQ[S_T] = S_0$。逐字沿用第 3 节第一步，对任意使 $A_M := c_1 + theta.alt M > 0$ 的常数 $M > 0$，均可构造等价概率测度 $hat(QQ)_M tilde QQ$ 及标准 $hat(QQ)_M$-布朗运动 $hat(B)^M$，使得 $hat(sigma)$ 在 $[0, T]$ 上连续非负且满足 $hat(sigma) - sigma_0 = K * dif Z$，其中 $Z$ 由 式 8 给出。

因 $K in L^2([0, T])$ 且 $L$ 为 $[0, T]$ 上满足 $K * L equiv 1$ 的非负有限测度，第 3.2 节基于停时 $tau_n = inf{ t in [0, T] : hat(sigma)_t >= n } and T$、取 $X^((n)) := (K * dif Z^(tau_n))$ 联合可测修正、#cite(<abijaber2019affine>, form: "prose", supplement: [Lemma 2.6])、乘积空间 Tonelli 定理以及由 $hat(sigma)_0 - sigma_0 = 0$ 与控制收敛定理得到的连续性论证原封不动地成立，给出 $hat(QQ)_M$-a.s. 逐轨反演 $Z_t = integral_([0, t]) (hat(sigma)_(t - r) - sigma_0) L(dif r)$（$forall t in [0, T]$）。用检验函数 $phi(u) = (T - u)^2$ 分部积分得 $integral_0^T (T - u)^2 dif Z_u = 2 integral_0^T (T - u) Z_u dif u$。应用 Fubini 定理（由 $hat(sigma)$ 在 $[0, T]$ 上连续及 $L([0, T]) < infinity$ 保证逐轨成立）并作变量替换 $s = u - r$：
$
  2 integral_0^T (T - u) integral_([0, u]) (hat(sigma)_(u - r) - sigma_0) L(dif r) dif u &= integral_0^T (hat(sigma)_s - sigma_0) ( 2 integral_([0, T - s]) (T - s - r) L(dif r) ) dif s \
  &= integral_0^T W_2(s) (hat(sigma)_s - sigma_0) dif s.
$
分离出 $-cal(M)_T$，并与 Doléans--Dade 上鞅界 @eq:fatou 及二次变差控制 $(1\/2) lambda^2 chevron.l cal(M) chevron.r_T <= (lambda q \/ 2) integral_0^T (T - u)^2 hat(sigma)_u^2 dif u$（其中 $lambda = q \/ (theta.alt^2 T^2)$）结合，得到（$hat(QQ)_M$-a.s.）：
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda [ & sigma_0 I_0(T) + (c_0 T^3) / 3 + integral_0^T ( q / 2 (T - u)^2 hat(sigma)_u^2 \
    & + (A_M (T - u)^2 - W_2(u)) hat(sigma)_u ) dif u ].
$ <eq:general-exp-lower>
由 (i) 与 (iii)，取充分小的 $delta in (0, T)$ 使 $"Tail"(delta) <= (1\/2) sigma_0 I_0(T)$；再由 (ii) 及 $theta.alt >= beta > 0$，取充分大的 $M > 0$ 使 $A_M >= max{1, B(delta)}$。将区间分解为 $[0, T] = [0, T - delta] union [T - delta, T]$：
- 在 $[0, T - delta]$ 上，$A_M (T - u)^2 - W_2(u) >= (B(delta) - W_2(u) \/ (T - u)^2)(T - u)^2 >= 0$，故整个被积函数非负，可直接舍去。
- 在 $[T - delta, T]$ 上，舍去 $A_M (T - u)^2 hat(sigma)_u >= 0$ 并对 $x = hat(sigma)_u$ 逐点配方，得
  $
    q / 2 (T - u)^2 x^2 - W_2(u) x >= - (W_2(u)^2) / (2 q (T - u)^2),
  $
  其在 $[T - delta, T]$ 上的积分恰为 $-"Tail"(delta)$。

舍去 $(c_0 T^3) \/ 3 >= 0$（当 $sigma_0 = 0$ 且 $c_0 > 0$ 时则予以保留）并代入 @eq:general-exp-lower 即得
$
  -lambda cal(M)_T - 1/2 lambda^2 chevron.l cal(M) chevron.r_T >= lambda ( sigma_0 I_0(T) - "Tail"(delta) ) >= 1/2 lambda sigma_0 I_0(T) =: epsilon.alt_0 > 0, quad hat(QQ)_M"-a.s."
$
两边取指数并在 @eq:fatou 中取期望得 $1 < e^(epsilon.alt_0) <= 1$，矛盾。因此 $EE_QQ[S_T] < S_0$。 #h(1fr) $square$

回顾核函数 $K : (0, infinity) -> [0, infinity)$ 称为*完全单调（completely monotone）*，若其在 $(0, infinity)$ 上 $C^infinity$ 光滑且对所有 $t > 0$ 与 $k >= 0$ 满足 $(-1)^k K^((k))(t) >= 0$。由 #cite(<gripenberg1990volterra>, form: "prose", supplement: [Theorem 5.5.4]) 的经典定理，任意非零完全单调核 $K in L^1_"loc"(RR_+)$ 在任意 $[0, T]$ 上均存在唯一的非负第一类预解核 $L$ 且满足 $L([0, T]) < infinity$。因此定理 3 直接推得：

#thmblock("推论 4（全体非零完全单调 L² 核）")[
  设 $K in L^2_"loc"(RR_+)$ 为任意非零完全单调核，并设 @eq:model 存在连续全局非负解 $(S, sigma)$，满足 $sigma_0 > 0$、$theta > 0$、$kappa_1 >= 0$、$kappa_2 >= 0$、$epsilon.alt >= 0$ 及 $beta > kappa_2$。则对任意 $T > 0$ 均有 $EE_QQ[S_T] < S_0$。
]

== 金融波动率典型核族的显式验证

以下在粗糙及多因子随机波动率建模常用的三类典型核族上具体展示定理 3 与推论 4。

*例 1（Gamma / 指数阻尼幂律核）。* 考虑带指数截断的分数阶核
$
  K_(alpha, eta)(t) := t^(alpha - 1) e^(-eta t) / Gamma(alpha), quad alpha = H + 1/2 in (1/2, 1), quad eta > 0,
$ <eq:gamma-kernel>
它兼具短时粗糙奇性（$K_(alpha, eta)(0) = infinity$）与指数级长记忆衰减。其 Laplace 变换为 $hat(K)_(alpha, eta)(zeta) = (zeta + eta)^(-alpha)$，故第一类预解核的 Laplace 变换满足
$
  hat(L)_(alpha, eta)(zeta) = (zeta + eta)^alpha / zeta = (zeta + eta)^(alpha - 1) + eta (zeta + eta)^(alpha - 1) / zeta.
$
逐项反演可得显式的严格正预解测度密度：
$
  L_(alpha, eta)(dif r) = ell_(alpha, eta)(r) dif r, quad ell_(alpha, eta)(r) := r^(-alpha) e^(-eta r) / Gamma(1 - alpha) + eta integral_0^r u^(-alpha) e^(-eta u) / Gamma(1 - alpha) dif u.
$
在 @eq:W2-def 中交换积分次序，对 $v := T - s in [0, T]$ 得到精确权重表达式
$
  W_2(T - v) = 1 / Gamma(1 - alpha) integral_0^v [ 2(v - u) + eta (v - u)^2 ] u^(-alpha) e^(-eta u) dif u.
$ <eq:W2-gamma>
特别地，当 $v arrow.b 0$ 时有 $W_2(T - v) = (2 v^(2 - alpha)) \/ Gamma(3 - alpha) + O(v^(3 - alpha))$，从而端点尾项与未阻尼的 Riemann--Liouville 核具有完全相同的衰减阶 $O(M^(-(2 - 2 H) \/ (H + 1\/2)))$，而总质量 $I_0(T)$ 则随 $eta$ 严格递增（参见 @tbl:general-kernels）。

*例 2（有限与无限指数混合核；多尺度粗糙核）。* 由 Bernstein 定理，任意非零完全单调核均具有 Laplace 表示
$
  K_mu(t) = integral_([0, infinity)) e^(-x t) mu(dif x),
$
其中 $mu$ 为 $[0, infinity)$ 上的非零非负 Radon 测度。条件 $K_mu in L^2_"loc"(RR_+)$ 等价于 $integral_([0, infinity)) (1 + x)^(-1\/2) mu(dif x) < infinity$，在此条件下推论 4 直接适用：
- *有限指数和核（Markov 升维近似）*：取 $mu = sum_(i=1)^N w_i delta_(x_i)$（$w_i > 0, x_i >= 0$）即得 $K^N(t) = sum_(i=1)^N w_i e^(-x_i t)$。以单因子指数核 $K(t) = w e^(-x t)$ 为例，其第一类预解核具有显式公式 $L(dif r) = w^(-1) delta_0(dif r) + (x \/ w) dif r$，由此算得
  $
    W_2(s) = (2 (T - s) + x (T - s)^2) / w, quad I_0(T) = T^2 / w + (x T^3) / (3 w),
  $
  且对 $A_M > x\/w$，零点交叉位于 $delta_M = 2 \/ (w A_M - x)$，精确尾项界为
  $
    "Tail"(delta_M) = 1 / (2 q w^2) ( 4 delta_M + 2 x delta_M^2 + (x^2 delta_M^3) / 3 ).
  $
  对一般 $N >= 1$，推论 4 无需借助高维 Itô 扩散爆炸检验即可直接涵盖 #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4])。
- *无限混合与多尺度粗糙核*：只要 $mu([0, infinity)) = infinity$ 且 $integral_([0, infinity)) (1 + x)^(-1\/2) mu(dif x) < infinity$，核函数就满足 $K_mu(0) = infinity$ 且 $K_mu in L^2([0, T])$。这涵盖用于同时拟合短期限偏度与长期限期限结构的双尺度分数阶核 $K(t) = w_1 t^(alpha_1 - 1)\/Gamma(alpha_1) + w_2 t^(alpha_2 - 1)\/Gamma(alpha_2)$（$1\/2 < alpha_1 < alpha_2 <= 1, w_1, w_2 > 0$）。即使此时 $L$ 不存在初等闭式表达式，推论 4 仍可无条件给出 $EE_QQ[S_T] < S_0$。

*例 3（平移幂律核）。* 正则化幂律核
$
  K_(alpha, epsilon)(t) := (t + epsilon)^(alpha - 1) = 1 / Gamma(1 - alpha) integral_0^infinity x^(-alpha) e^(-epsilon x) e^(-x t) dif x, quad alpha in (1/2, 1), quad epsilon > 0,
$
光滑且完全单调（$K_(alpha, epsilon)(0) = epsilon^(alpha - 1) < infinity$），常被用作粗糙波动率的光滑替代核。推论 4 适用于任意 $epsilon > 0$，并在同一证明框架下自然衔接奇异极限 $epsilon arrow.b 0$（定理 1）。

= 与现有方法的对比及数值算例

== 与微分及 Markov 型判据的适用范围对比

为明确本文定理 1 与定理 3 在近期 Volterra 鞅性文献中的位置，@tbl:comparison 将本文的检验函数法与 #cite(<sepp2023lognormal>, form: "prose") 的经典扩散检验、#cite(<bondi2026feller>, form: "prose") 的 Feller/Khasminskii 爆炸判据、#cite(<guyon2026martingale>, form: "prose") 的 Volterra 鞅性框架，以及 #cite(<sepp2026rough>, form: "prose", supplement: [Proposition 4.4]) 的有限指数和逆命题作了系统对比。

#figure(
  table(
    align: (left, left, left, left),
    columns: (auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*方法 / 文献*], [*必要性判据适用核类*], [*核心证明机制*], [*正则性与结构性前提*],
    [Sepp & Rakhmonov #cite(<sepp2023lognormal>)], [常核（$H = 1\/2$）], [一维 Feller 爆炸检验], [Markov 扩散过程；Itô 生成元],
    [Bondi & Pulido #cite(<bondi2026feller>)], [非奇异核（$K(0) < infinity$，$K in W^(1,1)$）及有限和核 $K^N$], [半鞅 Feller / Khasminskii 检验], [半鞅状态或 $N$ 维 Markov 升维],
    [Guyon et al. #cite(<guyon2026martingale>)], [光滑核（充分性条件允许粗糙核）], [光滑 Volterra SDE 爆炸判据], [光滑核 $K$；增长假设 1.2 在 $kappa_2 > 0$ 时不满足],
    [Sepp & Rakhmonov #cite(<sepp2026rough>, supplement: [Prop. 4.4])], [正权重有限指数和核 $K^N$], [借助 #cite(<bondi2026feller>) 作微分归约], [$K^N(0) < infinity$],
    [*本文（定理 3 / 推论 4）*], [*全体非零完全单调 $K in L^2$（兼顾 $K(0) < infinity$ 与 $K(0) = infinity$）*], [*第一类预解核 + 二次检验函数 + Cameron--Martin 倾斜 + Doléans--Dade 上鞅*], [*仅需 $sigma_t >= 0$ a.s. 与有限非负 $L >= 0$；无需半鞅、严格正性或 $L log L$*],
  ),
  caption: [对数正态 Volterra 随机波动率模型鞅性必要条件（严格局部鞅）判据的对比。]
) <tbl:comparison>

*方法边界。* 尽管定理 3 跨越了 $K(0) < infinity$ 的障碍并统一了光滑与奇异完全单调核，该方法仍具有两条清晰的结构边界：
1. *第一类预解核的符号*：一致界 @eq:W2-uniform 以及主区间 $[0, T - delta]$ 上被积函数的非负性均依赖 $L >= 0$（对全体完全单调核恒成立）与 $hat(sigma)_u >= 0$。对于第一类预解核变号的振荡或非完全单调核，$W_2(s)$ 可能取负值，此时逐点比较方向不再成立。
2. *漂移与扩散的增长阶平衡*：将 $(1\/2) lambda^2 chevron.l cal(M) chevron.r_T$ 吸收进 $(q\/2) integral_0^T (T - u)^2 hat(sigma)_u^2 dif u$，关键在于份额测度下的二次漂移 $+q hat(sigma)^2$ 与二次变差阶数 $theta.alt^2 hat(sigma)^2$ 相匹配。若波动率扩散项随 $sigma$ 的增长严格快于倾斜后漂移项的平方根，则需引入其他类型的检验函数或局部化估计。

== 数值算例

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

为进一步展示定理 3 在纯 Riemann--Liouville 核之外的表现，@tbl:general-kernels 在相同基准参数（$T = 0.01$ 年、$sigma_0 = 0.5$、$c_1 = -2.0$、$q = 0.6$、$theta.alt = 1.0$）下，分别计算了 $H = 0.25$ 的 Gamma 核 @eq:gamma-kernel（由 @eq:W2-gamma 算得）以及单因子指数核 $K(t) = e^(-x t)$（例 2）的主导项 $"LHS" = sigma_0 I_0(T)$、零点边界层厚度 $delta_M$ 与端点尾项界。

#figure(
  table(
    align: (left, center, right, right, right, right, right),
    columns: (auto, auto, auto, auto, auto, auto, auto),
    stroke: 0.5pt,
    inset: 5pt,
    [*核函数族*], [*阻尼参数*], [*$M$*], [*$delta_M$*], [*LHS*], [*尾项界*], [*净余量*],
    [Gamma 核 ($H = 0.25$)], [$eta = 0$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.24 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.30 times 10^(-6)$],
    [Gamma 核 ($H = 0.25$)], [$eta = 5$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.25 times 10^(-5)$], [$3.11 times 10^(-6)$], [$+9.44 times 10^(-6)$],
    [Gamma 核 ($H = 0.25$)], [$eta = 20$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.30 times 10^(-5)$], [$3.12 times 10^(-6)$], [$+9.86 times 10^(-6)$],
    [Gamma 核 ($H = 0.25$)], [$eta = 50$], [$1.32 times 10^3$], [$1.48 times 10^(-4)$], [$1.38 times 10^(-5)$], [$3.13 times 10^(-6)$], [$+1.07 times 10^(-5)$],
    [指数核 $e^(-x t)$], [$x = 0$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.00 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.50 times 10^(-5)$],
    [指数核 $e^(-x t)$], [$x = 5$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.08 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.59 times 10^(-5)$],
    [指数核 $e^(-x t)$], [$x = 20$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.33 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+2.84 times 10^(-5)$],
    [指数核 $e^(-x t)$], [$x = 50$], [$2.67 times 10^5$], [$7.49 times 10^(-6)$], [$5.83 times 10^(-5)$], [$2.50 times 10^(-5)$], [$+3.34 times 10^(-5)$],
  ),
  caption: [定理 3 在 $T = 0.01$ 年（$sigma_0 = 0.5$，$c_1 = -2.0$，$q = 0.6$，$theta.alt = 1.0$）下对 Gamma 核 $K_(0.75, eta)$ 与单因子指数核 $e^(-x t)$ 的显式参数。增大指数衰减会显著扩大主导正项 $"LHS"$，而对窄端点尾项界影响极微。]
) <tbl:general-kernels>

由 @tbl:general-kernels 可见，引入指数阻尼（$eta > 0$ 或 $x > 0$）会为第一类预解核 $L$ 带来一个非负的积分增量项，从而严格增大全局质量 $I_0(T)$（即增大 $"LHS"$），同时对窄边界层 $[T - delta_M, T]$ 仅产生 $O(eta delta_M)$ 阶的高阶影响，进而严格拓宽矛盾净余量。

*遗留公开问题。* 本文在分数阶核及全体非零完全单调 $L^2$ 核下证明了猜想 4.5（鞅性必要条件），但并未涉及 $H < 1\/2$ 时 $sigma_t$ 的几乎必然严格正性（#cite(<sepp2026rough>, form: "prose", supplement: [Conjecture 2.3])）以及二次漂移下的平稳分布问题，这两者目前仍处于开放状态。

*致谢与人工智能工具使用说明。* 作者感谢 Google 开发的大语言模型 Gemini 4 Neon #cite(<google2026gemini>) 在证明梳理、Typst 排版及 Lean 4 形式化过程中提供的辅助支持。

#bibliography("bibliography.bib", title: "参考文献")

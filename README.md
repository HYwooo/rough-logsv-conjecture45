# Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic Volatility with Quadratic Drift

**Author:** Huayang WU  *(with drafting and formalization assistance acknowledged for Google Gemini 4 Neon)*  
**Paper PDF:** [`paper/RoughLogSV_Conjecture45.pdf`](paper/RoughLogSV_Conjecture45.pdf) ([中文版 PDF](paper/RoughLogSV_Conjecture45_zh.pdf))  
**Typst Source:** [`paper/rough_logsv_conjecture_4_5.typ`](paper/rough_logsv_conjecture_4_5.typ) & [`paper/bibliography.bib`](paper/bibliography.bib)  
**Lean 4 + Mathlib4 Verification:** [`RoughLogSVConjecture45.lean`](RoughLogSVConjecture45.lean) (Lean `v4.36.0`, Mathlib `v4.36.0`, zero `sorry`)

## Overview

This repository contains the manuscript and Lean 4 formalization settling **Conjecture 4.5** of Sepp and Rakhmonov (2026, `arXiv:2611.32791`), unified with the classical diffusion endpoint $H = 1/2$ (Sepp and Rakhmonov, 2023, Theorem 3.7), and further extending the necessity argument to **general completely monotone Volterra kernels** $K \in L^2([0, T])$ via Gripenberg–Londen–Staffans (1990) first-kind resolvent measures.

Under the pricing measure $\mathbb{Q}$ with fractional Riemann–Liouville kernel $K(t) = t^{H - 1/2}/\Gamma(H + 1/2)$ ($H \in (0, 1/2]$), or more generally a non-trivial completely monotone kernel $K \in L^2_{\mathrm{loc}}([0, \infty))$, the forward price $S_t$ and instantaneous volatility $\sigma_t$ satisfy:
$$\frac{\mathrm{d}S_t}{S_t} = \sigma_t\,\mathrm{d}W_t^{(0)}, \qquad \sigma_t = \sigma_0 + \int_0^t K(t-s)\Big[(\kappa_1 + \kappa_2 \sigma_s)(\theta - \sigma_s)\,\mathrm{d}s + \beta \sigma_s\,\mathrm{d}W_s^{(0)} + \epsilon \sigma_s\,\mathrm{d}W_s^{(1)}\Big].$$

- **Theorem 1 (Unified Martingale Necessity, Fractional Case):** For any $H \in (0, 1/2]$, $\sigma_0 > 0$, $\theta > 0$, $\kappa_1 \ge 0$, $\kappa_2 \ge 0$, $\epsilon \ge 0$, and $\beta \in \mathbb{R}$ (so $c_0 = \kappa_1 \theta \ge 0$), if $\beta > \kappa_2$ then $\mathbb{E}_{\mathbb{Q}}[S_T] < S_0$ for every $T > 0$ (no strict positivity or $L\log L$ assumption required; and as noted in Remark 1, if $c_0 < 0$ one may shrink $t \in (0, T]$ so $2\sigma_0 t^{3-\alpha}/\Gamma(4-\alpha) + c_0 t^3/3 > 0$).
- **Corollary 2 (Exact Martingality Boundary, Fractional Case):** Combined with Theorem 4.3 of Sepp and Rakhmonov (2026), $S$ is a true $\mathbb{Q}$-martingale on $[0, T]$ if and only if $\kappa_2 \ge \beta$.
- **Theorem 3 (Extension to General Completely Monotone Kernels):** For any completely monotone $K \in L^2([0, T])$ that is not identically zero (hence admitting a unique non-negative Radon first-kind resolvent measure $L$ with $L([0, T]) < \infty$ by Gripenberg–Londen–Staffans 1990, Theorem 5.5.4) and $c_0 \ge 0$, $\beta > \kappa_2$ still forces $\mathbb{E}_{\mathbb{Q}}[S_T] < S_0$ for every $T > 0$ — with explicit resolvent weight $W_2(s) = 2\int_0^{T-s}(T-s-r)\,L(\mathrm{d}r)$, $I_0(T) = \int_0^T W_2(s)\,\mathrm{d}s \ge (T^2/8)L([0, T/2]) > 0$, $B(\delta) = 2L([0, T])/\delta$, and $\mathrm{Tail}(\delta) \le (2L([0, T])^2 / q)\delta$.
- **Corollary 4 & Examples 1–3:** Covers any completely monotone kernel satisfying Theorem 4.3 of Sepp and Rakhmonov (2026), and specializes closed-form $L$ and $(W_2, I_0, L([0, T]))$ for **tempered power-law (Gamma)** kernels $K_\eta(t) = e^{-\eta t} t^{H-1/2}/\Gamma(H+1/2)$, **exponential** kernels $K(t) = e^{-\varkappa t}$, and **finite multi-factor Markovian sums** $\sum_i w_i e^{-\varkappa_i t}$.

## Proof Structure

1. **Share-measure reduction:** Assuming $\mathbb{E}_{\mathbb{Q}}[S_T] = S_0$ defines $\hat{\mathbb{Q}} \sim \mathbb{Q}$ via $\mathrm{d}\hat{\mathbb{Q}}/\mathrm{d}\mathbb{Q}|_{\mathcal{F}_T} = S_T/S_0$, flipping the quadratic drift to $+q \hat{\sigma}_s^2$ with $q := \beta - \kappa_2 > 0$.
2. **Constant-drift Cameron–Martin tilt:** Tilting by $\exp(M \hat{B}_T - \frac{1}{2}M^2 T)$ shifts the linear drift $c_1 \mapsto A_M := c_1 + \vartheta M \to +\infty$ on $[0, T]$.
3. **First-kind resolvent & quadratic test function:** Convolving with the non-negative first-kind resolvent $L$ and applying localized stochastic Fubini (Abi Jaber–Larsson–Pulido 2019, Lemma 2.6, on $\{\tau_n = T\}$) gives $Z_t = (L * (\hat{\sigma} - \sigma_0))_t$; testing $\mathrm{d}Z_u$ against $\varphi(u) = (T - u)^2$ yields a unified identity for all $H \in (0, 1/2]$.
4. **Doléans–Dade supermartingale & boundary-layer splitting:** Choosing $\lambda = q/(\vartheta^2 T^2)$ absorbs $\frac{1}{2}\lambda^2\langle\mathcal{M}\rangle_T$ into half of the positive quadratic drift, while splitting $[0, T] = [0, T-\delta_M] \cup [T-\delta_M, T]$ yields a strictly positive deterministic pathwise lower bound contradicting Fatou's lemma $\mathbb{E}_{\hat{\mathbb{Q}}_M}[\mathcal{E}_T(-\lambda \mathcal{M})] \le 1$.

## Quantitative Benchmarks (Tables 2 & 3 in Paper)

Parameters: $T = 0.01$, $\sigma_0 = 0.5$, $c_1 = -2.0$, $q = 0.6$, $\vartheta = 1.0$. (See Table 1 in the paper for a scope comparison between Sepp–Rakhmonov 2023/2026, Theorem 1, and Theorem 3.)

**Table 2 (Riemann–Liouville fractional kernel):**

| $H$ | $M$ | $\delta_M$ | $\text{LHS}$ | Tail bound | Margin ($\text{LHS} - \text{Tail}$) |
| :---: | :---: | :---: | :---: | :---: | :---: |
| 0.10 | $2.00 \times 10^2$ | $3.29 \times 10^{-4}$ | $5.32 \times 10^{-6}$ | $6.45 \times 10^{-7}$ | $+4.67 \times 10^{-6}$ |
| 0.25 | $1.32 \times 10^3$ | $1.48 \times 10^{-4}$ | $1.24 \times 10^{-5}$ | $3.11 \times 10^{-6}$ | $+9.30 \times 10^{-6}$ |
| 0.40 | $1.96 \times 10^4$ | $3.50 \times 10^{-5}$ | $2.87 \times 10^{-5}$ | $1.14 \times 10^{-5}$ | $+1.73 \times 10^{-5}$ |
| 0.50 | $2.67 \times 10^5$ | $7.49 \times 10^{-6}$ | $5.00 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+2.50 \times 10^{-5}$ |

**Table 3 (General completely monotone kernels — tempered Gamma at $H=0.25$ and exponential):**

| Kernel | $L([0,T])$ | $\delta_M$ | $\text{LHS}$ | Tail bound | Margin |
| :--- | :---: | :---: | :---: | :---: | :---: |
| Gamma ($\eta = 0$) | $0.0620$ | $1.48 \times 10^{-4}$ | $1.24 \times 10^{-5}$ | $3.11 \times 10^{-6}$ | $+9.30 \times 10^{-6}$ |
| Gamma ($\eta = 5$) | $0.0630$ | $1.48 \times 10^{-4}$ | $1.25 \times 10^{-5}$ | $3.11 \times 10^{-6}$ | $+9.43 \times 10^{-6}$ |
| Gamma ($\eta = 20$) | $0.0660$ | $1.48 \times 10^{-4}$ | $1.30 \times 10^{-5}$ | $3.12 \times 10^{-6}$ | $+9.85 \times 10^{-6}$ |
| Gamma ($\eta = 50$) | $0.0721$ | $1.48 \times 10^{-4}$ | $1.38 \times 10^{-5}$ | $3.13 \times 10^{-6}$ | $+1.07 \times 10^{-5}$ |
| Exp ($\varkappa = 0$) | $1.0000$ | $7.49 \times 10^{-6}$ | $5.00 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+2.50 \times 10^{-5}$ |
| Exp ($\varkappa = 5$) | $1.0500$ | $7.49 \times 10^{-6}$ | $5.08 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+2.58 \times 10^{-5}$ |
| Exp ($\varkappa = 20$) | $1.2000$ | $7.49 \times 10^{-6}$ | $5.33 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+2.84 \times 10^{-5}$ |
| Exp ($\varkappa = 50$) | $1.5000$ | $7.49 \times 10^{-6}$ | $5.83 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+3.34 \times 10^{-5}$ |

## Lean 4 Verification

The formalization [`RoughLogSVConjecture45.lean`](RoughLogSVConjecture45.lean) is built against Lean `v4.36.0` + Mathlib `v4.36.0` with a transparent 3-layer separation (zero `sorry`, and `#print axioms` confirms both `conjecture_4_5` and `general_kernel_theorem_3` depend solely on `[propext, Classical.choice, Quot.sound]`):

- **Sections 1–3 (`conjecture_4_5`, Fractional & Classical $H \in (0, 1/2]$):**
  - *Layer 1 (Pure Real Analysis & Integral Estimates):* `resolvent_test_weight_eq`, `constant_test_weight_integral_eq`, `quadratic_variation_domination`, `main_interval_integrand_nonneg`, `endpoint_layer_pointwise_lower_bound`, `boundary_layer_integral_eq`, `split_integral_lower_bound`, `classical_endpoint_specialization`, and `exists_large_M_contradiction_margin`.
  - *Layer 2 (`VolterraMartingaleInterface`):* Isolates Girsanov tilts, localized Volterra resolvent inversion, Itô integration by parts + stochastic Fubini, and Fatou's lemma for the Doléans–Dade exponential.
  - *Layer 3 (`conjecture_4_5`):* Combines Layer 1 and Layer 2 to derive `I.E_S_T < I.S₀`.
- **Section 4 (`Theorem3GeneralKernels`, General Completely Monotone Kernels):**
  - *Layer 1 (`GeneralKernelParams`):* Models an abstract finite non-negative Radon resolvent measure `L` on `[0, T]` with `∫_[0,t] K(t-r) dL(r) > 0` for some `t ∈ (0, T/2)`, and unconditionally proves `W₂_continuousOn`, `W₂_le`, `W₂_lower_half`, `I₀_pos`, `B_bound_valid`, `integrable_tail`, `tail_le`, `exists_general_M_contradiction_margin`, `general_split_integral_lower_bound`, and `quadratic_variation_domination_general`.
  - *Layer 2 (`GeneralVolterraMartingaleInterface`):* Isolates stochastic calculus inputs for the general kernel (`resolvent_measure_quadratic_identity`).
  - *Layer 3 (`general_kernel_theorem_3`):* Combines Layer 1 and Layer 2 to derive `I.E_S_T < I.S₀`.

### Building Locally

```bash
lake exe cache get   # if fetching Mathlib cache for the first time
lake build
```

## Repository Structure

```text
.
├── .gitignore
├── README.md
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── RoughLogSVConjecture45.lean
└── paper/
    ├── RoughLogSV_Conjecture45.pdf
    ├── RoughLogSV_Conjecture45_zh.pdf
    ├── bibliography.bib
    ├── figures.typ
    ├── rough_logsv_conjecture_4_5.typ
    └── rough_logsv_conjecture_4_5_zh.typ
```

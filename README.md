# Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic Volatility with Quadratic Drift

**Author:** Huayang WU (`huayang.bryan.wu[at]outlook.com`)  
**Paper:** [`paper/RoughLogSV_Conjecture45.pdf`](paper/RoughLogSV_Conjecture45.pdf)  
**Lean 4 Core Verification:** [`RoughLogSVConjecture45.lean`](RoughLogSVConjecture45.lean) (Lean `v4.36.0`, zero external imports, zero `sorry`)

## Overview

This repository contains the manuscript and Lean 4 core formalization settling **Conjecture 4.5** of Sepp and Rakhmonov (2026, `arXiv:2611.32791v1`), unified with the classical diffusion endpoint $H = 1/2$ (Sepp and Rakhmonov, 2023, Theorem 3.7).

Under the pricing measure $\mathbb{Q}$ with Riemann–Liouville fractional kernel $K(t) = t^{H - 1/2}/\Gamma(H + 1/2)$ ($H \in (0, 1/2]$), the forward price $S_t$ and instantaneous volatility $\sigma_t$ satisfy:
$$\frac{\mathrm{d}S_t}{S_t} = \sigma_t\,\mathrm{d}W_t^{(0)}, \qquad \sigma_t = \sigma_0 + \int_0^t K(t-s)\Big[(\kappa_1 + \kappa_2 \sigma_s)(\theta - \sigma_s)\,\mathrm{d}s + \beta \sigma_s\,\mathrm{d}W_s^{(0)} + \epsilon \sigma_s\,\mathrm{d}W_s^{(1)}\Big].$$

- **Theorem 1 (Unified Martingale Necessity):** Whenever $\beta > \kappa_2$ and $H \in (0, 1/2]$, $\mathbb{E}_{\mathbb{Q}}[S_T] < S_0$ for every $T > 0$ (no strict positivity or $L\log L$ assumption required).
- **Corollary 2 (Exact Martingality Boundary):** Combined with Theorem 4.3 of Sepp and Rakhmonov (2026), $S$ is a true $\mathbb{Q}$-martingale on $[0, T]$ if and only if $\kappa_2 \ge \beta$.

## Proof Structure

1. **Share-measure reduction:** Assuming $\mathbb{E}_{\mathbb{Q}}[S_T] = S_0$ defines $\hat{\mathbb{Q}} \sim \mathbb{Q}$ via $\mathrm{d}\hat{\mathbb{Q}}/\mathrm{d}\mathbb{Q}|_{\mathcal{F}_T} = S_T/S_0$, flipping the quadratic drift to $+q \hat{\sigma}_s^2$ with $q := \beta - \kappa_2 > 0$.
2. **Constant-drift Cameron–Martin tilt:** Tilting by $\exp(M \hat{B}_T - \frac{1}{2}M^2 T)$ shifts the linear drift $c_1 \mapsto A_M := c_1 + \vartheta M \to +\infty$ on $[0, T]$.
3. **First-kind resolvent & quadratic Fujita–Kaplan test function:** Convolving with the non-negative first-kind resolvent $L$ gives $Z_t = (L * (\hat{\sigma} - \sigma_0))_t$ even when $K(0) = \infty$; testing $\mathrm{d}Z_u$ against $\varphi(u) = (T - u)^2$ yields a unified identity for all $H \in (0, 1/2]$.
4. **Doléans–Dade supermartingale & boundary-layer splitting:** Choosing $\lambda = q/(\vartheta^2 T^2)$ absorbs $\frac{1}{2}\lambda^2\langle\mathcal{M}\rangle_T$ into half of the positive quadratic drift, while splitting $[0, T] = [0, T-\delta_M] \cup [T-\delta_M, T]$ yields a strictly positive deterministic pathwise lower bound contradicting Fatou's lemma $\mathbb{E}_{\hat{\mathbb{Q}}_M}[\mathcal{E}_T(-\lambda \mathcal{M})] \le 1$.

## Quantitative Benchmark (Table 1 in Paper)

Parameters: $T = 0.01$, $\sigma_0 = 0.5$, $c_1 = -2.0$, $q = 0.6$, $\vartheta = 1.0$.

| $H$ | $M$ | $\delta_M$ | $\text{LHS}$ | Tail bound | Margin ($\text{LHS} - \text{Tail}$) |
| :---: | :---: | :---: | :---: | :---: | :---: |
| 0.10 | $2.00 \times 10^2$ | $3.29 \times 10^{-4}$ | $5.32 \times 10^{-6}$ | $6.45 \times 10^{-7}$ | $+4.67 \times 10^{-6}$ |
| 0.25 | $1.32 \times 10^3$ | $1.47 \times 10^{-4}$ | $1.24 \times 10^{-5}$ | $3.09 \times 10^{-6}$ | $+9.31 \times 10^{-6}$ |
| 0.40 | $1.96 \times 10^4$ | $3.50 \times 10^{-5}$ | $2.87 \times 10^{-5}$ | $1.14 \times 10^{-5}$ | $+1.73 \times 10^{-5}$ |
| 0.50 | $2.67 \times 10^5$ | $7.50 \times 10^{-6}$ | $5.00 \times 10^{-5}$ | $2.50 \times 10^{-5}$ | $+2.50 \times 10^{-5}$ |

## Lean 4 Verification

The file [`RoughLogSVConjecture45.lean`](RoughLogSVConjecture45.lean) targets Lean `v4.36.0` with zero external dependencies and verifies the core deterministic/algebraic inequalities and rational witnesses:

- `sq_le_sq` & `qv_absorption`: $\lambda^2 \vartheta^2 r^4 \le \lambda q r^2$ for $0 \le r \le T$ and $\lambda(\vartheta^2 T^2) = q$.
- `endpoint_layer_margin_pos`: strict positivity of $\varepsilon_0 = \lambda(\text{lhs} - \text{tail})$ when $\text{tail} < \text{lhs}$.
- `supermartingale_contradiction`: contradiction from $1 < \exp(\varepsilon_0) \le \mathbb{E}[\mathcal{E}_T(-\lambda\mathcal{M})] \le 1$.
- `sq_nonneg_int`: pointwise non-negativity $0 \le y^2$ over `Int` (updated for Lean 4.36.0 using `Int.natCast_nonneg`).
- `h_half_concrete_witness` & `h_half_delta_le_T`: exact rational checks at $H = 1/2$, $T = 1/100$, $\sigma_0 = 1/2$, $q = 3/5$, $A_M = 267000$.

*(Scope note: stochastic-calculus ingredients—Girsanov tilts, first-kind resolvent inversion, Itô integration by parts, and Fatou's lemma—are proved analytically in the paper and passed as hypotheses to the Lean theorems.)*

### Running Locally

```bash
lake build
# or directly:
lean RoughLogSVConjecture45.lean
```

## Repository Structure

```text
.
├── .gitignore
├── README.md
├── lakefile.toml
├── lean-toolchain
├── RoughLogSVConjecture45.lean
└── paper/
    └── RoughLogSV_Conjecture45.pdf
```

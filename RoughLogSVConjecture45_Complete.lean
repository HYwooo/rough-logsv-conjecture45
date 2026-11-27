/-
  RoughLogSVConjecture45_Complete.lean
  ==============================================================================
  Structured Lean 4 + Mathlib4 formalization of the proof of Conjecture 4.5 of
  Sepp & Rakhmonov (2026), arXiv:2611.32791v1, following Huayang Wu (2026):
  "Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic
   Volatility with Quadratic Drift".

  Architecture (3-layer separation for full auditability):
  ------------------------------------------------------------------------------
  * Layer 1 (Pure Real Analysis & Integral Estimates — ZERO axioms, ZERO sorry):
      Formalizes over `ℝ` (with `Real.Gamma`, `Real.rpow`, `intervalIntegral`)
      every analytical and quantitative step of Sections 3.2–3.4 of the paper:
      - Exact quadratic-variation bound (Eq. 16)
      - Main-interval non-negativity on `[0, T - δ_M]` (Eq. 19)
      - Pointwise completing-the-square lower bound on `[T - δ_M, T]` (Eq. 20)
      - Exact boundary-layer integral evaluation (Eq. 21)
      - Classical diffusion specialization `H = 1/2` (Eq. 23)
      - Explicit constructive existence of `M > 0` yielding `ε₀ > 0` and
        `1 < exp ε₀` (Eq. 22 & Eq. 24).
  * Layer 2 (Stochastic Calculus Interface — Explicit minimal assumptions):
      Since Mathlib4 does not yet contain full continuous-time stochastic
      calculus (Girsanov's theorem for Volterra SDEs, stochastic Fubini for
      singular kernels / Abi Jaber–Larsson–Pulido 2019 Lemma 2.6, and
      Doléans–Dade exponential supermartingales), these three exact stochastic
      inputs from Steps 3.1–3.3 are isolated as fields of the structure
      `VolterraMartingaleInterface`.
  * Layer 3 (End-to-End Main Theorem `conjecture_4_5`):
      Combines Layer 1 and Layer 2 with zero `sorry` to derive `E_Q[S_T] < S_0`
      for all `T > 0`, `H ∈ (0, 1/2]`, `σ₀ > 0`, `κ₁ ≥ 0`, `κ₂ ≥ 0`, `θ ≥ 0`, `β > κ₂`.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

open Real MeasureTheory Set Filter

noncomputable section

namespace RoughLogSVConjecture45

/-! ## 0. Model Parameters and Derived Constants -/

/-- Admissible parameter bundle matching Sepp & Rakhmonov (2026) Conjecture 4.5. -/
structure ModelParams where
  H : ℝ
  σ₀ : ℝ
  κ₁ : ℝ
  κ₂ : ℝ
  θ : ℝ
  β : ℝ
  ε : ℝ
  T : ℝ
  hH_pos : 0 < H
  hH_le : H ≤ 1 / 2
  hσ₀_pos : 0 < σ₀
  hκ₁_nonneg : 0 ≤ κ₁
  hκ₂_nonneg : 0 ≤ κ₂
  hθ_nonneg : 0 ≤ θ
  hβ_gt_κ₂ : κ₂ < β
  hT_pos : 0 < T

namespace ModelParams

def α (p : ModelParams) : ℝ := p.H + 1 / 2
def q (p : ModelParams) : ℝ := p.β - p.κ₂
def ϑ (p : ModelParams) : ℝ := Real.sqrt (p.β ^ 2 + p.ε ^ 2)
def c₀ (p : ModelParams) : ℝ := p.κ₁ * p.θ
def c₁ (p : ModelParams) : ℝ := p.κ₂ * p.θ - p.κ₁
def lam (p : ModelParams) : ℝ := p.q / (p.ϑ ^ 2 * p.T ^ 2)

lemma α_gt_half (p : ModelParams) : 1 / 2 < p.α := by
  unfold α; linarith [p.hH_pos]

lemma α_le_one (p : ModelParams) : p.α ≤ 1 := by
  unfold α; linarith [p.hH_le]

lemma α_pos (p : ModelParams) : 0 < p.α := by
  linarith [p.α_gt_half]

lemma q_pos (p : ModelParams) : 0 < p.q := by
  unfold q; linarith [p.hβ_gt_κ₂]

lemma β_pos (p : ModelParams) : 0 < p.β := by
  linarith [p.hκ₂_nonneg, p.hβ_gt_κ₂]

lemma ϑ_pos (p : ModelParams) : 0 < p.ϑ := by
  unfold ϑ
  apply Real.sqrt_pos.mpr
  have hβ : 0 < p.β ^ 2 := sq_pos_of_pos p.β_pos
  have hε : 0 ≤ p.ε ^ 2 := sq_nonneg p.ε
  linarith

lemma c₀_nonneg (p : ModelParams) : 0 ≤ p.c₀ :=
  mul_nonneg p.hκ₁_nonneg p.hθ_nonneg

lemma lam_pos (p : ModelParams) : 0 < p.lam := by
  unfold lam
  exact div_pos p.q_pos (mul_pos (sq_pos_of_pos p.ϑ_pos) (sq_pos_of_pos p.hT_pos))

lemma three_sub_α_pos (p : ModelParams) : 0 < 3 - p.α := by
  linarith [p.α_le_one]

lemma four_sub_α_pos (p : ModelParams) : 0 < 4 - p.α := by
  linarith [p.α_le_one]

lemma one_sub_H_pos (p : ModelParams) : 0 < 1 - p.H := by
  linarith [p.hH_le]

lemma two_sub_twoH_ge_one (p : ModelParams) : 1 ≤ 2 - 2 * p.H := by
  linarith [p.hH_le]

lemma one_sub_twoH_nonneg (p : ModelParams) : 0 ≤ 1 - 2 * p.H := by
  linarith [p.hH_le]

lemma three_sub_α_eq (p : ModelParams) : 3 - p.α = 5 / 2 - p.H := by
  unfold α; ring

lemma four_sub_α_eq (p : ModelParams) : 4 - p.α = 7 / 2 - p.H := by
  unfold α; ring

lemma Gamma_three_sub_α_pos (p : ModelParams) : 0 < Real.Gamma (3 - p.α) :=
  Real.Gamma_pos_of_pos p.three_sub_α_pos

lemma Gamma_four_sub_α_pos (p : ModelParams) : 0 < Real.Gamma (4 - p.α) :=
  Real.Gamma_pos_of_pos p.four_sub_α_pos

/-- Tilted linear drift coefficient `A_M = c₁ + ϑ M`. -/
def A_M (p : ModelParams) (M : ℝ) : ℝ := p.c₁ + p.ϑ * M

/-- Boundary-layer thickness `δ_M = (2 / (A_M Γ(3 - α)))^(1 / α)` (Eq. 18). -/
def δ_M (p : ModelParams) (M : ℝ) : ℝ :=
  (2 / (p.A_M M * Real.Gamma (3 - p.α))) ^ (1 / p.α)

/-- Deterministic leading term `2 σ₀ T^(3 - α) / Γ(4 - α)` (Eq. 22 LHS). -/
def leadingTerm (p : ModelParams) : ℝ :=
  2 * p.σ₀ * p.T ^ (3 - p.α) / Real.Gamma (4 - p.α)

/-- Deterministic boundary-layer tail bound `δ_M^(2 - 2H) / (q (1 - H) Γ(3 - α)^2)` (Eq. 21/22). -/
def tailTerm (p : ModelParams) (M : ℝ) : ℝ :=
  (p.δ_M M) ^ (2 - 2 * p.H) / (p.q * (1 - p.H) * (Real.Gamma (3 - p.α)) ^ 2)

lemma leadingTerm_pos (p : ModelParams) : 0 < p.leadingTerm := by
  unfold leadingTerm
  exact div_pos
    (mul_pos (mul_pos (by norm_num) p.hσ₀_pos) (Real.rpow_pos_of_pos p.hT_pos _))
    p.Gamma_four_sub_α_pos

lemma δ_M_pos (p : ModelParams) {M : ℝ} (hA : 0 < p.A_M M) : 0 < p.δ_M M := by
  unfold δ_M
  apply Real.rpow_pos_of_pos
  exact div_pos (by norm_num) (mul_pos hA p.Gamma_three_sub_α_pos)

lemma δ_M_rpow_α (p : ModelParams) {M : ℝ} (hA : 0 < p.A_M M) :
    (p.δ_M M) ^ p.α = 2 / (p.A_M M * Real.Gamma (3 - p.α)) := by
  unfold δ_M
  have hbase : 0 ≤ 2 / (p.A_M M * Real.Gamma (3 - p.α)) :=
    le_of_lt (div_pos (by norm_num) (mul_pos hA p.Gamma_three_sub_α_pos))
  rw [← Real.rpow_mul hbase, one_div_mul_cancel (ne_of_gt p.α_pos), Real.rpow_one]

end ModelParams

/-! ## Layer 1: Pure Real Analysis & Quantitative Core (Eqs. 16, 18–24) -/

section Layer1Analysis

/-- **Eq. (16) Pointwise Kernel Bound**:
    For `u ∈ [0, T]`, `(T - u)^4 ≤ T^2 (T - u)^2`. -/
lemma quartic_le_sq_mul_sq {T u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) :
    (T - u) ^ 4 ≤ T ^ 2 * (T - u) ^ 2 := by
  have hTu_nonneg : 0 ≤ T - u := sub_nonneg.mpr huT
  have hTu_le : T - u ≤ T := by linarith
  have hsq : (T - u) ^ 2 ≤ T ^ 2 := by nlinarith
  have hsq_nonneg : 0 ≤ (T - u) ^ 2 := sq_nonneg (T - u)
  calc
    (T - u) ^ 4 = (T - u) ^ 2 * (T - u) ^ 2 := by ring
    _ ≤ T ^ 2 * (T - u) ^ 2 := mul_le_mul_of_nonneg_right hsq hsq_nonneg

/-- **Eq. (16) Integral Bound**:
    With `λ = q / (ϑ^2 T^2)`, for any continuous non-negative path `σ` on `[0, T]`,
    `(1/2) λ^2 ϑ^2 ∫_0^T (T-u)^4 σ(u)^2 du ≤ (λ q / 2) ∫_0^T (T-u)^2 σ(u)^2 du`. -/
lemma quadratic_variation_domination (p : ModelParams) (σ : ℝ → ℝ)
    (hσ_cont : ContinuousOn σ (Icc 0 p.T)) :
    (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 *
        (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 4 * (σ u) ^ 2) ≤
      (p.lam * p.q / 2) *
        (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ u) ^ 2) := by
  have hT_nonneg : 0 ≤ p.T := le_of_lt p.hT_pos
  have hInt1 : IntervalIntegrable (fun u => (p.T - u) ^ 4 * (σ u) ^ 2) volume 0 p.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT_nonneg]
    exact ((continuousOn_const.sub continuousOn_id).pow 4).mul (hσ_cont.pow 2)
  have hInt2 : IntervalIntegrable (fun u => p.T ^ 2 * ((p.T - u) ^ 2 * (σ u) ^ 2)) volume 0 p.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT_nonneg]
    exact continuousOn_const.mul (((continuousOn_const.sub continuousOn_id).pow 2).mul (hσ_cont.pow 2))
  have hMono :
      (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 4 * (σ u) ^ 2) ≤
        p.T ^ 2 * (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ u) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT_nonneg hInt1 hInt2
    intro u hu
    have h1 := quartic_le_sq_mul_sq hu.1 hu.2
    have h2 : 0 ≤ (σ u) ^ 2 := sq_nonneg (σ u)
    nlinarith
  have hCoeff :
      (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 * p.T ^ 2 = p.lam * p.q / 2 := by
    unfold ModelParams.lam
    have hϑ : p.ϑ ≠ 0 := ne_of_gt p.ϑ_pos
    have hT : p.T ≠ 0 := ne_of_gt p.hT_pos
    field_simp [hϑ, hT]
  have hFactor_nonneg : 0 ≤ (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 := by
    positivity
  calc
    (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 * (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 4 * (σ u) ^ 2)
        ≤ (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 *
            (p.T ^ 2 * (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ u) ^ 2)) :=
          mul_le_mul_of_nonneg_left hMono hFactor_nonneg
    _ = ((1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 * p.T ^ 2) *
          (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ u) ^ 2) := by ring
    _ = (p.lam * p.q / 2) * (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ u) ^ 2) := by
          rw [hCoeff]

/-- **Eq. (19) Main-Interval Non-Negativity**:
    For `u ∈ [0, T - δ_M]` and `x ≥ 0`, the entire integrand
    `(q/2)(T-u)^2 x^2 + (A_M (T-u)^2 - 2 (T-u)^(2-α) / Γ(3-α)) x` is `≥ 0`. -/
lemma main_interval_integrand_nonneg (p : ModelParams) {M u x : ℝ}
    (hA : 0 < p.A_M M) (hu : p.δ_M M ≤ p.T - u) (hx : 0 ≤ x) :
    0 ≤ (p.q / 2) * (p.T - u) ^ 2 * x ^ 2 +
        (p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * x := by
  have hδ_pos : 0 < p.δ_M M := p.δ_M_pos hA
  have hTu_pos : 0 < p.T - u := lt_of_lt_of_le hδ_pos hu
  have hTu_nonneg : 0 ≤ p.T - u := le_of_lt hTu_pos
  have hPow : (p.δ_M M) ^ p.α ≤ (p.T - u) ^ p.α :=
    Real.rpow_le_rpow (le_of_lt hδ_pos) hu (le_of_lt p.α_pos)
  rw [p.δ_M_rpow_α hA] at hPow
  have hΓ : 0 < Real.Gamma (3 - p.α) := p.Gamma_three_sub_α_pos
  have hMul : 2 / Real.Gamma (3 - p.α) ≤ p.A_M M * (p.T - u) ^ p.α := by
    have hAΓ : 0 < p.A_M M * Real.Gamma (3 - p.α) := mul_pos hA hΓ
    have h1 : 2 ≤ (p.T - u) ^ p.α * (p.A_M M * Real.Gamma (3 - p.α)) := by
      rwa [div_le_iff₀ hAΓ] at hPow
    rw [div_le_iff₀ hΓ]
    nlinarith
  have hSplit : (p.T - u) ^ (2 : ℝ) = (p.T - u) ^ (2 - p.α) * (p.T - u) ^ p.α := by
    rw [← Real.rpow_add hTu_pos]
    congr 1; ring
  have hSq : (p.T - u) ^ 2 = (p.T - u) ^ (2 : ℝ) := (Real.rpow_two (p.T - u)).symm
  have hLin_coeff : 0 ≤ p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α) := by
    rw [hSq, hSplit]
    have hFac :
        p.A_M M * ((p.T - u) ^ (2 - p.α) * (p.T - u) ^ p.α) -
          2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α) =
        (p.T - u) ^ (2 - p.α) * (p.A_M M * (p.T - u) ^ p.α - 2 / Real.Gamma (3 - p.α)) := by
      ring
    rw [hFac]
    exact mul_nonneg (Real.rpow_nonneg hTu_nonneg _) (sub_nonneg.mpr hMul)
  have hQuad : 0 ≤ (p.q / 2) * (p.T - u) ^ 2 * x ^ 2 := by
    have hq := le_of_lt p.q_pos
    positivity
  exact add_nonneg hQuad (mul_nonneg hLin_coeff hx)

/-- **Eq. (20) Pointwise Completing-the-Square Lower Bound on `[T - δ_M, T]`**:
    For `u < T` and `x ≥ 0` (with `A_M > 0`),
    `(q/2)(T-u)^2 x^2 + (A_M (T-u)^2 - 2 (T-u)^(2-α)/Γ(3-α)) x ≥ -2 (T-u)^(1-2H) / (q Γ(3-α)^2)`. -/
lemma endpoint_layer_pointwise_lower_bound (p : ModelParams) {M u x : ℝ}
    (hA : 0 < p.A_M M) (huT : u < p.T) (hx : 0 ≤ x) :
    -2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2) ≤
      (p.q / 2) * (p.T - u) ^ 2 * x ^ 2 +
        (p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * x := by
  have hTu_pos : 0 < p.T - u := sub_pos.mpr huT
  have hq_pos : 0 < p.q := p.q_pos
  have hΓ_pos : 0 < Real.Gamma (3 - p.α) := p.Gamma_three_sub_α_pos
  have hDrop : 0 ≤ p.A_M M * (p.T - u) ^ 2 * x := by positivity
  -- Completing the square: `a x^2 - b x + b^2 / (4 a) = a (x - b / (2a))^2 ≥ 0`
  set a : ℝ := (p.q / 2) * (p.T - u) ^ 2
  set b : ℝ := 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)
  have ha_pos : 0 < a := by positivity
  have hCS : -(b ^ 2 / (4 * a)) ≤ a * x ^ 2 - b * x := by
    have hsq : 0 ≤ a * (x - b / (2 * a)) ^ 2 := mul_nonneg (le_of_lt ha_pos) (sq_nonneg _)
    have hid : a * (x - b / (2 * a)) ^ 2 = a * x ^ 2 - b * x + b ^ 2 / (4 * a) := by
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      field_simp [ha_ne]; ring
    linarith
  -- Simplify `b^2 / (4a) = 2 (T-u)^(1-2H) / (q Γ(3-α)^2)`
  have hExp : ((p.T - u) ^ (2 - p.α)) ^ 2 / (p.T - u) ^ 2 = (p.T - u) ^ (1 - 2 * p.H) := by
    rw [← Real.rpow_natCast ((p.T - u) ^ (2 - p.α)) 2, ← Real.rpow_mul (le_of_lt hTu_pos)]
    rw [← Real.rpow_natCast (p.T - u) 2, ← Real.rpow_sub hTu_pos]
    congr 1
    unfold ModelParams.α
    norm_num; ring
  have hB2 : b ^ 2 / (4 * a) = 2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2) := by
    dsimp only [a, b]
    have hq_ne : p.q ≠ 0 := ne_of_gt hq_pos
    have hΓ_ne : Real.Gamma (3 - p.α) ≠ 0 := ne_of_gt hΓ_pos
    have hTu2_ne : (p.T - u) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hTu_pos)
    calc
      (2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) ^ 2 / (4 * (p.q / 2 * (p.T - u) ^ 2))
          = (2 * (((p.T - u) ^ (2 - p.α)) ^ 2 / (p.T - u) ^ 2)) / (p.q * (Real.Gamma (3 - p.α)) ^ 2) := by
              field_simp [hq_ne, hΓ_ne, hTu2_ne]; ring
      _ = 2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2) := by
              rw [hExp]
  have hLower : -2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2) = -(b ^ 2 / (4 * a)) := by
    rw [hB2]; ring
  rw [hLower]
  have hRearr :
      (p.q / 2) * (p.T - u) ^ 2 * x ^ 2 +
        (p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * x =
      (a * x ^ 2 - b * x) + p.A_M M * (p.T - u) ^ 2 * x := by
    dsimp only [a, b]; ring
  rw [hRearr]
  linarith

/-- **Eq. (21) Exact Boundary-Layer Integral Evaluation**:
    `∫_{T - δ}^T (2 (T - u)^(1 - 2H) / (q Γ(3 - α)^2)) du = δ^(2 - 2H) / (q (1 - H) Γ(3 - α)^2)`. -/
lemma boundary_layer_integral_eq (p : ModelParams) {δ : ℝ} (_hδ_nonneg : 0 ≤ δ) :
    (∫ u in (p.T - δ)..p.T,
        2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2)) =
      δ ^ (2 - 2 * p.H) / (p.q * (1 - p.H) * (Real.Gamma (3 - p.α)) ^ 2) := by
  have hExp_eq : (1 - 2 * p.H) + 1 = 2 - 2 * p.H := by ring
  -- Change of variable `v = T - u` via `intervalIntegral.integral_comp_sub_left`
  have hSub :
      (∫ u in (p.T - δ)..p.T, (p.T - u) ^ (1 - 2 * p.H)) =
        ∫ v in (0 : ℝ)..δ, v ^ (1 - 2 * p.H) := by
    simpa [sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (fun v => v ^ (1 - 2 * p.H)) p.T (a := p.T - δ) (b := p.T))
  have hPowInt :
      (∫ v in (0 : ℝ)..δ, v ^ (1 - 2 * p.H)) = δ ^ (2 - 2 * p.H) / (2 - 2 * p.H) := by
    rw [integral_rpow (Or.inl (by linarith [p.hH_le]))]
    rw [hExp_eq, Real.zero_rpow (by linarith [p.hH_le]), sub_zero]
  have hPull :
      (∫ u in (p.T - δ)..p.T,
          2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2)) =
        (2 / (p.q * (Real.Gamma (3 - p.α)) ^ 2)) *
          (∫ u in (p.T - δ)..p.T, (p.T - u) ^ (1 - 2 * p.H)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext u; ring
  rw [hPull, hSub, hPowInt]
  have hq_ne : p.q ≠ 0 := ne_of_gt p.q_pos
  have h1H_ne : (1 - p.H) ≠ 0 := ne_of_gt p.one_sub_H_pos
  have hΓ_ne : Real.Gamma (3 - p.α) ≠ 0 := ne_of_gt p.Gamma_three_sub_α_pos
  have h22H : 2 - 2 * p.H = 2 * (1 - p.H) := by ring
  rw [h22H]
  field_simp [hq_ne, h1H_ne, hΓ_ne]

/-- **Eq. (22) Deterministic Pathwise Integral Lower Bound**:
    Combining `[0, T - δ_M]` (Eq. 19) and `[T - δ_M, T]` (Eqs. 20–21) for any
    continuous non-negative path `σ` on `[0, T]`, whenever `A_M > 0` and `δ_M ≤ T`. -/
lemma split_integral_lower_bound (p : ModelParams) {M : ℝ}
    (hA : 0 < p.A_M M) (hδ_le : p.δ_M M ≤ p.T)
    (σ : ℝ → ℝ) (hσ_cont : ContinuousOn σ (Icc 0 p.T))
    (hσ_nonneg : ∀ u ∈ Icc 0 p.T, 0 ≤ σ u) :
    -p.tailTerm M ≤
      ∫ u in (0 : ℝ)..p.T,
        ((p.q / 2) * (p.T - u) ^ 2 * (σ u) ^ 2 +
          (p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ u) := by
  set f : ℝ → ℝ := fun u =>
    (p.q / 2) * (p.T - u) ^ 2 * (σ u) ^ 2 +
      (p.A_M M * (p.T - u) ^ 2 - 2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ u
  have hδ_pos : 0 < p.δ_M M := p.δ_M_pos hA
  have hSplit_pt : 0 ≤ p.T - p.δ_M M := sub_nonneg.mpr hδ_le
  have hSplit_le : p.T - p.δ_M M ≤ p.T := by linarith
  have hf_cont : ContinuousOn f (Icc 0 p.T) := by
    have h1 : ContinuousOn (fun u => p.T - u) (Icc 0 p.T) :=
      continuousOn_const.sub continuousOn_id
    have h2 : ContinuousOn (fun u => (p.T - u) ^ (2 - p.α)) (Icc 0 p.T) :=
      h1.rpow_const (fun u _ => Or.inr (by linarith [p.α_le_one]))
    exact (((continuousOn_const.mul (h1.pow 2)).mul (hσ_cont.pow 2)).add
      (((continuousOn_const.mul (h1.pow 2)).sub
        ((continuousOn_const.mul h2).div_const _)).mul hσ_cont))
  have hf_int1 : IntervalIntegrable f volume 0 (p.T - p.δ_M M) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hSplit_pt]
    exact hf_cont.mono (Icc_subset_Icc_right hSplit_le)
  have hf_int2 : IntervalIntegrable f volume (p.T - p.δ_M M) p.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hSplit_le]
    exact hf_cont.mono (Icc_subset_Icc_left hSplit_pt)
  rw [← intervalIntegral.integral_add_adjacent_intervals hf_int1 hf_int2]
  -- Bound 1: Main interval `[0, T - δ_M]` integral is ≥ 0
  have hMain_nonneg : 0 ≤ ∫ u in (0 : ℝ)..(p.T - p.δ_M M), f u := by
    apply intervalIntegral.integral_nonneg hSplit_pt
    intro u hu
    apply main_interval_integrand_nonneg p hA (by linarith [hu.2])
    exact hσ_nonneg u ⟨hu.1, le_trans hu.2 hSplit_le⟩
  -- Bound 2: Endpoint layer `[T - δ_M, T]` integral is ≥ -tailTerm M
  set g : ℝ → ℝ := fun u =>
    -(2 * (p.T - u) ^ (1 - 2 * p.H) / (p.q * (Real.Gamma (3 - p.α)) ^ 2))
  have hg_int : IntervalIntegrable g volume (p.T - p.δ_M M) p.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hSplit_le]
    have h1 : ContinuousOn (fun u => p.T - u) (Icc (p.T - p.δ_M M) p.T) :=
      continuousOn_const.sub continuousOn_id
    have h2 : ContinuousOn (fun u => (p.T - u) ^ (1 - 2 * p.H)) (Icc (p.T - p.δ_M M) p.T) :=
      h1.rpow_const (fun u _ => Or.inr p.one_sub_twoH_nonneg)
    exact ((continuousOn_const.mul h2).div_const _).neg
  have hLayer_bound : (∫ u in (p.T - p.δ_M M)..p.T, g u) ≤ ∫ u in (p.T - p.δ_M M)..p.T, f u := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hSplit_le hg_int hf_int2
    intro u hu
    have hu_in : u ∈ Icc 0 p.T := ⟨le_trans hSplit_pt (le_of_lt hu.1), le_of_lt hu.2⟩
    have hpt := endpoint_layer_pointwise_lower_bound p hA hu.2 (hσ_nonneg u hu_in)
    dsimp only [f, g]
    simpa [neg_div] using hpt
  have hg_val : (∫ u in (p.T - p.δ_M M)..p.T, g u) = -p.tailTerm M := by
    dsimp only [g, ModelParams.tailTerm]
    rw [intervalIntegral.integral_neg, boundary_layer_integral_eq p (le_of_lt hδ_pos)]
  linarith

/-- **Eq. (23) Classical Diffusion Specialization (`H = 1/2`)**:
    At `H = 1/2` (`α = 1`), `leadingTerm - tailTerm M = σ₀ T^2 - 4 / (q A_M)`. -/
lemma classical_endpoint_specialization (p : ModelParams) (hH : p.H = 1 / 2)
    {M : ℝ} (hA : 0 < p.A_M M) :
    p.leadingTerm - p.tailTerm M = p.σ₀ * p.T ^ 2 - 4 / (p.q * p.A_M M) := by
  have hα : p.α = 1 := by unfold ModelParams.α; linarith
  have hΓ2 : Real.Gamma (3 - 1) = 1 := by
    have : (3 : ℝ) - 1 = (1 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hΓ3 : Real.Gamma (4 - 1) = 2 := by
    have : (4 : ℝ) - 1 = (2 : ℕ) + 1 := by norm_num
    rw [this, Real.Gamma_nat_eq_factorial]
    norm_num
  have hδ : p.δ_M M = 2 / p.A_M M := by
    unfold ModelParams.δ_M
    rw [hα, hΓ2, mul_one, div_one, Real.rpow_one]
  unfold ModelParams.leadingTerm ModelParams.tailTerm
  rw [hδ, hα, hH, hΓ2, hΓ3]
  have h1 : (3 : ℝ) - 1 = 2 := by norm_num
  have h2 : (2 : ℝ) - 2 * (1 / 2) = 1 := by norm_num
  have h3 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h1, h2, h3, Real.rpow_two, Real.rpow_one]
  have hq_ne : p.q ≠ 0 := ne_of_gt p.q_pos
  have hA_ne : p.A_M M ≠ 0 := ne_of_gt hA
  field_simp [hq_ne, hA_ne]
  ring

/-- **Constructive Existence of Large `M` Yielding Strict Positive Margin (Eq. 22 → Eq. 24)**:
    For every admissible parameter set `p`, there exists `M > 0` such that:
    1. `A_M > 0`
    2. `δ_M ≤ T`
    3. `tailTerm M < leadingTerm` (so `ε₀ := λ (leadingTerm - tailTerm M) > 0`). -/
lemma exists_large_M_contradiction_margin (p : ModelParams) :
    ∃ M : ℝ, 0 < p.A_M M ∧ p.δ_M M ≤ p.T ∧ p.tailTerm M < p.leadingTerm := by
  -- Choose a target δ₀ > 0 small enough that both `δ₀ ≤ T` and `δ₀^(2-2H) < ...`
  set C_tail : ℝ := p.q * (1 - p.H) * (Real.Gamma (3 - p.α)) ^ 2
  have hC_pos : 0 < C_tail := by
    have hq := p.q_pos; have h1H := p.one_sub_H_pos; have hΓ := p.Gamma_three_sub_α_pos
    positivity
  set r : ℝ := (p.leadingTerm * C_tail / 2) ^ (1 / (2 - 2 * p.H))
  have h22H_pos : 0 < 2 - 2 * p.H := by linarith [p.two_sub_twoH_ge_one]
  have hr_pos : 0 < r :=
    Real.rpow_pos_of_pos (div_pos (mul_pos p.leadingTerm_pos hC_pos) (by norm_num)) _
  set δ₀ : ℝ := min p.T r
  have hδ₀_pos : 0 < δ₀ := lt_min p.hT_pos hr_pos
  have hδ₀_le_T : δ₀ ≤ p.T := min_le_left _ _
  have hδ₀_le_r : δ₀ ≤ r := min_le_right _ _
  -- Solve `δ_M M = δ₀` explicitly for `A_target := 2 / (δ₀^α * Γ(3 - α))`
  set A_target : ℝ := 2 / (δ₀ ^ p.α * Real.Gamma (3 - p.α))
  have hA_target_pos : 0 < A_target :=
    div_pos (by norm_num) (mul_pos (Real.rpow_pos_of_pos hδ₀_pos _) p.Gamma_three_sub_α_pos)
  set M : ℝ := (A_target - p.c₁) / p.ϑ
  have hAM_eq : p.A_M M = A_target := by
    unfold ModelParams.A_M
    dsimp only [M]
    have hϑ_ne : p.ϑ ≠ 0 := ne_of_gt p.ϑ_pos
    field_simp [hϑ_ne]; ring
  have hAM_pos : 0 < p.A_M M := hAM_eq.symm ▸ hA_target_pos
  have hδM_eq : p.δ_M M = δ₀ := by
    unfold ModelParams.δ_M
    rw [hAM_eq]
    have hΓ_ne : Real.Gamma (3 - p.α) ≠ 0 := ne_of_gt p.Gamma_three_sub_α_pos
    have hδα_ne : δ₀ ^ p.α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hδ₀_pos _)
    have hSimp : 2 / (A_target * Real.Gamma (3 - p.α)) = δ₀ ^ p.α := by
      dsimp only [A_target]
      field_simp [hΓ_ne, hδα_ne]
    rw [hSimp, ← Real.rpow_mul (le_of_lt hδ₀_pos), mul_one_div_cancel (ne_of_gt p.α_pos),
      Real.rpow_one]
  refine ⟨M, hAM_pos, hδM_eq.symm ▸ hδ₀_le_T, ?_⟩
  unfold ModelParams.tailTerm
  rw [hδM_eq]
  change δ₀ ^ (2 - 2 * p.H) / C_tail < p.leadingTerm
  rw [div_lt_iff₀ hC_pos]
  have hPow_le : δ₀ ^ (2 - 2 * p.H) ≤ r ^ (2 - 2 * p.H) :=
    Real.rpow_le_rpow (le_of_lt hδ₀_pos) hδ₀_le_r (le_of_lt h22H_pos)
  have hr_pow : r ^ (2 - 2 * p.H) = p.leadingTerm * C_tail / 2 := by
    dsimp only [r]
    rw [← Real.rpow_mul (le_of_lt (div_pos (mul_pos p.leadingTerm_pos hC_pos) (by norm_num))),
      one_div_mul_cancel (ne_of_gt h22H_pos), Real.rpow_one]
  have hProd_pos : 0 < p.leadingTerm * C_tail := mul_pos p.leadingTerm_pos hC_pos
  linarith

end Layer1Analysis

/-! ## Layer 2: Minimal Stochastic Calculus Interface (Steps 3.1–3.3) -/

section Layer2StochasticInterface

/--
Explicit, minimal stochastic-calculus interface encapsulating the three
continuous-time stochastic analysis inputs from Sections 3.1–3.3 of the paper
(which are currently outside Mathlib4's library coverage):

1. **Step 3.1 (`share_and_cameron_martin_tilt`)**:
   Under the contradiction hypothesis `E_Q[S_T] = S_0`, `S/S_0` is a true
   `Q`-martingale on `[0, T]`, so for every constant `M : ℝ`, there exists an
   equivalent probability measure `Q_hat_M` under which `σ` remains a.s.
   continuous and non-negative on `[0, T]`, and satisfies Eq. (7).
2. **Step 3.2 (`resolvent_fujita_kaplan_identity`)**:
   First-kind Volterra resolvent inversion (Abi Jaber–Larsson–Pulido 2019,
   Lemma 2.6 + localization `τ_n`) and Itô integration by parts with
   `φ(u) = (T - u)^2` yield the exact pathwise identity Eq. (14) `Q_hat_M`-a.s.
3. **Step 3.3 (`doleans_dade_supermartingale_bound`)**:
   Fatou's lemma applied to the stopped Doléans–Dade exponential of `-λ M_t`
   yields `E_{Q_hat_M}[exp(-λ M_T - (1/2) λ^2 ⟨M⟩_T)] ≤ 1` (Eq. 15).
-/
structure VolterraMartingaleInterface (p : ModelParams) where
  /-- Underlying sample space `Ω`. -/
  Ω : Type*
  /-- Asset price expectation `E_Q[S_T]` and initial price `S_0`. -/
  E_S_T : ℝ
  S₀ : ℝ
  /-- Supermartingale property of the non-negative local martingale `S`: `E_Q[S_T] ≤ S_0`. -/
  supermartingale_le : E_S_T ≤ S₀
  /--
  If `E_Q[S_T] = S_0`, then for every constant `M : ℝ` with `A_M > 0`, there exist:
  - a probability-expectation functional `E_M` (corresponding to `E_{Q_hat_M}`),
  - a volatility path family `σ : Ω → ℝ → ℝ`,
  - a terminal local martingale `M_T : Ω → ℝ`,
  - an event `Good : Set Ω` of full `Q_hat_M`-measure (where `σ ω` is continuous
    and non-negative on `[0, T]` and Eq. (14) holds pathwise),
  satisfying:
  - Monotonicity of `E_M` on deterministic constants (`Good`-a.s. lower bound `c ≤ X` ⇒ `c ≤ E_M X`),
  - Pathwise Fujita–Kaplan identity Eq. (14) on `Good`,
  - Doléans–Dade supermartingale bound Eq. (15).
  -/
  tilted_system :
    E_S_T = S₀ →
    ∀ M : ℝ, 0 < p.A_M M →
      ∃ (E_M : (Ω → ℝ) → ℝ) (σ : Ω → ℝ → ℝ) (M_T : Ω → ℝ) (Good : Set Ω),
        -- (a) Continuity and non-negativity of `σ ω` on `[0, T]` for `ω ∈ Good`
        (∀ ω ∈ Good, ContinuousOn (σ ω) (Icc 0 p.T) ∧ ∀ u ∈ Icc 0 p.T, 0 ≤ σ ω u) ∧
        -- (b) Exact pathwise Fujita–Kaplan identity (Eq. 14) on `Good`
        (∀ ω ∈ Good,
          -M_T ω =
            p.leadingTerm + p.c₀ * p.T ^ 3 / 3 +
            ∫ u in (0 : ℝ)..p.T,
              (p.q * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
                (p.A_M M * (p.T - u) ^ 2 -
                  2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u)) ∧
        -- (c) Doléans–Dade exponential supermartingale bound (Eq. 15)
        E_M (fun ω => Real.exp (-(p.lam * M_T ω) -
            (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 *
              (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 4 * (σ ω u) ^ 2))) ≤ 1 ∧
        -- (d) Constant lower-bound monotonicity of expectation `E_M`
        (∀ (c : ℝ) (X : Ω → ℝ), (∀ ω ∈ Good, c ≤ X ω) → c ≤ E_M X)

end Layer2StochasticInterface

/-! ## Layer 3: End-to-End Proof of Conjecture 4.5 (Zero `sorry`) -/

section Layer3MainTheorem

/--
**Main Theorem (Conjecture 4.5 of Sepp & Rakhmonov 2026)**:
For every `H ∈ (0, 1/2]`, `σ₀ > 0`, `κ₁ ≥ 0`, `κ₂ ≥ 0`, `θ ≥ 0`, `β > κ₂`,
and every maturity `T > 0`, the asset price `S` is a strict local martingale:
`E_Q[S_T] < S_0`.
-/
theorem conjecture_4_5 (p : ModelParams) (I : VolterraMartingaleInterface p) :
    I.E_S_T < I.S₀ := by
  -- Since `E_S_T ≤ S₀`, it suffices to rule out `E_S_T = S₀`.
  refine lt_of_le_of_ne I.supermartingale_le ?_
  intro hEq
  -- Step 4: Pick `M` via Layer 1 so that `A_M > 0`, `δ_M ≤ T`, and `tailTerm M < leadingTerm`.
  obtain ⟨M, hAM_pos, hδ_le, hMargin⟩ := exists_large_M_contradiction_margin p
  -- Steps 1–3: Extract the tilted system under `Q_hat_M` from Layer 2.
  obtain ⟨E_M, σ, M_T, Good, hReg, hFK, hDD, hMono⟩ := I.tilted_system hEq M hAM_pos
  -- Define the strictly positive deterministic lower bound `ε₀ > 0`.
  set ε₀ : ℝ := p.lam * (p.leadingTerm - p.tailTerm M)
  have hε₀_pos : 0 < ε₀ := mul_pos p.lam_pos (sub_pos.mpr hMargin)
  -- Show that on `Good`, the Doléans–Dade exponent is pathwise bounded below by `ε₀`.
  have hPathwise :
      ∀ ω ∈ Good,
        Real.exp ε₀ ≤
          Real.exp (-(p.lam * M_T ω) -
            (1 / 2) * p.lam ^ 2 * p.ϑ ^ 2 *
              (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 4 * (σ ω u) ^ 2)) := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    obtain ⟨hσ_cont, hσ_nonneg⟩ := hReg ω hω
    have hT_nonneg : 0 ≤ p.T := le_of_lt p.hT_pos
    -- Quadratic variation domination (Eq. 16)
    have hQV := quadratic_variation_domination p (σ ω) hσ_cont
    -- Split-integral lower bound (Eq. 22)
    have hSplit := split_integral_lower_bound p hAM_pos hδ_le (σ ω) hσ_cont hσ_nonneg
    -- Non-negativity of `c₀ T^3 / 3`
    have hc₀_term : 0 ≤ p.c₀ * p.T ^ 3 / 3 := by
      have hc₀ := p.c₀_nonneg
      have hT := le_of_lt p.hT_pos
      positivity
    -- Algebraic combination of Eq. (14) and Eq. (16) to obtain Eq. (17)
    have hInt_q :
        IntervalIntegrable (fun u => (p.q / 2) * (p.T - u) ^ 2 * (σ ω u) ^ 2) volume 0 p.T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT_nonneg]
      exact (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)).mul
        (hσ_cont.pow 2)
    have hInt_q' :
        IntervalIntegrable (fun x => p.q / 2 * ((p.T - x) ^ 2 * (σ ω x) ^ 2)) volume 0 p.T := by
      simpa [mul_assoc] using hInt_q
    have hInt_rem :
        IntervalIntegrable
          (fun u =>
            (p.q / 2) * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
              (p.A_M M * (p.T - u) ^ 2 -
                2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u)
          volume 0 p.T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT_nonneg]
      have h1 : ContinuousOn (fun u => p.T - u) (Icc 0 p.T) :=
        continuousOn_const.sub continuousOn_id
      have h2 : ContinuousOn (fun u => (p.T - u) ^ (2 - p.α)) (Icc 0 p.T) :=
        h1.rpow_const (fun u _ => Or.inr (by linarith [p.α_le_one]))
      exact (((continuousOn_const.mul (h1.pow 2)).mul (hσ_cont.pow 2)).add
        (((continuousOn_const.mul (h1.pow 2)).sub
          ((continuousOn_const.mul h2).div_const _)).mul hσ_cont))
    have hInt_decomp :
        (∫ u in (0 : ℝ)..p.T,
            (p.q * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
              (p.A_M M * (p.T - u) ^ 2 -
                2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u)) =
          (p.q / 2) * (∫ u in (0 : ℝ)..p.T, (p.T - u) ^ 2 * (σ ω u) ^ 2) +
          (∫ u in (0 : ℝ)..p.T,
            ((p.q / 2) * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
              (p.A_M M * (p.T - u) ^ 2 -
                2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hInt_q' hInt_rem]
      congr 1; ext u; ring
    have hFK_ω := hFK ω hω
    have hNeg : -(p.lam * M_T ω) = p.lam * (-M_T ω) := by ring
    rw [hNeg, hFK_ω, hInt_decomp]
    have hlam_nonneg : 0 ≤ p.lam := le_of_lt p.lam_pos
    nlinarith
  -- Step 4 Finale (Eq. 24): `1 < exp ε₀ ≤ E_M[...] ≤ 1`, contradiction!
  have h1_lt_exp : 1 < Real.exp ε₀ := Real.one_lt_exp_iff.mpr hε₀_pos
  have hexp_le_EM := hMono (Real.exp ε₀) _ hPathwise
  linarith

end Layer3MainTheorem


end RoughLogSVConjecture45

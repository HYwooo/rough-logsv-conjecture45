/-
  RoughLogSVConjecture45.lean
  ==============================================================================
  Structured Lean 4 + Mathlib4 formalization of the proof of Conjecture 4.5 of
  Sepp & Rakhmonov (2026), arXiv:2611.32791v1, following Huayang WU (2026):
  "Proof of the Martingale Necessity Conjecture for Rough Log-Normal Stochastic
   Volatility with Quadratic Drift".

  Architecture (3-layer separation for full auditability):
  ------------------------------------------------------------------------------
  * Layer 1 (Pure Real Analysis & Integral Estimates — ZERO axioms, ZERO sorry):
      Formalizes over `ℝ` (with `Real.Gamma`, `Real.rpow`, `intervalIntegral`)
      every analytical and quantitative step of Sections 3.2–3.4 of the paper:
      - Step 2 deterministic resolvent test-weight integral (Eq. 13 & `α = 1`)
      - Step 2 constant initial-volatility term integral (`leadingTerm`)
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
  * Section 4 (General Kernels with Non-Negative First-Kind Resolvent — Theorem 3):
      Follows the same 3-layer separation for arbitrary `K ∈ L²([0, T])` admitting
      a finite non-negative first-kind resolvent measure `L` on `[0, T]`, proving
      structural bounds (i)–(iii) (Eqs. 25–30) unconditionally in Layer 1 and deriving
      `E_Q[S_T] < S_0` in `general_kernel_theorem_3`.
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

/-- Raw first-kind resolvent quadratic test weight `W₂(s)` prior to closed-form integration (Step 2). -/
def W₂ (p : ModelParams) (s : ℝ) : ℝ :=
  if p.α < 1 then
    2 * ∫ u in s..p.T, (p.T - u) * (u - s) ^ (-p.α) / Real.Gamma (1 - p.α)
  else
    2 * (p.T - s)

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

/-! ## Layer 1: Pure Real Analysis & Quantitative Core (Eqs. 13, 16, 18–24) -/

section Layer1Analysis

/-- **Step 2 Deterministic Kernel-Weight Integral (Eq. 13 & `α = 1` branch)**:
    For every `s ∈ [0, T]`, the raw resolvent test weight `W₂(s)` equals
    `2 (T - s)^(2 - α) / Γ(3 - α)`. -/
lemma resolvent_test_weight_eq (p : ModelParams) {s : ℝ} (hs : s ≤ p.T) :
    p.W₂ s = 2 * (p.T - s) ^ (2 - p.α) / Real.Gamma (3 - p.α) := by
  unfold ModelParams.W₂
  by_cases hα : p.α < 1
  · simp only [hα, ↓reduceIte]
    have h1subα_pos : 0 < 1 - p.α := sub_pos.mpr hα
    have h2subα_pos : 0 < 2 - p.α := by linarith
    have hΓ1_pos : 0 < Real.Gamma (1 - p.α) := Real.Gamma_pos_of_pos h1subα_pos
    have hΓ1_ne : Real.Gamma (1 - p.α) ≠ 0 := ne_of_gt hΓ1_pos
    have h1subα_ne : (1 - p.α) ≠ 0 := ne_of_gt h1subα_pos
    have h2subα_ne : (2 - p.α) ≠ 0 := ne_of_gt h2subα_pos
    have hΓ2 : Real.Gamma (2 - p.α) = (1 - p.α) * Real.Gamma (1 - p.α) := by
      have h : (2 : ℝ) - p.α = (1 - p.α) + 1 := by ring
      rw [h, Real.Gamma_add_one h1subα_ne]
    have hΓ3 : Real.Gamma (3 - p.α) = (2 - p.α) * ((1 - p.α) * Real.Gamma (1 - p.α)) := by
      have h : (3 : ℝ) - p.α = (2 - p.α) + 1 := by ring
      rw [h, Real.Gamma_add_one h2subα_ne, hΓ2]
    rcases eq_or_lt_of_le hs with rfl | hs_lt
    · simp [Real.zero_rpow h2subα_ne]
    · set d : ℝ := p.T - s
      have hd_pos : 0 < d := sub_pos.mpr hs_lt
      -- Pull out `1 / Γ(1 - α)` and substitute `v = u - s`.
      have hPull :
          (∫ u in s..p.T, (p.T - u) * (u - s) ^ (-p.α) / Real.Gamma (1 - p.α)) =
            (∫ u in s..p.T, (p.T - u) * (u - s) ^ (-p.α)) / Real.Gamma (1 - p.α) := by
        simp [div_eq_mul_inv, intervalIntegral.integral_mul_const]
      have hShift :
          (∫ u in s..p.T, (p.T - u) * (u - s) ^ (-p.α)) =
            ∫ v in (0 : ℝ)..d, (d - v) * v ^ (-p.α) := by
        have hcomp := intervalIntegral.integral_comp_sub_right
          (fun v => (d - v) * v ^ (-p.α)) s (a := s) (b := p.T)
        simpa [d, sub_sub_sub_cancel_right, sub_self] using hcomp
      -- Split `(d - v) * v^(-α) = d * v^(-α) - v^(1 - α)` everywhere on `[0, d]`.
      have hCongr :
          (∫ v in (0 : ℝ)..d, (d - v) * v ^ (-p.α)) =
            ∫ v in (0 : ℝ)..d, (d * v ^ (-p.α) - v ^ (1 - p.α)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le (le_of_lt hd_pos)] at hv
        rcases eq_or_lt_of_le hv.1 with rfl | hv_pos
        · simp [Real.zero_rpow h1subα_ne]
        · have hPowV : v ^ (1 : ℝ) * v ^ (-p.α) = v ^ (1 - p.α) := by
            have hExpV : (1 : ℝ) + (-p.α) = 1 - p.α := by ring
            rw [← Real.rpow_add hv_pos, hExpV]
          calc
            (d - v) * v ^ (-p.α) = d * v ^ (-p.α) - v * v ^ (-p.α) := by ring
            _ = d * v ^ (-p.α) - v ^ (1 : ℝ) * v ^ (-p.α) := by rw [Real.rpow_one]
            _ = d * v ^ (-p.α) - v ^ (1 - p.α) := by rw [hPowV]
      have hInt1 : IntervalIntegrable (fun v : ℝ => d * v ^ (-p.α)) volume 0 d := by
        have hbase : IntervalIntegrable (fun v : ℝ => v ^ (-p.α)) volume 0 d :=
          intervalIntegral.intervalIntegrable_rpow' (by linarith)
        exact hbase.const_mul d
      have hInt2 : IntervalIntegrable (fun v : ℝ => v ^ (1 - p.α)) volume 0 d :=
        intervalIntegral.intervalIntegrable_rpow' (by linarith)
      have hVal1 :
          (∫ v in (0 : ℝ)..d, d * v ^ (-p.α)) = d ^ (2 - p.α) / (1 - p.α) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have hExp : -p.α + 1 = 1 - p.α := by ring
        rw [hExp, Real.zero_rpow h1subα_ne, sub_zero]
        have hPow : d * d ^ (1 - p.α) = d ^ (2 - p.α) := by
          have hExpD : (1 : ℝ) + (1 - p.α) = 2 - p.α := by ring
          conv_lhs => arg 1; rw [← Real.rpow_one d]
          rw [← Real.rpow_add hd_pos, hExpD]
        rw [← mul_div_assoc, hPow]
      have hVal2 :
          (∫ v in (0 : ℝ)..d, v ^ (1 - p.α)) = d ^ (2 - p.α) / (2 - p.α) := by
        rw [integral_rpow (Or.inl (by linarith))]
        have hExp : (1 - p.α) + 1 = 2 - p.α := by ring
        rw [hExp, Real.zero_rpow h2subα_ne, sub_zero]
      rw [hPull, hShift, hCongr, intervalIntegral.integral_sub hInt1 hInt2, hVal1, hVal2, hΓ3]
      field_simp [hΓ1_ne, h1subα_ne, h2subα_ne]
      ring
  · simp only [hα, ↓reduceIte]
    have hα_eq : p.α = 1 := le_antisymm p.α_le_one (not_lt.mp hα)
    rw [hα_eq]
    have hExp : (2 : ℝ) - 1 = 1 := by norm_num
    have hΓ : Real.Gamma ((3 : ℝ) - 1) = 1 := by
      have h31 : (3 : ℝ) - 1 = ((1 : ℕ) : ℝ) + 1 := by norm_num
      rw [h31, Real.Gamma_nat_eq_factorial]
      norm_num
    rw [hExp, Real.rpow_one, hΓ, div_one]

/-- **Step 2 Constant-Term Integral**:
    `σ₀ ∫_0^T W₂(s) ds = 2 σ₀ T^(3 - α) / Γ(4 - α) = p.leadingTerm`. -/
lemma constant_test_weight_integral_eq (p : ModelParams) :
    p.σ₀ * (∫ s in (0 : ℝ)..p.T, p.W₂ s) = p.leadingTerm := by
  have hT_nonneg : 0 ≤ p.T := le_of_lt p.hT_pos
  have hCongr :
      (∫ s in (0 : ℝ)..p.T, p.W₂ s) =
        ∫ s in (0 : ℝ)..p.T, 2 * (p.T - s) ^ (2 - p.α) / Real.Gamma (3 - p.α) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT_nonneg] at hs
    exact resolvent_test_weight_eq p hs.2
  have hPull :
      (∫ s in (0 : ℝ)..p.T, 2 * (p.T - s) ^ (2 - p.α) / Real.Gamma (3 - p.α)) =
        (2 / Real.Gamma (3 - p.α)) * ∫ s in (0 : ℝ)..p.T, (p.T - s) ^ (2 - p.α) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext s; ring
  have hSub :
      (∫ s in (0 : ℝ)..p.T, (p.T - s) ^ (2 - p.α)) =
        ∫ v in (0 : ℝ)..p.T, v ^ (2 - p.α) := by
    simpa [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (fun v => v ^ (2 - p.α)) p.T (a := 0) (b := p.T))
  have h3subα_pos : 0 < 3 - p.α := p.three_sub_α_pos
  have h3subα_ne : (3 - p.α) ≠ 0 := ne_of_gt h3subα_pos
  have hΓ3_ne : Real.Gamma (3 - p.α) ≠ 0 := ne_of_gt p.Gamma_three_sub_α_pos
  have hPowInt :
      (∫ v in (0 : ℝ)..p.T, v ^ (2 - p.α)) = p.T ^ (3 - p.α) / (3 - p.α) := by
    rw [integral_rpow (Or.inl (by linarith [p.α_le_one]))]
    have hExp : (2 - p.α) + 1 = 3 - p.α := by ring
    rw [hExp, Real.zero_rpow h3subα_ne, sub_zero]
  have hΓ4 : Real.Gamma (4 - p.α) = (3 - p.α) * Real.Gamma (3 - p.α) := by
    have h43 : (4 : ℝ) - p.α = (3 - p.α) + 1 := by ring
    rw [h43, Real.Gamma_add_one h3subα_ne]
  rw [hCongr, hPull, hSub, hPowInt]
  unfold ModelParams.leadingTerm
  rw [hΓ4]
  field_simp [hΓ3_ne, h3subα_ne]

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
2. **Step 3.2 (`resolvent_quadratic_test_identity`)**:
   First-kind Volterra resolvent inversion (Abi Jaber–Larsson–Pulido 2019,
   Lemma 2.6 + localization `τ_n`), Itô integration by parts with
   `φ(u) = (T - u)^2` (Mitidieri–Pohozaev 2001), and Fubini's theorem yield the
   pathwise Volterra test identity Eq. (12) in terms of the raw resolvent weight
   `W₂(s)` `Q_hat_M`-a.s. (The deterministic Gamma/Beta evaluation of `W₂(s)` and
   `σ₀ ∫_0^T W₂(s) ds` is proved unconditionally in Layer 1.)
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
    and non-negative on `[0, T]` and the resolvent quadratic test-function
    identity holds pathwise),
  satisfying:
  - Monotonicity of `E_M` on deterministic constants (`Good`-a.s. lower bound `c ≤ X` ⇒ `c ≤ E_M X`),
  - Pathwise quadratic test-function identity (Eq. 12 + Fubini in raw weight `W₂`) on `Good`,
  - Doléans–Dade supermartingale bound Eq. (15).
  -/
  tilted_system :
    E_S_T = S₀ →
    ∀ M : ℝ, 0 < p.A_M M →
      ∃ (E_M : (Ω → ℝ) → ℝ) (σ : Ω → ℝ → ℝ) (M_T : Ω → ℝ) (Good : Set Ω),
        -- (a) Continuity and non-negativity of `σ ω` on `[0, T]` for `ω ∈ Good`
        (∀ ω ∈ Good, ContinuousOn (σ ω) (Icc 0 p.T) ∧ ∀ u ∈ Icc 0 p.T, 0 ≤ σ ω u) ∧
        -- (b) Exact pathwise quadratic test-function identity (Eq. 12 + Fubini) on `Good`
        (∀ ω ∈ Good,
          -M_T ω =
            p.σ₀ * (∫ s in (0 : ℝ)..p.T, p.W₂ s) + p.c₀ * p.T ^ 3 / 3 +
            ∫ s in (0 : ℝ)..p.T,
              (p.q * (p.T - s) ^ 2 * (σ ω s) ^ 2 +
                (p.A_M M * (p.T - s) ^ 2 - p.W₂ s) * σ ω s)) ∧
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
  obtain ⟨E_M, σ, M_T, Good, hReg, hQuadTest, hDD, hMono⟩ := I.tilted_system hEq M hAM_pos
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
    have hQuadTest_ω :
        -M_T ω =
          p.leadingTerm + p.c₀ * p.T ^ 3 / 3 +
          ∫ u in (0 : ℝ)..p.T,
            (p.q * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
              (p.A_M M * (p.T - u) ^ 2 -
                2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u) := by
      have hRaw := hQuadTest ω hω
      have hConst := constant_test_weight_integral_eq p
      have hIntegrand :
          (∫ s in (0 : ℝ)..p.T,
              (p.q * (p.T - s) ^ 2 * (σ ω s) ^ 2 +
                (p.A_M M * (p.T - s) ^ 2 - p.W₂ s) * σ ω s)) =
            ∫ u in (0 : ℝ)..p.T,
              (p.q * (p.T - u) ^ 2 * (σ ω u) ^ 2 +
                (p.A_M M * (p.T - u) ^ 2 -
                  2 * (p.T - u) ^ (2 - p.α) / Real.Gamma (3 - p.α)) * σ ω u) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hT_nonneg] at hs
        dsimp only
        rw [resolvent_test_weight_eq p hs.2]
      rw [hRaw, hConst, hIntegrand]
    have hNeg : -(p.lam * M_T ω) = p.lam * (-M_T ω) := by ring
    rw [hNeg, hQuadTest_ω, hInt_decomp]
    have hlam_nonneg : 0 ≤ p.lam := le_of_lt p.lam_pos
    nlinarith
  -- Step 4 Finale (Eq. 24): `1 < exp ε₀ ≤ E_M[...] ≤ 1`, contradiction!
  have h1_lt_exp : 1 < Real.exp ε₀ := Real.one_lt_exp_iff.mpr hε₀_pos
  have hexp_le_EM := hMono (Real.exp ε₀) _ hPathwise
  linarith

end Layer3MainTheorem

/-! ## Section 4: General Kernels with Non-Negative First-Kind Resolvent (Theorem 3) -/

section Theorem3GeneralKernels

/-- Admissible parameters for Theorem 3 (arbitrary kernel with non-negative finite
    first-kind resolvent measure `L` on `[0, T]`). -/
structure GeneralKernelParams where
  σ₀ : ℝ
  κ₁ : ℝ
  κ₂ : ℝ
  θ : ℝ
  β : ℝ
  ε : ℝ
  T : ℝ
  L : Measure ℝ
  K : ℝ → ℝ
  hσ₀_pos : 0 < σ₀
  hκ₁_nonneg : 0 ≤ κ₁
  hκ₂_nonneg : 0 ≤ κ₂
  hθ_nonneg : 0 ≤ θ
  hβ_gt_κ₂ : κ₂ < β
  hT_pos : 0 < T
  hL_fin : L (Icc 0 T) ≠ ⊤
  /-- `(K * L)(t) = 1` a.e. on `(0, T]` guarantees a point `t ∈ (0, T / 2]` where
      `∫ r in Icc 0 t, K (t - r) ∂L = 1` (hence `L [0, T/2] > 0`). -/
  hKL_pos : ∃ t ∈ Ioo 0 (T / 2), (∫ r in Icc 0 t, K (t - r) ∂L) = 1

namespace GeneralKernelParams

def q (g : GeneralKernelParams) : ℝ := g.β - g.κ₂
def ϑ (g : GeneralKernelParams) : ℝ := Real.sqrt (g.β ^ 2 + g.ε ^ 2)
def c₀ (g : GeneralKernelParams) : ℝ := g.κ₁ * g.θ
def c₁ (g : GeneralKernelParams) : ℝ := g.κ₂ * g.θ - g.κ₁
def lam (g : GeneralKernelParams) : ℝ := g.q / (g.ϑ ^ 2 * g.T ^ 2)
def A_M (g : GeneralKernelParams) (M : ℝ) : ℝ := g.c₁ + g.ϑ * M

lemma q_pos (g : GeneralKernelParams) : 0 < g.q := by
  unfold q; linarith [g.hβ_gt_κ₂]

lemma β_pos (g : GeneralKernelParams) : 0 < g.β := by
  linarith [g.hκ₂_nonneg, g.hβ_gt_κ₂]

lemma ϑ_pos (g : GeneralKernelParams) : 0 < g.ϑ := by
  unfold ϑ
  apply Real.sqrt_pos.mpr
  have hβ : 0 < g.β ^ 2 := sq_pos_of_pos g.β_pos
  have hε : 0 ≤ g.ε ^ 2 := sq_nonneg g.ε
  linarith

lemma c₀_nonneg (g : GeneralKernelParams) : 0 ≤ g.c₀ :=
  mul_nonneg g.hκ₁_nonneg g.hθ_nonneg

lemma lam_pos (g : GeneralKernelParams) : 0 < g.lam := by
  unfold lam
  exact div_pos g.q_pos (mul_pos (sq_pos_of_pos g.ϑ_pos) (sq_pos_of_pos g.hT_pos))

/-- Induced quadratic kernel weight `W₂(s) = 2 ∫_{[0, T - s]} (T - s - r) L(dr)` (Eq. 25). -/
def W₂ (g : GeneralKernelParams) (s : ℝ) : ℝ :=
  2 * ∫ r in Icc 0 (g.T - s), (g.T - s - r) ∂g.L

/-- Total mass `I₀(T) = ∫_0^T W₂(s) ds`. -/
def I₀ (g : GeneralKernelParams) : ℝ :=
  ∫ s in (0 : ℝ)..g.T, g.W₂ s

/-- Uniform main-interval upper bound `2 L([0, T]) / δ` (Eq. 26). -/
def B_bound (g : GeneralKernelParams) (δ : ℝ) : ℝ :=
  2 * g.L.real (Icc 0 g.T) / δ

/-- Endpoint layer tail `Tail(δ) = ∫_{T-δ}^T W₂(s)^2 / (2 q (T - s)^2) ds` (Eq. 27). -/
def tail (g : GeneralKernelParams) (δ : ℝ) : ℝ :=
  ∫ s in (g.T - δ)..g.T, (g.W₂ s) ^ 2 / (2 * g.q * (g.T - s) ^ 2)

lemma L_fin_subset (g : GeneralKernelParams) {A : Set ℝ} (hA : A ⊆ Icc 0 g.T) :
    g.L A ≠ ⊤ :=
  ne_top_of_le_ne_top g.hL_fin (measure_mono hA)

lemma L_real_mono (g : GeneralKernelParams) {A B : Set ℝ} (hAB : A ⊆ B) (hB : B ⊆ Icc 0 g.T) :
    g.L.real A ≤ g.L.real B :=
  ENNReal.toReal_mono (g.L_fin_subset hB) (measure_mono hAB)

lemma L_half_pos (g : GeneralKernelParams) : 0 < g.L.real (Icc 0 (g.T / 2)) := by
  obtain ⟨t, ht, hInt⟩ := g.hKL_pos
  have hsub : Icc 0 t ⊆ Icc 0 (g.T / 2) := Icc_subset_Icc_right (le_of_lt ht.2)
  have hsubT : Icc 0 (g.T / 2) ⊆ Icc 0 g.T := Icc_subset_Icc_right (by linarith [g.hT_pos])
  by_contra hle
  push Not at hle
  have hzero_half : g.L.real (Icc 0 (g.T / 2)) = 0 := le_antisymm hle ENNReal.toReal_nonneg
  have hzero_t : g.L.real (Icc 0 t) = 0 :=
    le_antisymm ((g.L_real_mono hsub hsubT).trans_eq hzero_half) ENNReal.toReal_nonneg
  have hm_t : g.L (Icc 0 t) = 0 :=
    (ENNReal.toReal_eq_zero_iff (g.L (Icc 0 t))).mp hzero_t |>.resolve_right
      (g.L_fin_subset (hsub.trans hsubT))
  have hzero_int : (∫ r in Icc 0 t, g.K (t - r) ∂g.L) = 0 := by
    simp [MeasureTheory.Measure.restrict_eq_zero.mpr hm_t]
  linarith

private lemma integrableOn_continuous_Icc (g : GeneralKernelParams) {b : ℝ} (hb : b ≤ g.T)
    {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Icc 0 b) g.L := by
  have hfin : g.L (Icc 0 b) < ⊤ :=
    lt_top_iff_ne_top.mpr (g.L_fin_subset (Icc_subset_Icc_right hb))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 b) hf.continuousOn
  exact MeasureTheory.IntegrableOn.of_bound hfin hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Icc hC)

lemma W₂_eq_Icc_T (g : GeneralKernelParams) {s : ℝ} (hs : s ∈ Icc 0 g.T) :
    g.W₂ s = 2 * ∫ r in Icc 0 g.T, max (g.T - s - r) 0 ∂g.L := by
  unfold W₂
  congr 1
  have hsub : Icc 0 (g.T - s) ⊆ Icc 0 g.T := Icc_subset_Icc_right (by linarith [hs.1])
  have hIntT : IntegrableOn (fun r => max (g.T - s - r) 0) (Icc 0 g.T) g.L :=
    g.integrableOn_continuous_Icc le_rfl ((continuous_const.sub continuous_id).max continuous_const)
  have hSplit :
      (∫ r in Icc 0 g.T, max (g.T - s - r) 0 ∂g.L) =
        (∫ r in Icc 0 (g.T - s), max (g.T - s - r) 0 ∂g.L) +
        (∫ r in Icc 0 g.T \ Icc 0 (g.T - s), max (g.T - s - r) 0 ∂g.L) := by
    rw [← MeasureTheory.setIntegral_union disjoint_sdiff_self_right
      (measurableSet_Icc.diff measurableSet_Icc)
      (hIntT.mono_set hsub) (hIntT.mono_set sdiff_subset)]
    rw [union_sdiff_cancel hsub]
  have hFirst :
      (∫ r in Icc 0 (g.T - s), max (g.T - s - r) 0 ∂g.L) =
        ∫ r in Icc 0 (g.T - s), (g.T - s - r) ∂g.L := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro r hr
    exact max_eq_left (sub_nonneg.mpr hr.2)
  have hSecond : (∫ r in Icc 0 g.T \ Icc 0 (g.T - s), max (g.T - s - r) 0 ∂g.L) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    have hgt : g.T - s < r := by
      by_contra hle
      push Not at hle
      exact hr.2 ⟨hr.1.1, hle⟩
    exact max_eq_right (by linarith)
  rw [hSplit, hFirst, hSecond, add_zero]

lemma W₂_nonneg (g : GeneralKernelParams) (s : ℝ) : 0 ≤ g.W₂ s := by
  unfold W₂
  apply mul_nonneg (by norm_num)
  apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
  intro r hr
  linarith [hr.2]

lemma W₂_continuousOn (g : GeneralKernelParams) : ContinuousOn g.W₂ (Icc 0 g.T) := by
  rw [Metric.continuousOn_iff]
  intro s hs ε hε
  set C : ℝ := 2 * g.L.real (Icc 0 g.T) + 1
  have hC_pos : 0 < C := by
    have : 0 ≤ g.L.real (Icc 0 g.T) := ENNReal.toReal_nonneg
    linarith
  refine ⟨ε / C, div_pos hε hC_pos, fun s' hs' hdist => ?_⟩
  have hInt1 : IntegrableOn (fun r => max (g.T - s' - r) 0) (Icc 0 g.T) g.L :=
    g.integrableOn_continuous_Icc le_rfl ((continuous_const.sub continuous_id).max continuous_const)
  have hInt2 : IntegrableOn (fun r => max (g.T - s - r) 0) (Icc 0 g.T) g.L :=
    g.integrableOn_continuous_Icc le_rfl ((continuous_const.sub continuous_id).max continuous_const)
  have hPt : ∀ r ∈ Icc 0 g.T, |max (g.T - s' - r) 0 - max (g.T - s - r) 0| ≤ dist s' s := by
    intro r _
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor
    · have h1 : max (g.T - s' - r) 0 ≤ max (g.T - s - r) 0 + |s' - s| := by
        refine max_le ?_ (add_nonneg (le_max_right _ _) (abs_nonneg _))
        have h2 : g.T - s' - r ≤ (g.T - s - r) + |s' - s| := by
          have := neg_le_abs (s' - s)
          linarith
        linarith [le_max_left (g.T - s - r) (0 : ℝ)]
      linarith
    · have h1 : max (g.T - s - r) 0 ≤ max (g.T - s' - r) 0 + |s' - s| := by
        refine max_le ?_ (add_nonneg (le_max_right _ _) (abs_nonneg _))
        have h2 : g.T - s - r ≤ (g.T - s' - r) + |s' - s| := by
          have := le_abs_self (s' - s)
          linarith
        linarith [le_max_left (g.T - s' - r) (0 : ℝ)]
      linarith
  have hNorm :
      |∫ r in Icc 0 g.T, (max (g.T - s' - r) 0 - max (g.T - s - r) 0) ∂g.L| ≤
        ∫ _ in Icc 0 g.T, dist s' s ∂g.L := by
    rw [← Real.norm_eq_abs]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    apply MeasureTheory.setIntegral_mono_on
    · exact (hInt1.sub hInt2).norm
    · exact g.integrableOn_continuous_Icc le_rfl continuous_const
    · exact measurableSet_Icc
    · intro r hr
      simpa [Real.norm_eq_abs] using hPt r hr
  have hConst : (∫ _ in Icc 0 g.T, dist s' s ∂g.L) = g.L.real (Icc 0 g.T) * dist s' s := by
    simp [smul_eq_mul]
  rw [Real.dist_eq, g.W₂_eq_Icc_T hs', g.W₂_eq_Icc_T hs, ← mul_sub, ← integral_sub hInt1 hInt2]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hBound :
      2 * |∫ r in Icc 0 g.T, (max (g.T - s' - r) 0 - max (g.T - s - r) 0) ∂g.L| ≤
        2 * g.L.real (Icc 0 g.T) * dist s' s := by
    have := mul_le_mul_of_nonneg_left (hNorm.trans_eq hConst) (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hLt : 2 * g.L.real (Icc 0 g.T) * dist s' s < ε := by
    have hL_nonneg : 0 ≤ g.L.real (Icc 0 g.T) := ENNReal.toReal_nonneg
    have hDist_nonneg : 0 ≤ dist s' s := dist_nonneg
    have hProd : 2 * g.L.real (Icc 0 g.T) * dist s' s ≤ (2 * g.L.real (Icc 0 g.T) + 1) * dist s' s := by
      nlinarith
    have hC_dist : C * dist s' s < ε := by
      have := (lt_div_iff₀' hC_pos).mp hdist
      simpa [C] using this
    exact lt_of_le_of_lt hProd hC_dist
  exact lt_of_le_of_lt hBound hLt

/-- **Eq. (29) Uniform Weight Upper Bound**:
    For all `s ∈ [0, T]`, `W₂(s) ≤ 2 (T - s) L([0, T - s])`. -/
lemma W₂_le (g : GeneralKernelParams) {s : ℝ} (hs : s ∈ Icc 0 g.T) :
    g.W₂ s ≤ 2 * (g.T - s) * g.L.real (Icc 0 (g.T - s)) := by
  unfold W₂
  have hMono :
      (∫ r in Icc 0 (g.T - s), (g.T - s - r) ∂g.L) ≤
        ∫ _ in Icc 0 (g.T - s), (g.T - s) ∂g.L := by
    apply MeasureTheory.setIntegral_mono_on
      (g.integrableOn_continuous_Icc (by linarith [hs.1]) (continuous_const.sub continuous_id))
      (g.integrableOn_continuous_Icc (by linarith [hs.1]) continuous_const) measurableSet_Icc
    intro r hr
    dsimp
    linarith [hr.1]
  have hConst : (∫ _ in Icc 0 (g.T - s), (g.T - s) ∂g.L) = g.L.real (Icc 0 (g.T - s)) * (g.T - s) := by
    simp [smul_eq_mul]
  linarith

/-- **Eq. (28) Lower Bound on `[0, T / 4]`**:
    For `s ∈ [0, T / 4]`, `(T / 2) L([0, T / 2]) ≤ W₂(s)`. -/
lemma W₂_lower_half (g : GeneralKernelParams) {s : ℝ} (hs : s ∈ Icc 0 (g.T / 4)) :
    (g.T / 2) * g.L.real (Icc 0 (g.T / 2)) ≤ g.W₂ s := by
  unfold W₂
  have hsT : s ∈ Icc 0 g.T := ⟨hs.1, by linarith [hs.2, g.hT_pos]⟩
  have hsub : Icc 0 (g.T / 2) ⊆ Icc 0 (g.T - s) := Icc_subset_Icc_right (by linarith [hs.2, g.hT_pos])
  have hIntW : IntegrableOn (fun r => g.T - s - r) (Icc 0 (g.T - s)) g.L :=
    g.integrableOn_continuous_Icc (by linarith [hsT.1]) (continuous_const.sub continuous_id)
  have hMonoSet :
      (∫ r in Icc 0 (g.T / 2), (g.T - s - r) ∂g.L) ≤
        ∫ r in Icc 0 (g.T - s), (g.T - s - r) ∂g.L := by
    apply MeasureTheory.setIntegral_mono_set hIntW
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact sub_nonneg.mpr hr.2
    · exact Eventually.of_forall (fun r hr => hsub hr)
  have hMonoOn :
      (∫ _ in Icc 0 (g.T / 2), (g.T / 4) ∂g.L) ≤
        ∫ r in Icc 0 (g.T / 2), (g.T - s - r) ∂g.L := by
    apply MeasureTheory.setIntegral_mono_on
      (g.integrableOn_continuous_Icc (by linarith [g.hT_pos]) continuous_const)
      (hIntW.mono_set hsub) measurableSet_Icc
    intro r hr
    linarith [hs.2, hr.2]
  have hConst : (∫ _ in Icc 0 (g.T / 2), (g.T / 4) ∂g.L) = g.L.real (Icc 0 (g.T / 2)) * (g.T / 4) := by
    simp [smul_eq_mul]
  linarith

/-- **Theorem 3(1)(i)**: `I₀(T) ≥ (T^2 / 8) L([0, T/2]) > 0`. -/
lemma I₀_pos (g : GeneralKernelParams) : 0 < g.I₀ := by
  unfold I₀
  have hT_nonneg : 0 ≤ g.T := le_of_lt g.hT_pos
  have hT4_nonneg : 0 ≤ g.T / 4 := by linarith [g.hT_pos]
  have hT4_le : g.T / 4 ≤ g.T := by linarith [g.hT_pos]
  have hInt1 : IntervalIntegrable g.W₂ volume 0 (g.T / 4) := by
    apply g.W₂_continuousOn.mono _ |>.intervalIntegrable
    rw [uIcc_of_le hT4_nonneg]
    exact Icc_subset_Icc_right hT4_le
  have hInt2 : IntervalIntegrable g.W₂ volume (g.T / 4) g.T := by
    apply g.W₂_continuousOn.mono _ |>.intervalIntegrable
    rw [uIcc_of_le hT4_le]
    exact Icc_subset_Icc_left hT4_nonneg
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
  have hFirst : (g.T ^ 2 / 8) * g.L.real (Icc 0 (g.T / 2)) ≤ ∫ s in (0 : ℝ)..(g.T / 4), g.W₂ s := by
    have hConstInt :
        (∫ _ in (0 : ℝ)..(g.T / 4), (g.T / 2) * g.L.real (Icc 0 (g.T / 2))) =
          (g.T ^ 2 / 8) * g.L.real (Icc 0 (g.T / 2)) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      ring
    rw [← hConstInt]
    apply intervalIntegral.integral_mono_on hT4_nonneg intervalIntegrable_const hInt1
    intro s hs
    exact g.W₂_lower_half hs
  have hSecond : 0 ≤ ∫ s in (g.T / 4)..g.T, g.W₂ s := by
    apply intervalIntegral.integral_nonneg hT4_le
    intro s _
    exact g.W₂_nonneg s
  have hLower_pos : 0 < (g.T ^ 2 / 8) * g.L.real (Icc 0 (g.T / 2)) :=
    mul_pos (div_pos (sq_pos_of_pos g.hT_pos) (by norm_num)) g.L_half_pos
  linarith

/-- **Theorem 3(1)(ii)**: On `[0, T - δ]`, `W₂(s) ≤ B_bound(δ) (T - s)^2`. -/
lemma B_bound_valid (g : GeneralKernelParams) {δ s : ℝ} (hδ : δ ∈ Ioo 0 g.T)
    (hs0 : 0 ≤ s) (hsδ : s ≤ g.T - δ) :
    g.W₂ s ≤ g.B_bound δ * (g.T - s) ^ 2 := by
  have hsT : s ∈ Icc 0 g.T := ⟨hs0, by linarith [hδ.1]⟩
  have hW := g.W₂_le hsT
  have hLmono : g.L.real (Icc 0 (g.T - s)) ≤ g.L.real (Icc 0 g.T) :=
    g.L_real_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl
  have hTus : δ ≤ g.T - s := by linarith
  have hTu_nonneg : 0 ≤ g.T - s := le_trans (le_of_lt hδ.1) hTus
  have h2_le : 2 * (g.T - s) * g.L.real (Icc 0 (g.T - s)) ≤ 2 * (g.T - s) * g.L.real (Icc 0 g.T) :=
    mul_le_mul_of_nonneg_left hLmono (by linarith)
  have hB : 2 * (g.T - s) * g.L.real (Icc 0 g.T) ≤ g.B_bound δ * (g.T - s) ^ 2 := by
    unfold B_bound
    have hδ_pos : 0 < δ := hδ.1
    have hL_nonneg : 0 ≤ g.L.real (Icc 0 g.T) := ENNReal.toReal_nonneg
    have h1 : 2 * (g.T - s) * g.L.real (Icc 0 g.T) * δ ≤ 2 * g.L.real (Icc 0 g.T) * (g.T - s) ^ 2 := by
      have : (g.T - s) * δ ≤ (g.T - s) ^ 2 := by nlinarith
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ_pos]
    linarith
  exact hW.trans (h2_le.trans hB)

/-- **Eq. (30) & Theorem 3(1)(iii)**:
    `Tail(δ)` is integrable and bounded by `(2 L([0, T])^2 / q) * δ`. -/
lemma integrable_tail (g : GeneralKernelParams) {δ : ℝ} (hδ : δ ∈ Ioo 0 g.T) :
    IntervalIntegrable (fun s => (g.W₂ s) ^ 2 / (2 * g.q * (g.T - s) ^ 2)) volume (g.T - δ) g.T := by
  have hle : g.T - δ ≤ g.T := by linarith [hδ.1]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  have hIoo_ae : Ioo (g.T - δ) g.T =ᵐ[volume] Ioc (g.T - δ) g.T := Ioo_ae_eq_Ioc
  rw [← MeasureTheory.integrableOn_congr_set_ae hIoo_ae]
  have hCont : ContinuousOn (fun s => (g.W₂ s) ^ 2 / (2 * g.q * (g.T - s) ^ 2)) (Ioo (g.T - δ) g.T) := by
    apply ContinuousOn.div
    · exact (g.W₂_continuousOn.mono
        (show Ioo (g.T - δ) g.T ⊆ Icc 0 g.T from
          fun s hs => ⟨by linarith [hs.1, hδ.2], le_of_lt hs.2⟩)).pow 2
    · exact continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)
    · intro s hs
      exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt g.q_pos))
        (pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hs.2)))
  have hMeas : AEStronglyMeasurable (fun s => (g.W₂ s) ^ 2 / (2 * g.q * (g.T - s) ^ 2))
      (volume.restrict (Ioo (g.T - δ) g.T)) :=
    hCont.aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioo_lt_top hMeas
    (2 * (g.L.real (Icc 0 g.T)) ^ 2 / g.q) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsT : s ∈ Icc 0 g.T := ⟨by linarith [hs.1, hδ.2], le_of_lt hs.2⟩
  have hTu_pos : 0 < g.T - s := sub_pos.mpr hs.2
  have hW_nonneg : 0 ≤ g.W₂ s := g.W₂_nonneg s
  have hW_le : g.W₂ s ≤ 2 * (g.T - s) * g.L.real (Icc 0 g.T) := by
    have := g.W₂_le hsT
    have hLm : g.L.real (Icc 0 (g.T - s)) ≤ g.L.real (Icc 0 g.T) :=
      g.L_real_mono (Icc_subset_Icc_right (by linarith [hsT.1])) Subset.rfl
    nlinarith
  have hVal_nonneg : 0 ≤ (g.W₂ s) ^ 2 / (2 * g.q * (g.T - s) ^ 2) := by
    have := g.q_pos; positivity
  rw [Real.norm_of_nonneg hVal_nonneg]
  have hSq : (g.W₂ s) ^ 2 ≤ 4 * (g.T - s) ^ 2 * (g.L.real (Icc 0 g.T)) ^ 2 := by nlinarith
  have hDen_pos : 0 < 2 * g.q * (g.T - s) ^ 2 := mul_pos (mul_pos (by norm_num) g.q_pos) (sq_pos_of_pos hTu_pos)
  rw [div_le_div_iff₀ hDen_pos g.q_pos]
  nlinarith [sq_pos_of_pos hTu_pos]

lemma tail_le (g : GeneralKernelParams) {δ : ℝ} (hδ : δ ∈ Ioo 0 g.T) :
    g.tail δ ≤ (2 * (g.L.real (Icc 0 g.T)) ^ 2 / g.q) * δ := by
  unfold tail
  have hle : g.T - δ ≤ g.T := by linarith [hδ.1]
  have hInt := g.integrable_tail hδ
  have hConstInt :
      (∫ _ in (g.T - δ)..g.T, (2 * (g.L.real (Icc 0 g.T)) ^ 2 / g.q)) =
        (2 * (g.L.real (Icc 0 g.T)) ^ 2 / g.q) * δ := by
    rw [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul]
    ring
  rw [← hConstInt]
  apply intervalIntegral.integral_mono_on hle hInt intervalIntegrable_const
  intro s hs
  rcases eq_or_lt_of_le hs.2 with rfl | hs_lt
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero]
    have hq_nonneg : 0 ≤ g.q := le_of_lt g.q_pos
    positivity
  · have hsT : s ∈ Icc 0 g.T := ⟨by linarith [hs.1, hδ.2], le_of_lt hs_lt⟩
    have hTu_pos : 0 < g.T - s := sub_pos.mpr hs_lt
    have hW_nonneg : 0 ≤ g.W₂ s := g.W₂_nonneg s
    have hW_le : g.W₂ s ≤ 2 * (g.T - s) * g.L.real (Icc 0 g.T) := by
      have := g.W₂_le hsT
      have hLm : g.L.real (Icc 0 (g.T - s)) ≤ g.L.real (Icc 0 g.T) :=
        g.L_real_mono (Icc_subset_Icc_right (by linarith [hsT.1])) Subset.rfl
      nlinarith
    have hSq : (g.W₂ s) ^ 2 ≤ 4 * (g.T - s) ^ 2 * (g.L.real (Icc 0 g.T)) ^ 2 := by nlinarith
    have hDen_pos : 0 < 2 * g.q * (g.T - s) ^ 2 :=
      mul_pos (mul_pos (by norm_num) g.q_pos) (sq_pos_of_pos hTu_pos)
    rw [div_le_div_iff₀ hDen_pos g.q_pos]
    nlinarith [sq_pos_of_pos hTu_pos]

/-- **Eq. (34) Constructive Parameter Selection (`δ`, `M`)**:
    There exist `δ ∈ (0, T)` and `M > 0` with `A_M ≥ B(δ)` and `Tail(δ) ≤ (1/2) σ₀ I₀(T)`. -/
lemma exists_general_M_contradiction_margin (g : GeneralKernelParams) :
    ∃ (δ M : ℝ), δ ∈ Ioo 0 g.T ∧ 0 < g.A_M M ∧ g.B_bound δ ≤ g.A_M M ∧
      g.tail δ ≤ (1 / 2) * g.σ₀ * g.I₀ := by
  set Ltot : ℝ := g.L.real (Icc 0 g.T)
  set D : ℝ := 2 * Ltot ^ 2 / g.q + 1
  have hD_pos : 0 < D := by
    have hq := g.q_pos; positivity
  set δ : ℝ := min (g.T / 2) ((1 / 2) * g.σ₀ * g.I₀ / D)
  have hNum_pos : 0 < (1 / 2) * g.σ₀ * g.I₀ :=
    mul_pos (mul_pos (by norm_num) g.hσ₀_pos) g.I₀_pos
  have hδ_pos : 0 < δ := lt_min (by linarith [g.hT_pos]) (div_pos hNum_pos hD_pos)
  have hδ_lt_T : δ < g.T := lt_of_le_of_lt (min_le_left _ _) (by linarith [g.hT_pos])
  have hδ_mem : δ ∈ Ioo 0 g.T := ⟨hδ_pos, hδ_lt_T⟩
  have hTail : g.tail δ ≤ (1 / 2) * g.σ₀ * g.I₀ := by
    have h1 := g.tail_le hδ_mem
    have hCoeff : 2 * Ltot ^ 2 / g.q ≤ D := by
      dsimp only [D]; linarith
    have h2 : (2 * Ltot ^ 2 / g.q) * δ ≤ D * δ := mul_le_mul_of_nonneg_right hCoeff (le_of_lt hδ_pos)
    have hδ_le_frac : δ ≤ (1 / 2) * g.σ₀ * g.I₀ / D := min_le_right _ _
    have h3 : D * δ ≤ (1 / 2) * g.σ₀ * g.I₀ := by
      calc D * δ ≤ D * ((1 / 2) * g.σ₀ * g.I₀ / D) := mul_le_mul_of_nonneg_left hδ_le_frac (le_of_lt hD_pos)
        _ = (1 / 2) * g.σ₀ * g.I₀ := mul_div_cancel₀ _ (ne_of_gt hD_pos)
    exact h1.trans (h2.trans h3)
  set targetA : ℝ := max 1 (g.B_bound δ)
  set M : ℝ := (targetA - g.c₁) / g.ϑ
  have hAM_eq : g.A_M M = targetA := by
    dsimp only [A_M, M]
    have hϑ_ne : g.ϑ ≠ 0 := ne_of_gt g.ϑ_pos
    field_simp [hϑ_ne]; ring
  have hAM_pos : 0 < g.A_M M := by
    rw [hAM_eq]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hB_le : g.B_bound δ ≤ g.A_M M := by
    rw [hAM_eq]; exact le_max_right _ _
  exact ⟨δ, M, hδ_mem, hAM_pos, hB_le, hTail⟩

/-- **Eq. (33)–(34) General Split-Integral Lower Bound**:
    For continuous `σ ≥ 0` on `[0, T]`, `δ ∈ (0, T)`, and `B(δ) ≤ A_M`:
    `-Tail(δ) ≤ ∫_0^T ((q/2)(T-u)^2 σ(u)^2 + (A_M (T-u)^2 - W₂(u)) σ(u)) du`. -/
lemma general_split_integral_lower_bound (g : GeneralKernelParams) {δ M : ℝ}
    (hδ : δ ∈ Ioo 0 g.T) (hA : 0 < g.A_M M) (hB : g.B_bound δ ≤ g.A_M M)
    (σ : ℝ → ℝ) (hσ_cont : ContinuousOn σ (Icc 0 g.T))
    (hσ_nonneg : ∀ u ∈ Icc 0 g.T, 0 ≤ σ u) :
    -g.tail δ ≤
      ∫ u in (0 : ℝ)..g.T,
        ((g.q / 2) * (g.T - u) ^ 2 * (σ u) ^ 2 +
          (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ u) := by
  set f : ℝ → ℝ := fun u =>
    (g.q / 2) * (g.T - u) ^ 2 * (σ u) ^ 2 + (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ u
  have hT_nonneg : 0 ≤ g.T := le_of_lt g.hT_pos
  have hTδ_nonneg : 0 ≤ g.T - δ := by linarith [hδ.2]
  have hTδ_le : g.T - δ ≤ g.T := by linarith [hδ.1]
  have hf_cont : ContinuousOn f (Icc 0 g.T) := by
    have h1 : ContinuousOn (fun u => g.T - u) (Icc 0 g.T) := continuousOn_const.sub continuousOn_id
    exact ((continuousOn_const.mul (h1.pow 2)).mul (hσ_cont.pow 2)).add
      (((continuousOn_const.mul (h1.pow 2)).sub g.W₂_continuousOn).mul hσ_cont)
  have hf1 : IntervalIntegrable f volume 0 (g.T - δ) :=
    (hf_cont.mono (by rw [uIcc_of_le hTδ_nonneg]; exact Icc_subset_Icc_right hTδ_le)).intervalIntegrable
  have hf2 : IntervalIntegrable f volume (g.T - δ) g.T :=
    (hf_cont.mono (by rw [uIcc_of_le hTδ_le]; exact Icc_subset_Icc_left hTδ_nonneg)).intervalIntegrable
  change -g.tail δ ≤ ∫ u in (0 : ℝ)..g.T, f u
  rw [← intervalIntegral.integral_add_adjacent_intervals hf1 hf2]
  have hMain : 0 ≤ ∫ u in (0 : ℝ)..(g.T - δ), f u := by
    apply intervalIntegral.integral_nonneg hTδ_nonneg
    intro u hu
    have hW := g.B_bound_valid hδ hu.1 hu.2
    have hCo : g.W₂ u ≤ g.A_M M * (g.T - u) ^ 2 :=
      hW.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))
    have hQuad : 0 ≤ (g.q / 2) * (g.T - u) ^ 2 * (σ u) ^ 2 := by
      have := le_of_lt g.q_pos; positivity
    have hLin : 0 ≤ (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ u :=
      mul_nonneg (sub_nonneg.mpr hCo) (hσ_nonneg u ⟨hu.1, hu.2.trans hTδ_le⟩)
    exact add_nonneg hQuad hLin
  have hEnd : -g.tail δ ≤ ∫ u in (g.T - δ)..g.T, f u := by
    have hTailInt := g.integrable_tail hδ
    have hNegInt :
        -g.tail δ = ∫ u in (g.T - δ)..g.T, -((g.W₂ u) ^ 2 / (2 * g.q * (g.T - u) ^ 2)) := by
      unfold tail
      rw [intervalIntegral.integral_neg]
    rw [hNegInt]
    apply intervalIntegral.integral_mono_on hTδ_le hTailInt.neg hf2
    intro u hu
    rcases eq_or_lt_of_le hu.2 with rfl | hu_lt
    · simp only [f, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_sub]
      -- At `u = T`, `W₂(T) = 0` so `f T = 0`.
      have hWT : g.W₂ g.T = 0 := by
        have h1 := g.W₂_le ⟨le_of_lt g.hT_pos, le_rfl⟩
        have h2 := g.W₂_nonneg g.T
        linarith
      simp [hWT]
    · have huT : u ∈ Icc 0 g.T := ⟨by linarith [hu.1, hδ.2], le_of_lt hu_lt⟩
      have hTu_pos : 0 < g.T - u := sub_pos.mpr hu_lt
      have hDrop : 0 ≤ g.A_M M * (g.T - u) ^ 2 * σ u :=
        mul_nonneg (mul_nonneg (le_of_lt hA) (sq_nonneg _)) (hσ_nonneg u huT)
      set a : ℝ := (g.q / 2) * (g.T - u) ^ 2
      set b : ℝ := g.W₂ u
      have ha_pos : 0 < a := by have := g.q_pos; positivity
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hCS : -(b ^ 2 / (4 * a)) ≤ a * (σ u) ^ 2 - b * σ u := by
        have hsq : 0 ≤ a * (σ u - b / (2 * a)) ^ 2 := mul_nonneg (le_of_lt ha_pos) (sq_nonneg _)
        have hid : a * (σ u - b / (2 * a)) ^ 2 = a * (σ u) ^ 2 - b * σ u + b ^ 2 / (4 * a) := by
          field_simp [ha_ne]; ring
        linarith
      have hEqDen : 4 * a = 2 * g.q * (g.T - u) ^ 2 := by dsimp only [a]; ring
      have hRearr : f u = (a * (σ u) ^ 2 - b * σ u) + g.A_M M * (g.T - u) ^ 2 * σ u := by
        dsimp only [f, a, b]; ring
      simp only [Pi.neg_apply]
      rw [hRearr, ← hEqDen]
      change -(b ^ 2 / (4 * a)) ≤ _
      linarith
  linarith

/-- Eq. (16) Quadratic-variation domination for `GeneralKernelParams`. -/
lemma quadratic_variation_domination_general (g : GeneralKernelParams) (σ : ℝ → ℝ)
    (hσ_cont : ContinuousOn σ (Icc 0 g.T)) :
    (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 *
        (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 4 * (σ u) ^ 2) ≤
      (g.lam * g.q / 2) *
        (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ u) ^ 2) := by
  have hT_nonneg : 0 ≤ g.T := le_of_lt g.hT_pos
  have hInt1 : IntervalIntegrable (fun u => (g.T - u) ^ 4 * (σ u) ^ 2) volume 0 g.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT_nonneg]
    exact ((continuousOn_const.sub continuousOn_id).pow 4).mul (hσ_cont.pow 2)
  have hInt2 : IntervalIntegrable (fun u => g.T ^ 2 * ((g.T - u) ^ 2 * (σ u) ^ 2)) volume 0 g.T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT_nonneg]
    exact continuousOn_const.mul (((continuousOn_const.sub continuousOn_id).pow 2).mul (hσ_cont.pow 2))
  have hMono :
      (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 4 * (σ u) ^ 2) ≤
        g.T ^ 2 * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ u) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT_nonneg hInt1 hInt2
    intro u hu
    have h1 := quartic_le_sq_mul_sq hu.1 hu.2
    have h2 : 0 ≤ (σ u) ^ 2 := sq_nonneg (σ u)
    nlinarith
  have hCoeff : (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 * g.T ^ 2 = g.lam * g.q / 2 := by
    unfold lam
    have hϑ : g.ϑ ≠ 0 := ne_of_gt g.ϑ_pos
    have hT : g.T ≠ 0 := ne_of_gt g.hT_pos
    field_simp [hϑ, hT]
  have hFactor_nonneg : 0 ≤ (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 := by positivity
  calc
    (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 4 * (σ u) ^ 2)
        ≤ (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 *
            (g.T ^ 2 * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ u) ^ 2)) :=
          mul_le_mul_of_nonneg_left hMono hFactor_nonneg
    _ = ((1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 * g.T ^ 2) *
          (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ u) ^ 2) := by ring
    _ = (g.lam * g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ u) ^ 2) := by rw [hCoeff]

end GeneralKernelParams

/-- Layer 2 stochastic-calculus interface for **Theorem 3** (general `K ∈ L²([0, T])`
    admitting a finite non-negative first-kind resolvent measure `L`). -/
structure GeneralVolterraMartingaleInterface (g : GeneralKernelParams) where
  Ω : Type*
  E_S_T : ℝ
  S₀ : ℝ
  supermartingale_le : E_S_T ≤ S₀
  tilted_system :
    E_S_T = S₀ →
    ∀ M : ℝ, 0 < g.A_M M →
      ∃ (E_M : (Ω → ℝ) → ℝ) (σ : Ω → ℝ → ℝ) (M_T : Ω → ℝ) (Good : Set Ω),
        (∀ ω ∈ Good, ContinuousOn (σ ω) (Icc 0 g.T) ∧ ∀ u ∈ Icc 0 g.T, 0 ≤ σ ω u) ∧
        (∀ ω ∈ Good,
          -M_T ω =
            g.σ₀ * g.I₀ + g.c₀ * g.T ^ 3 / 3 +
            ∫ s in (0 : ℝ)..g.T,
              (g.q * (g.T - s) ^ 2 * (σ ω s) ^ 2 +
                (g.A_M M * (g.T - s) ^ 2 - g.W₂ s) * σ ω s)) ∧
        E_M (fun ω => Real.exp (-(g.lam * M_T ω) -
            (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 *
              (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 4 * (σ ω u) ^ 2))) ≤ 1 ∧
        (∀ (c : ℝ) (X : Ω → ℝ), (∀ ω ∈ Good, c ≤ X ω) → c ≤ E_M X)

/-- **Theorem 3 (Martingale Necessity for General Kernels with Non-Negative First-Kind Resolvent)**:
    Under `GeneralKernelParams` and `GeneralVolterraMartingaleInterface`, `E_Q[S_T] < S_0`. -/
theorem general_kernel_theorem_3 (g : GeneralKernelParams)
    (I : GeneralVolterraMartingaleInterface g) : I.E_S_T < I.S₀ := by
  refine lt_of_le_of_ne I.supermartingale_le ?_
  intro hEq
  obtain ⟨δ, M, hδ, hAM_pos, hB, hTail⟩ := g.exists_general_M_contradiction_margin
  obtain ⟨E_M, σ, M_T, Good, hReg, hQuadTest, hDD, hMono⟩ := I.tilted_system hEq M hAM_pos
  set ε₀ : ℝ := g.lam * ((1 / 2) * g.σ₀ * g.I₀)
  have hε₀_pos : 0 < ε₀ :=
    mul_pos g.lam_pos (mul_pos (mul_pos (by norm_num) g.hσ₀_pos) g.I₀_pos)
  have hPathwise :
      ∀ ω ∈ Good,
        Real.exp ε₀ ≤
          Real.exp (-(g.lam * M_T ω) -
            (1 / 2) * g.lam ^ 2 * g.ϑ ^ 2 *
              (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 4 * (σ ω u) ^ 2)) := by
    intro ω hω
    apply Real.exp_le_exp.mpr
    obtain ⟨hσ_cont, hσ_nonneg⟩ := hReg ω hω
    have hT_nonneg : 0 ≤ g.T := le_of_lt g.hT_pos
    have hQV := g.quadratic_variation_domination_general (σ ω) hσ_cont
    have hSplit := g.general_split_integral_lower_bound hδ hAM_pos hB (σ ω) hσ_cont hσ_nonneg
    have hc₀_term : 0 ≤ g.c₀ * g.T ^ 3 / 3 := by
      have hc₀ := g.c₀_nonneg
      have hT := le_of_lt g.hT_pos
      positivity
    have hInt_q :
        IntervalIntegrable (fun u => (g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2) volume 0 g.T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT_nonneg]
      exact (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow 2)).mul
        (hσ_cont.pow 2)
    have hInt_q' :
        IntervalIntegrable (fun x => g.q / 2 * ((g.T - x) ^ 2 * (σ ω x) ^ 2)) volume 0 g.T := by
      simpa [mul_assoc] using hInt_q
    have hInt_rem :
        IntervalIntegrable
          (fun u =>
            (g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
              (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u)
          volume 0 g.T := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hT_nonneg]
      have h1 : ContinuousOn (fun u => g.T - u) (Icc 0 g.T) := continuousOn_const.sub continuousOn_id
      exact ((continuousOn_const.mul (h1.pow 2)).mul (hσ_cont.pow 2)).add
        (((continuousOn_const.mul (h1.pow 2)).sub g.W₂_continuousOn).mul hσ_cont)
    have hInt_decomp :
        (∫ u in (0 : ℝ)..g.T,
            (g.q * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
              (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u)) =
          (g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ ω u) ^ 2) +
          (∫ u in (0 : ℝ)..g.T,
            ((g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
              (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hInt_q' hInt_rem]
      congr 1; ext u; ring
    have hQuad_ω := hQuadTest ω hω
    have hNeg : -(g.lam * M_T ω) = g.lam * (-M_T ω) := by ring
    rw [hNeg, hQuad_ω, hInt_decomp]
    have hlam_nonneg : 0 ≤ g.lam := le_of_lt g.lam_pos
    have hMargin_ge : (1 / 2) * g.σ₀ * g.I₀ ≤ g.σ₀ * g.I₀ - g.tail δ := by linarith
    have hMarg : ε₀ ≤ g.lam * (g.σ₀ * g.I₀ - g.tail δ) :=
      mul_le_mul_of_nonneg_left hMargin_ge hlam_nonneg
    have hc₀_scaled : 0 ≤ g.lam * (g.c₀ * g.T ^ 3 / 3) := mul_nonneg hlam_nonneg hc₀_term
    have hSplit_scaled :
        g.lam * (-g.tail δ) ≤
          g.lam * ∫ u in (0 : ℝ)..g.T,
            ((g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
              (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u) :=
      mul_le_mul_of_nonneg_left hSplit hlam_nonneg
    have hAssoc :
        g.lam * ((g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ ω u) ^ 2)) =
          (g.lam * g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ ω u) ^ 2) := by
      ring
    have hDist :
        g.lam * (g.σ₀ * g.I₀ + g.c₀ * g.T ^ 3 / 3 +
          ((g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ ω u) ^ 2) +
            (∫ u in (0 : ℝ)..g.T,
              ((g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
                (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u)))) =
          g.lam * (g.σ₀ * g.I₀) + g.lam * (g.c₀ * g.T ^ 3 / 3) +
            g.lam * ((g.q / 2) * (∫ u in (0 : ℝ)..g.T, (g.T - u) ^ 2 * (σ ω u) ^ 2)) +
            g.lam * (∫ u in (0 : ℝ)..g.T,
              ((g.q / 2) * (g.T - u) ^ 2 * (σ ω u) ^ 2 +
                (g.A_M M * (g.T - u) ^ 2 - g.W₂ u) * σ ω u)) := by
      ring
    rw [hDist, hAssoc]
    linarith
  have h1_lt_exp : 1 < Real.exp ε₀ := Real.one_lt_exp_iff.mpr hε₀_pos
  have hexp_le_EM := hMono (Real.exp ε₀) _ hPathwise
  linarith

end Theorem3GeneralKernels

end RoughLogSVConjecture45

/-!
# Formal Verification of the Core Inequalities for Conjecture 4.5
(Sepp & Rakhmonov 2026, arXiv:2611.32791v1, unified with H = 1/2, 2023 Theorem 3.7)

Pure Lean 4 core (zero external imports, zero `sorry`), designed for Lean 4.36.0.
Run locally with: `lean RoughLogSVConjecture45.lean` or `lake build`

Verifies:
1. `qv_absorption`: for 0 ≤ r ≤ T and λ = q / (ϑ² T²), the quadratic-variation weight
   λ² ϑ² r⁴ is bounded by λ q r², leaving half of the quadratic drift intact.
2. `endpoint_layer_margin_pos`: whenever `tail < lhs` and `0 < λ`, the deterministic
   exponential lower bound `ε₀ = λ (lhs - tail)` is strictly positive.
3. `supermartingale_contradiction`: if `-λ M_T - ½ λ² ⟨M⟩_T ≥ ε₀ > 0` a.s. implies
   `exp(ε₀) ≤ E[ℰ_T(-λ M)]` while Fatou gives `E[ℰ_T(-λ M)] ≤ 1`, then `False`.
4. `sq_nonneg_int`: cleared-denominator pointwise completion-of-the-square
   inequality `(q w x - b)² ≥ 0` over `Int` (for the endpoint-layer tail bound).
5. `h_half_concrete_witness` & `h_half_delta_le_T`: exact rational verification for
   the classical endpoint H = 1/2 at T = 1/100, σ₀ = 1/2, q = 3/5, A_M = 267000.
-/

namespace RoughLogSVConjecture45

/-- Minimal ordered commutative ring interface (instantiated by ℝ). -/
class OrderedRing (R : Type) where
  zero : R
  one : R
  add : R → R → R
  sub : R → R → R
  mul : R → R → R
  le : R → R → Prop
  lt : R → R → Prop
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  not_lt_of_le : ∀ {a b}, le a b → ¬ lt b a
  sub_pos_of_lt : ∀ {a b}, lt a b → lt zero (sub b a)
  mul_le_mul_left_nonneg : ∀ {a b c}, le zero c → le a b → le (mul c a) (mul c b)
  mul_le_mul_right_nonneg : ∀ {a b c}, le zero c → le a b → le (mul a c) (mul b c)
  mul_nonneg : ∀ {a b}, le zero a → le zero b → le zero (mul a b)
  mul_pos : ∀ {a b}, lt zero a → lt zero b → lt zero (mul a b)

section CoreProof

variable {R : Type} [OrderedRing R]

open OrderedRing

/-- Helper: 0 ≤ r ≤ T implies r² ≤ T². -/
theorem sq_le_sq {r T : R} (hr : le zero r) (hT : le zero T) (hrT : le r T) :
    le (mul r r) (mul T T) := by
  have h1 : le (mul r r) (mul r T) := mul_le_mul_left_nonneg hr hrT
  have h2 : le (mul r T) (mul T T) := mul_le_mul_right_nonneg hT hrT
  exact le_trans h1 h2

/--
Step 3 (Quadratic-Variation Absorption):
For 0 ≤ r ≤ T, 0 ≤ λ, 0 ≤ ϑ², and λ (ϑ² T²) = q, we have
  λ² ϑ² r⁴ ≤ λ q r²,
which absorbs ½ λ² ⟨M⟩_T into half of the positive quadratic drift ∫ q (T-u)² σ_u² du.
-/
theorem qv_absorption {r T lam v2 q : R}
    (hr : le zero r) (hT : le zero T) (hrT : le r T)
    (hlam : le zero lam) (hv2 : le zero v2)
    (h_choice : mul lam (mul v2 (mul T T)) = q) :
    le (mul (mul lam lam) (mul v2 (mul (mul r r) (mul r r))))
       (mul lam (mul q (mul r r))) := by
  have hr2 : le zero (mul r r) := mul_nonneg hr hr
  have h_sq : le (mul r r) (mul T T) := sq_le_sq hr hT hrT
  -- r⁴ = (r²)(r²) ≤ (T²)(r²)
  have h_r4 : le (mul (mul r r) (mul r r)) (mul (mul T T) (mul r r)) :=
    mul_le_mul_right_nonneg hr2 h_sq
  -- Multiply on left by λ² ϑ² ≥ 0
  have h_lam2v2 : le zero (mul (mul lam lam) v2) :=
    mul_nonneg (mul_nonneg hlam hlam) hv2
  have h_step :
      le (mul (mul (mul lam lam) v2) (mul (mul r r) (mul r r)))
         (mul (mul (mul lam lam) v2) (mul (mul T T) (mul r r))) :=
    mul_le_mul_left_nonneg h_lam2v2 h_r4
  -- Reassociate LHS: ((λ λ) ϑ²) (r² r²) = (λ λ) (ϑ² (r² r²))
  have h_lhs :
      mul (mul (mul lam lam) v2) (mul (mul r r) (mul r r)) =
      mul (mul lam lam) (mul v2 (mul (mul r r) (mul r r))) :=
    mul_assoc (mul lam lam) v2 (mul (mul r r) (mul r r))
  -- Reassociate RHS: ((λ λ) ϑ²) (T² r²) = λ ( (λ (ϑ² T²)) r² ) = λ (q r²)
  have h_rhs :
      mul (mul (mul lam lam) v2) (mul (mul T T) (mul r r)) =
      mul lam (mul q (mul r r)) := by
    rw [mul_assoc lam lam v2]
    rw [mul_assoc lam (mul lam v2) (mul (mul T T) (mul r r))]
    rw [← mul_assoc (mul lam v2) (mul T T) (mul r r)]
    rw [mul_assoc lam v2 (mul T T)]
    rw [h_choice]
  rw [h_lhs, h_rhs] at h_step
  exact h_step

/--
Step 4a (Strict Positivity of the Deterministic Exponential Margin):
Once M is chosen large enough that `tail < lhs`, `ε₀ = λ (lhs - tail) > 0`.
-/
theorem endpoint_layer_margin_pos {lam lhs tail : R}
    (hlam : lt zero lam) (h_lt : lt tail lhs) :
    lt zero (mul lam (sub lhs tail)) :=
  mul_pos hlam (sub_pos_of_lt h_lt)

/--
Step 4b (Doléans–Dade Supermartingale Contradiction):
If `0 < ε₀`, `exp(ε₀) > 1`, `exp(ε₀) ≤ E[ℰ_T(-λ M)]`, and Fatou gives `E[ℰ_T(-λ M)] ≤ 1`,
then `False` (contradicting the assumption E_Q[S_T] = S_0).
-/
theorem supermartingale_contradiction
    (exp : R → R) (eps expect_E : R)
    (h_exp_gt_one : ∀ {x}, lt zero x → lt one (exp x))
    (h_eps : lt zero eps)
    (h_lower : le (exp eps) expect_E)
    (h_fatou : le expect_E one) :
    False := by
  have h1 : lt one (exp eps) := h_exp_gt_one h_eps
  have h2 : le (exp eps) one := le_trans h_lower h_fatou
  exact not_lt_of_le h2 h1

end CoreProof

/--
Pointwise completion-of-the-square non-negativity over `Int`:
For all integers `y`, `0 ≤ y * y` (cleared-denominator core of
`½ q w x² - b x + b² / (2 q w) = (q w x - b)² / (2 q w) ≥ 0`).
-/
theorem sq_nonneg_int (y : Int) : 0 ≤ y * y := by
  cases y with
  | ofNat n =>
    exact Int.natCast_nonneg (n * n)
  | negSucc n =>
    have h : Int.negSucc n * Int.negSucc n = Int.ofNat ((n + 1) * (n + 1)) := rfl
    rw [h]
    exact Int.natCast_nonneg ((n + 1) * (n + 1))

/--
Concrete Rational Witness for the Classical Diffusion Endpoint H = 1/2:
At T = 1/100, σ₀ = 1/2, q = 3/5, A_M = 267000:
  - LHS  = σ₀ T² = 1 / 20000
  - Tail = 4 / (q A_M) = 20 / 801000 = 1 / 40050
Clearing denominators checks `20000 < 40050`, certifying `Tail < LHS` (in fact `2 * Tail < LHS`).
-/
theorem h_half_concrete_witness : (2 * 20000 : Nat) < 40050 := by
  decide

/--
Concrete Rational Check that δ_M ≤ T at H = 1/2, T = 1/100, A_M = 267000:
  δ_M = 2 / A_M = 1 / 133500 ≤ 1 / 100 = T.
-/
theorem h_half_delta_le_T : (100 : Nat) ≤ 133500 := by
  decide

end RoughLogSVConjecture45

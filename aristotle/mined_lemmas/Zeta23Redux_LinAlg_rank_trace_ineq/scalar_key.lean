import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix
open scoped ComplexOrder

variable {d : ℕ}

/-! ## Basic real-valued trace functionals -/

/-- The real part of the trace. -/

lemma scalar_key (p w : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    {k : ℕ} (hk : (Finset.univ.filter (fun i => p i ≠ 0)).card ≤ k) {c : ℝ} (hc : 0 ≤ c) :
    c * (∑ i, p i) - (c ^ 2 / 4) * k + 2 * (∑ i, p i * w i)
      ≤ (∑ i, (p i) ^ 2) + (∑ i, (w i) ^ 2) + c * (∑ i, w i) := by
  have key : ∀ i ∈ Finset.univ, c * p i + 2 * (p i * w i) - ((p i) ^ 2 + (w i) ^ 2 + c * w i)
      ≤ (if p i ≠ 0 then c ^ 2 / 4 else 0) := by
    intro i _
    by_cases h : p i = 0
    · simp only [h, ne_eq, not_true_eq_false, ite_false]
      nlinarith [hw i, sq_nonneg (w i)]
    · rw [if_pos h]
      nlinarith [sq_nonneg (w i - p i + c / 2)]
  have hsum := Finset.sum_le_sum key
  have h2 : ∑ i : Fin d, (if p i ≠ 0 then c ^ 2 / 4 else 0)
      = (c ^ 2 / 4) * (Finset.univ.filter (fun i => p i ≠ 0)).card := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp [mul_comm]
  have h3 : (c ^ 2 / 4) * ((Finset.univ.filter (fun i => p i ≠ 0)).card : ℝ) ≤ (c ^ 2 / 4) * k := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast hk
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [h2] at hsum
  linarith

/-! ## The key matrix estimate -/

/-- If `P = U diag m Uᴴ` is positive semidefinite with at most `k` nonzero eigenvalues and `N` is
positive semidefinite, then the linear part of `P` is controlled by the Frobenius norms, with an
interaction term `2 tr (P N)` on the left. -/

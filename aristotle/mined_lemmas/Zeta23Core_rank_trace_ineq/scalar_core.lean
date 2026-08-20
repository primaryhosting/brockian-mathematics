/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

lemma scalar_core {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ) (S U : Finset ι)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i ∉ S, q i ≤ 0) (hpz : ∀ i, i ∉ S → i ∉ U → p i = 0)
    {c : ℝ} (hc : 0 ≤ c) {r b : ℕ} (hS : S.card ≤ b) (hU : U.card ≤ r) :
    c * (∑ i, p i) - c ^ 2 / 4 * r + 2 * c * (∑ i, q i) - c ^ 2 * b
      ≤ ∑ i, (p i + q i) ^ 2 := by
  classical
  set w : ι → ℝ := fun i => (if i ∈ S then c ^ 2 else 0) + (if i ∈ U then c ^ 2 / 4 else 0)
    with hw
  have hwnn : ∀ i, 0 ≤ w i := by
    intro i
    simp only [hw]
    have h1 : (0:ℝ) ≤ if i ∈ S then c ^ 2 else 0 := by split <;> positivity
    have h2 : (0:ℝ) ≤ if i ∈ U then c ^ 2 / 4 else 0 := by split <;> positivity
    positivity
  have key : ∀ i, 2 * c * (p i + q i) - c * p i - w i ≤ (p i + q i) ^ 2 := by
    intro i
    by_cases hiS : i ∈ S
    · have h1 : (c ^ 2 : ℝ) ≤ w i := by
        simp only [hw, if_pos hiS]
        have : (0:ℝ) ≤ if i ∈ U then c ^ 2 / 4 else 0 := by split <;> positivity
        linarith
      nlinarith [sq_nonneg (p i + q i - c), hp i, mul_nonneg hc (hp i)]
    · have hqi : q i ≤ 0 := hq i hiS
      by_cases hiU : i ∈ U
      · have h1 : (c ^ 2 / 4 : ℝ) ≤ w i := by
          simp only [hw, if_neg hiS, if_pos hiU]; norm_num
        nlinarith [sq_nonneg (p i + q i - c / 2), mul_nonneg hc (neg_nonneg.mpr hqi)]
      · have hpi : p i = 0 := hpz i hiS hiU
        have h0 : 0 ≤ w i := hwnn i
        rw [hpi]
        nlinarith [sq_nonneg (q i), mul_nonneg hc (neg_nonneg.mpr hqi)]
  have hsum : ∑ i, w i ≤ c ^ 2 * b + c ^ 2 / 4 * r := by
    have e1 : ∑ i, (if i ∈ S then c ^ 2 else 0) = c ^ 2 * S.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
    have e2 : ∑ i, (if i ∈ U then c ^ 2 / 4 else 0) = c ^ 2 / 4 * U.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]; ring
    have e3 : ∑ i, w i = c ^ 2 * S.card + c ^ 2 / 4 * U.card := by
      simp only [hw, Finset.sum_add_distrib, e1, e2]
    rw [e3]
    have h1 : (S.card : ℝ) ≤ b := by exact_mod_cast hS
    have h2 : (U.card : ℝ) ≤ r := by exact_mod_cast hU
    have h3 : c ^ 2 * (S.card : ℝ) ≤ c ^ 2 * b := by nlinarith [sq_nonneg c]
    have h4 : c ^ 2 / 4 * (U.card : ℝ) ≤ c ^ 2 / 4 * r := by nlinarith [sq_nonneg c]
    linarith
  have step : ∑ i, (2 * c * (p i + q i) - c * p i - w i) ≤ ∑ i, (p i + q i) ^ 2 :=
    Finset.sum_le_sum fun i _ => key i
  have expand : ∑ i, (2 * c * (p i + q i) - c * p i - w i)
      = c * (∑ i, p i) + 2 * c * (∑ i, q i) - ∑ i, w i := by
    have h : ∀ i, 2 * c * (p i + q i) - c * p i - w i = c * p i + 2 * c * q i - w i := by
      intro i; ring
    simp_rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [expand] at step
  linarith

/-! ### Existence of an adapted orthonormal basis -/

/-- The span of the eigenvectors of a Hermitian matrix belonging to its positive eigenvalues. -/

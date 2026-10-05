/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

/-! ### Arithmetic in `ZMod 2` -/


lemma hat_eq_zero_imp {k : ℕ} (f : Cube k → ℝ) (h : ∀ s, hat f s = 0) : f = 0 := by
  classical
  funext x
  simp only [Pi.zero_apply]
  have key : ∑ s : Cube k, hat f s * chi s x = (2 ^ k : ℝ) * f x := by
    have h1 : ∑ s : Cube k, hat f s * chi s x
        = ∑ s : Cube k, ∑ y : Cube k, f y * chi s (y + x) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hat, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by rw [mul_assoc, chi_mul]
    have h3 : ∀ y : Cube k, (y + x = 0) ↔ y = x := by
      intro y
      constructor
      · intro hy
        funext i
        have hyi := congrFun hy i
        simp only [Pi.add_apply, Pi.zero_apply] at hyi
        exact (zmod2_add_eq_zero (y i) (x i)).mp hyi
      · rintro rfl
        funext i
        simp only [Pi.add_apply, Pi.zero_apply]
        exact (zmod2_add_eq_zero _ _).mpr rfl
    have h2 : ∀ y : Cube k, ∑ s : Cube k, f y * chi s (y + x)
        = if y = x then f y * (2 ^ k : ℝ) else 0 := by
      intro y
      rw [← Finset.mul_sum, sum_chi]
      simp only [h3 y]
      by_cases hy : y = x <;> simp [hy]
    rw [h1, Finset.sum_comm, Finset.sum_congr rfl (fun y _ => h2 y),
      Finset.sum_ite_eq' Finset.univ x (fun y => f y * (2 ^ k : ℝ))]
    simp only [Finset.mem_univ, if_true]
    ring
  simp only [h, zero_mul, Finset.sum_const_zero] at key
  have h2 : (2 : ℝ) ^ k ≠ 0 := by positivity
  rcases mul_eq_zero.mp key.symm with h' | h'
  · exact absurd h' h2
  · exact h'

/-! ### The spectral gap -/

/-- Every nonzero eigenvalue of the hypercube Laplacian is at least `2`. -/

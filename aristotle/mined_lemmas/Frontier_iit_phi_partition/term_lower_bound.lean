/-
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a global state `x` to the part `A` of the system. -/

lemma term_lower_bound {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  rcases eq_or_lt_of_le hp with h | h
  · simp [← h]
    linarith
  · have hq' : 0 < q := hpq h
    have hlog : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hinv : Real.log (p / q) = - Real.log (q / p) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    have h1 : 1 - q / p ≤ Real.log (p / q) := by rw [hinv]; linarith
    have h2 : p * (1 - q / p) ≤ p * Real.log (p / q) := by nlinarith
    have h3 : p * (1 - q / p) = p - q := by field_simp
    linarith


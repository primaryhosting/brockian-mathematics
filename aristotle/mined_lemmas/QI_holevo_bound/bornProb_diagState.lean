import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma bornProb_diagState (E : Matrix n n ℂ) (r : n → ℝ) :
    bornProb E (diagState r) = ∑ z, r z * (E z z).re := by
  rw [bornProb, diagState]
  have : (E * Matrix.diagonal (fun z => (r z : ℂ))).trace = ∑ z, E z z * (r z : ℂ) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal]
  rw [this, Complex.re_sum]
  exact Finset.sum_congr rfl (fun z _ => by simp [Complex.mul_re]; ring)

/-- Mutual information (in nats) between the label `i` (with prior `p`) and the measurement
outcome `y`, where `q i y` is the conditional probability of outcome `y` given label `i`.
Maximising this over measurements gives the accessible information. -/

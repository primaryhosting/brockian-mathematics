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

lemma vonNeumannEntropy_diagState (r : n → ℝ) :
    vonNeumannEntropy (diagState r) = shannonEntropy r := by
  rw [vonNeumannEntropy, dif_pos (diagState_isHermitian r), shannonEntropy]
  exact sum_eigenvalues_diagState r Real.negMulLog (diagState_isHermitian r)

/-- Born rule: the probability of outcome `E` on the state `ρ`. -/

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

lemma vonNeumannEntropy_commutingState (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (r : n → ℝ) :
    vonNeumannEntropy (commutingState U r) = shannonEntropy r := by
  have hH : (commutingState U r).IsHermitian := commutingState_isHermitian U r
  have hD : (diagState r).IsHermitian := diagState_isHermitian r
  have hev : hH.eigenvalues = hD.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hA := hH) (hB := hD)).2
      (charpoly_conj_unitary U (diagState r) hU)
  rw [vonNeumannEntropy, dif_pos hH, hev, shannonEntropy]
  exact sum_eigenvalues_diagState r Real.negMulLog hD


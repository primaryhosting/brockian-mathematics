import Mathlib

/-!
# Pbr Theorem
Category: Frontier Qi
Target: QI.pbr_theorem
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

open Complex Finset

/-! ## The two-qubit vectors used in the PBR argument -/

/-- The normalisation constant `1/√2`. -/

private lemma expand (u v : Vec4) :
    ip u v = (starRingEnd ℂ) (u (0, 0)) * v (0, 0) + (starRingEnd ℂ) (u (0, 1)) * v (0, 1)
      + ((starRingEnd ℂ) (u (1, 0)) * v (1, 0) + (starRingEnd ℂ) (u (1, 1)) * v (1, 1)) := by
  simp [ip, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Each of the four PBR basis vectors is orthogonal to the corresponding product
preparation: the outcome `i` never occurs on the preparation `badPair i`. -/

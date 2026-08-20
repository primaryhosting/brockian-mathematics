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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Functional calculus for a Hermitian matrix: `hermFun hρ f` is the matrix obtained by
applying the real function `f` to the eigenvalues of `ρ`, in an eigenbasis of `ρ`. -/

lemma vonNeumannEntropy_eq {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) :
    vonNeumannEntropy hρ = -∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
  rw [vonNeumannEntropy, mulLog, trace_hermFun]
  norm_num

/-- Applying the identity function to the eigenvalues recovers the matrix itself
(spectral theorem). -/

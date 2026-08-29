/-!
# Bell Orthonormal
Category: Quantum Computing
Target: QC.bell_orthonormal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

/-- A single qubit space: `ℂ²` with its standard (Euclidean) inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`, with the tensor-product inner product. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis kets `|0⟩` and `|1⟩` of a single qubit. -/

lemma inner_smul_l (x y : TwoQubit) (c : ℂ) :
    inner ℂ (c • x) y = (starRingEnd ℂ) c * inner ℂ x y := inner_smul_left x y c


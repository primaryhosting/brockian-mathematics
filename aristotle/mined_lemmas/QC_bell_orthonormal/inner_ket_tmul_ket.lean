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

lemma inner_ket_tmul_ket (a b c d : Fin 2) :
    inner ℂ (ket a ⊗ₜ[ℂ] ket b) (ket c ⊗ₜ[ℂ] ket d)
      = (if a = c then 1 else 0) * (if b = d then 1 else 0) := by
  rw [TensorProduct.inner_tmul]
  simp [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/- Scalar multiplication on `ℂ² ⊗ ℂ²` reaches the inner product through a different
(definitionally equal) instance path, so we restate the two `inner`/`smul` lemmas here. -/

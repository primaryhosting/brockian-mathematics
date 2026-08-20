import Mathlib
/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The state space of four qubits: the Hilbert space `ℂ^(2×2×2×2)`, whose
computational basis is indexed by bit strings `(b₀, b₁, b₂, b₃)`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2 × Fin 2)

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`. -/
noncomputable def ghz4 : Qubits4 :=
  WithLp.toLp 2 fun i =>
    if i = (0, 0, 0, 0) ∨ i = (1, 1, 1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0

/-- `ghz4` is indeed `(1/√2) • (|0000⟩ + |1111⟩)`, expressed via the standard
orthonormal (computational) basis of the 4-qubit space. -/
theorem ghz4_eq_smul_add_basis :
    ghz4 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single (0, 0, 0, 0) (1 : ℂ)
        + EuclideanSpace.single (1, 1, 1, 1) (1 : ℂ)) := by
  ext i
  by_cases h0 : i = (0, 0, 0, 0)
  · subst h0; simp [ghz4, EuclideanSpace.single_apply]
  · by_cases h1 : i = (1, 1, 1, 1)
    · subst h1; simp [ghz4, EuclideanSpace.single_apply, h0]
    · simp [ghz4, EuclideanSpace.single_apply, h0, h1]

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz4, Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num

end QC


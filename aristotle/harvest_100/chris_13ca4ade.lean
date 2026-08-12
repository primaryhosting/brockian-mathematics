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

/-!
# The 3-qubit GHZ state is a unit vector

We model the state space of three qubits as the finite-dimensional complex Hilbert
space `EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)`, whose standard basis vectors
`ket (b₀, b₁, b₂)` are the computational basis states `|b₀ b₁ b₂⟩`.

The GHZ state is `(|000⟩ + |111⟩) / √2`, and we show that it has norm `1`.
-/

namespace QC

/-- The Hilbert space of three qubits, with the computational basis indexed by
bit-triples. -/
abbrev Q3 : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The computational basis state `|b₀ b₁ b₂⟩`. -/
noncomputable def ket (b : Fin 2 × Fin 2 × Fin 2) : Q3 := EuclideanSpace.single b (1 : ℂ)

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩) / √2`. -/
noncomputable def ghz3 : Q3 := ((1 : ℂ) / Real.sqrt 2) • (ket (0, 0, 0) + ket (1, 1, 1))

/-- The coordinates of the GHZ state: `1/√2` at `|000⟩` and `|111⟩`, and `0` elsewhere. -/
theorem ghz3_apply (b : Fin 2 × Fin 2 × Fin 2) :
    ghz3 b = if b = (0, 0, 0) ∨ b = (1, 1, 1) then ((1 : ℂ) / Real.sqrt 2) else 0 := by
  simp only [ghz3, ket, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply, smul_eq_mul]
  by_cases h1 : b = (0, 0, 0) <;> by_cases h2 : b = (1, 1, 1) <;> simp_all

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [ghz3_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QC


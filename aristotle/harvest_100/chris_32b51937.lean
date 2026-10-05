import Mathlib

/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
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

/-- The state space of three qubits: `ℂ^(2×2×2)` with the Euclidean (Hermitian) norm. -/
abbrev Qubits3 := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The computational basis ket `|v⟩` for a bit-triple `v`. -/
noncomputable def ket (v : Fin 2 × Fin 2 × Fin 2) : Qubits3 := EuclideanSpace.single v 1

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz3 : Qubits3 := ((Real.sqrt 2)⁻¹ : ℂ) • (ket (0, 0, 0) + ket (1, 1, 1))

/-- Coordinates of the GHZ state: `1/√2` at `|000⟩` and `|111⟩`, zero elsewhere. -/
lemma ghz3_apply (v : Fin 2 × Fin 2 × Fin 2) :
    ghz3 v =
      if v = (0, 0, 0) then ((Real.sqrt 2)⁻¹ : ℂ)
      else if v = (1, 1, 1) then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  simp only [ghz3, ket, PiLp.smul_apply, PiLp.add_apply, EuclideanSpace.single_apply,
    smul_eq_mul]
  split_ifs with h1 h2 <;> simp_all

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [ghz3_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num [Complex.norm_real, Real.sq_sqrt, abs_of_nonneg, Real.sqrt_nonneg]

end QC


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

namespace QC

/-- The state space of three qubits: `ℂ^(2×2×2)` with the Euclidean (ℓ²) inner product. -/
abbrev Qubit3 : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz3 : Qubit3 :=
  ((1 : ℂ) / (Real.sqrt 2 : ℂ)) •
    (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
      + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) (1 : ℂ))

/-- The amplitude of `|000⟩` in the GHZ state is `1/√2`. -/
theorem ghz3_apply_zero : ghz3 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) = 1 / (Real.sqrt 2 : ℂ) := by
  simp [ghz3, EuclideanSpace.single_apply]

/-- The amplitude of `|111⟩` in the GHZ state is `1/√2`. -/
theorem ghz3_apply_one : ghz3 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) = 1 / (Real.sqrt 2 : ℂ) := by
  simp [ghz3, EuclideanSpace.single_apply]

/-- All other amplitudes of the GHZ state vanish. -/
theorem ghz3_apply_eq_zero (i : Fin 2 × Fin 2 × Fin 2)
    (h0 : i ≠ (0, 0, 0)) (h1 : i ≠ (1, 1, 1)) : ghz3 i = 0 := by
  simp [ghz3, EuclideanSpace.single_apply, if_neg h0, if_neg h1]

/-- The 3-qubit GHZ state is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz3, EuclideanSpace.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Prod.ext_iff]
  norm_num

end QC


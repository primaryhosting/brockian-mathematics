/-
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

/-- The state space of three qubits: the Hilbert space `ℂ^(2×2×2)`, with the
standard (Euclidean) inner product.  A basis vector `|b₀b₁b₂⟩` corresponds to the
index `(b₀, b₁, b₂) : Fin 2 × Fin 2 × Fin 2`. -/
abbrev ThreeQubit : Type := EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, given by its amplitudes. -/
noncomputable def ghz3 : ThreeQubit :=
  WithLp.toLp 2 fun i =>
    if i = (0, 0, 0) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if i = (1, 1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0

/-- The definition of `ghz3` by amplitudes agrees with the usual description
`(|000⟩ + |111⟩)/√2` as a combination of computational basis vectors. -/
theorem ghz3_eq_smul_add_single :
    ghz3 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
        + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) := by
  ext i
  by_cases h0 : i = (0, 0, 0)
  · subst h0; simp [ghz3, EuclideanSpace.single_apply]
  · by_cases h1 : i = (1, 1, 1)
    · subst h1; simp [ghz3, EuclideanSpace.single_apply]
    · simp [ghz3, EuclideanSpace.single_apply, h0, h1]

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2` is a unit vector. -/
theorem ghz3_normalized : ‖ghz3‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz3, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QC


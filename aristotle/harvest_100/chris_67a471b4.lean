/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
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

/-- The state space of two qubits: `ℂ^(Fin 2 × Fin 2)` with the Euclidean (ℓ²) norm.
Basis states are indexed by pairs `(a, b)` of bits, representing `|ab⟩`. -/
abbrev TwoQubit : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`. -/
noncomputable def ghz2 : TwoQubit :=
  WithLp.toLp 2 (fun q : Fin 2 × Fin 2 =>
    if q = (0, 0) ∨ q = (1, 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The defining formula: `ghz2 = (1/√2) • (|00⟩ + |11⟩)`, where `|ab⟩` is the standard
basis vector `EuclideanSpace.single (a, b) 1`. -/
theorem ghz2_eq_smul_add_single :
    ghz2 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
        + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) := by
  ext q
  fin_cases q <;> simp [ghz2, EuclideanSpace.single_apply, Prod.ext_iff]

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ q : Fin 2 × Fin 2, ‖ghz2 q‖ ^ 2) = 1 := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ghz2, WithLp.ofLp_toLp]
    norm_num [Complex.norm_real, abs_of_pos hpos, div_pow, h2]
  rw [hsum, Real.sqrt_one]

end QC


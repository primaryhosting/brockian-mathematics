/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module docstrings (`/-! ... -/`).  The header therefore appears twice: as a plain
-- block comment at the very top of the file, and as the module docstring below the
-- import.  The text is otherwise identical.

namespace QC

/-- The all-zeros basis label `|000000⟩` of a 6-qubit register. -/
def allZeros : Fin 6 → Bool := fun _ => false

/-- The all-ones basis label `|111111⟩` of a 6-qubit register. -/
def allOnes : Fin 6 → Bool := fun _ => true

theorem allZeros_ne_allOnes : allZeros ≠ allOnes := by
  intro h
  have := congrFun h 0
  simp [allZeros, allOnes] at this

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
`2^6`-dimensional complex Hilbert space indexed by bit strings `Fin 6 → Bool`. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Bool) :=
  WithLp.toLp 2 (fun x =>
    if x = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if x = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0)

/-- `ghz6` is indeed the superposition `(1/√2) • (|0…0⟩ + |1…1⟩)` of the two
computational basis vectors `|000000⟩` and `|111111⟩`. -/
theorem ghz6_eq_smul_add_single :
    ghz6 = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
      (EuclideanSpace.single allZeros (1 : ℂ) + EuclideanSpace.single allOnes (1 : ℂ)) := by
  have hne := allZeros_ne_allOnes
  ext x
  simp only [ghz6, WithLp.ofLp_toLp, PiLp.smul_apply, PiLp.add_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases h0 : x = allZeros
  · subst h0; simp [hne]
  · by_cases h1 : x = allOnes
    · subst h1; simp [hne.symm]
    · simp [h0, h1]

/-- The 6-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hne := allZeros_ne_allOnes
  have hterm : ∀ x : (Fin 6 → Bool), ‖ghz6.ofLp x‖ ^ 2
      = (if x = allZeros then (1/2 : ℝ) else 0) + (if x = allOnes then (1/2 : ℝ) else 0) := by
    intro x
    simp only [ghz6, WithLp.ofLp_toLp]
    by_cases h0 : x = allZeros
    · simp [h0, hne]
    · by_cases h1 : x = allOnes
      · simp [h1, hne.symm]
      · simp [h0, h1]
  rw [EuclideanSpace.norm_eq]
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  norm_num

/-- Equivalent phrasing: the GHZ state lies on the unit sphere. -/
theorem ghz6_mem_sphere : ghz6 ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 6 → Bool)) 1 := by
  simpa [mem_sphere_iff_norm] using ghz6_normalized

end QC

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


import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The computational basis of a 6-qubit register: bit strings of length 6. -/
abbrev Bits6 := Fin 6 → Bool

/-- The all-zeros bit string, labelling the basis vector `|000000⟩`. -/
def allZero : Bits6 := fun _ => false

/-- The all-ones bit string, labelling the basis vector `|111111⟩`. -/
def allOne : Bits6 := fun _ => true

theorem allZero_ne_allOne : allZero ≠ allOne := by
  intro h
  have := congrFun h 0
  simp [allZero, allOne] at this

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^6)` whose coordinates are indexed by bit strings of length 6. -/
noncomputable def ghz6 : EuclideanSpace ℂ Bits6 :=
  WithLp.toLp 2 (fun b => if b = allZero then ((1 / Real.sqrt 2 : ℝ) : ℂ) else
                          if b = allOne then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 6-qubit GHZ state is a unit vector.

The key Mathlib ingredient is `EuclideanSpace.norm_eq`, which reduces the norm to
`√(∑ b, ‖ghz6 b‖ ^ 2)`; the sum has exactly two nonzero terms, each equal to `1/2`. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hne : allZero ≠ allOne := allZero_ne_allOne
  rw [EuclideanSpace.norm_eq]
  have hpt : ∀ b : Bits6, ‖ghz6.ofLp b‖ ^ 2
      = (if b = allZero then (1 / 2 : ℝ) else 0)
        + (if b = allOne then (1 / 2 : ℝ) else 0) := by
    intro b
    by_cases h0 : b = allZero
    · subst h0
      simp [ghz6, hne]
    · by_cases h1 : b = allOne
      · subst h1
        simp [ghz6, h0]
      · simp [ghz6, h0, h1]
  simp only [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ allZero (fun _ => (1 / 2 : ℝ)),
    Finset.sum_ite_eq' Finset.univ allOne (fun _ => (1 / 2 : ℝ))]
  norm_num

#print axioms QC.ghz6_normalized

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


/-
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hardy Paradox
Category: Frontier Qi
Target: QI.hardy_paradox
Statement: Hardy's nonlocality argument: a fraction of runs violate local realism without inequalities.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Finset

namespace QI

universe u

/-! ## Two-qubit kinematics

A two-qubit pure state is an array of amplitudes `psi : Fin 2 → Fin 2 → ℂ`, and a local
measurement outcome on each side is described by a unit vector in `ℂ²`.  The Born rule gives
the joint probability of the pair of outcomes `(u, v)` as `|⟪u ⊗ v, psi⟫|²`.
-/

/-- The amplitude `⟪u ⊗ v, psi⟫` of the product vector `u ⊗ v` in the two-qubit state `psi`. -/

theorem lhv_hardy_zero {Λ : Type u} [MeasurableSpace Λ] (μ : Measure Λ)
    (A0 A1 B0 B1 : Set Λ)
    (h1 : μ (A0 ∩ B1ᶜ) = 0) (h2 : μ (A1ᶜ ∩ B0) = 0) (h3 : μ (A1 ∩ B1) = 0) :
    μ (A0 ∩ B0) = 0 := by
  have hsub : A0 ∩ B0 ⊆ (A0 ∩ B1ᶜ) ∪ ((A1ᶜ ∩ B0) ∪ (A1 ∩ B1)) := by
    rintro x ⟨hA0, hB0⟩
    by_cases hB1 : x ∈ B1
    · by_cases hA1 : x ∈ A1
      · exact Or.inr (Or.inr ⟨hA1, hB1⟩)
      · exact Or.inr (Or.inl ⟨hA1, hB0⟩)
    · exact Or.inl ⟨hA0, hB1⟩
  refine measure_mono_null hsub ?_
  simp [h1, h2, h3, measure_union_null]

/-! ## Hardy's paradox -/

/-- **Hardy's paradox.**

* The first conjunct is the quantum-mechanical side: there is a genuine two-qubit state
  (Hardy's state) and genuine measurements — a unit vector `a0` for Alice's setting `0`, an
  orthonormal pair `a1, a1'` for her setting `1`, and likewise `b0`, `b1`, `b1'` for Bob —
  such that three joint outcome probabilities vanish (`+−` for `(0,1)`, `−+` for `(1,0)` and
  `++` for `(1,1)`) while the joint outcome `++` for the settings `(0,0)` occurs in a fraction
  `1/12 > 0` of the runs.

* The second conjunct is the local-realist side: no local hidden-variable model can reproduce
  these numbers.  Indeed the three vanishing probabilities force, run by run and without any
  inequality, the probability of the `++` event for the settings `(0,0)` to be exactly `0`,
  contradicting the quantum value `1/12`.

Hence a nonzero fraction of the runs witnesses the failure of local realism. -/

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

lemma v1_orthogonal : inner2 v1 v1' = 0 := by
  simp [inner2, v1, v1', Fin.sum_univ_two, star_c2]


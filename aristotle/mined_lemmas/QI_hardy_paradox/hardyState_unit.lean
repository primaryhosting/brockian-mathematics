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

lemma hardyState_unit : IsUnitState hardyState := by
  simp only [IsUnitState, hardyState, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show ((-3 : ℂ) * c12) = ((-3 : ℝ) : ℂ) * c12 by norm_num]
  rw [Complex.normSq_mul]
  simp [normSq_c12]
  norm_num

/-- Hardy's first zero: outcome `+` for Alice's setting 0 never occurs together with
outcome `−` for Bob's setting 1. -/

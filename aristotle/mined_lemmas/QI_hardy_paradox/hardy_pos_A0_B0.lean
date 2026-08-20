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

lemma hardy_pos_A0_B0 : prob v0 v0 hardyState = 1 / 12 := by
  have : amp v0 v0 hardyState = c12 := by
    simp [amp, v0, hardyState, Fin.sum_univ_two]
  rw [prob, this, normSq_c12]

/-! ## The local hidden-variable no-go

In a local hidden-variable model, each run is described by a hidden state `x : Λ` which already
determines the outcome of every measurement.  `A0` (resp. `A1`) is the set of hidden states for
which Alice's setting 0 (resp. 1) yields the outcome `+`, and similarly for Bob; the complement
of such a set is the event that the outcome is `−`.  Probabilities of joint events are then
computed from a single measure `μ` on `Λ`.
-/

/-- **Hardy's argument, run by run.**  In a deterministic local hidden-variable model, where
`A i x = true` means that Alice's setting `i` yields the outcome `+` on the run with hidden state
`x` (and similarly for Bob), the three Hardy constraints are incompatible, on *every* run, with
both first settings yielding `+`.  No inequality is involved. -/

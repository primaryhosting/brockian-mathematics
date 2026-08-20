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

theorem lhv_hardy_pointwise {Λ : Type u} (A B : Fin 2 → Λ → Bool)
    (h1 : ∀ x, A 0 x = true → B 1 x = true)
    (h2 : ∀ x, B 0 x = true → A 1 x = true)
    (h3 : ∀ x, ¬(A 1 x = true ∧ B 1 x = true)) :
    ∀ x, ¬(A 0 x = true ∧ B 0 x = true) := by
  rintro x ⟨hA0, hB0⟩
  exact h3 x ⟨h2 x hB0, h1 x hA0⟩

/-- **The local realist prediction.**  If a local hidden-variable model reproduces Hardy's three
vanishing probabilities, then in that model the event "both first settings give `+`" has
probability zero. -/

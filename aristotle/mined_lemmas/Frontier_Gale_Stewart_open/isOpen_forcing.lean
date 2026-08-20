/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GaleStewart

universe u

variable {X : Type u}

/-- The list of the first `n` moves of the play `a`. -/

lemma isOpen_forcing [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsOpen A) {a : ℕ → X}
    (ha : a ∈ A) : ∃ n, ∀ b : ℕ → X, (∀ i < n, b i = a i) → b ∈ A := by
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hA a ha
  refine ⟨I.sup id + 1, fun b hb => hsub ?_⟩
  intro i hi
  have hile : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [hb i (by omega)]
  exact (hu i hi).2

section Strategies

/-- A play `a` follows the strategy `σ` for player I (who moves at even times). -/

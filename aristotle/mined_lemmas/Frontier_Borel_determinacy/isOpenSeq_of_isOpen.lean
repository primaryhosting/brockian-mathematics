/-
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above repeats verbatim as a module docstring below; Lean 4 does not allow a
-- module docstring to precede the `import` commands.)

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u

/-! ## Infinite two-player games on sequences -/

/-- A strategy is a map from the finite history of moves played so far to the next move. -/

lemma isOpenSeq_of_isOpen {S : Set (ℕ → A)} (hS : IsOpen S) : IsOpenSeq S := by
  intro x hx
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hS x hx
  refine ⟨I.sup id + 1, fun y hy => ?_⟩
  refine hsub fun i hi => ?_
  have hi' : i ∈ I := by simpa using hi
  have hlt : i < I.sup id + 1 := by
    have := Finset.le_sup (f := id) hi'
    simp only [id_eq] at this
    omega
  have : y i = x i := (hist_eq_iff y x _).mp hy i hlt
  rw [this]
  exact (hu i hi').2

/-- The basic cylinder consisting of all sequences agreeing with `x` on the first `n` coordinates
is open. -/

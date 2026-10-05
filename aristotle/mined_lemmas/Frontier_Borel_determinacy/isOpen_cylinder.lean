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

lemma isOpen_cylinder (x : ℕ → A) (n : ℕ) : IsOpen {y : ℕ → A | hist y n = hist x n} := by
  have hset : {y : ℕ → A | hist y n = hist x n}
      = ⋂ i ∈ Finset.range n, (fun y : ℕ → A => y i) ⁻¹' {x i} := by
    ext y
    simp [hist_eq_iff]
  rw [hset]
  exact isOpen_biInter_finset fun i _ =>
    (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)


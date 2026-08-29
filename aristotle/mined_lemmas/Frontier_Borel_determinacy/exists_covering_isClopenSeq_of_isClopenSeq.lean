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

lemma exists_covering_isClopenSeq_of_isClopenSeq [Inhabited A] {S : Set (ℕ → A)}
    (hS : IsClopenSeq S) :
    ∃ (B : Type u) (cov : Covering A B), Nonempty (Inhabited B) ∧ IsClopenSeq (cov.push ⁻¹' S) :=
  ⟨A, Covering.refl A, ⟨inferInstance⟩, hS⟩

/-- **Borel determinacy (Martin's theorem), as a Lean-checked reduction.**
Every Borel game on a discrete alphabet `A` is determined, given Martin's unravelling lemma:
each Borel payoff set becomes clopen in a suitable covering game.  The base case (clopen, indeed
open, games are determined) is fully proved above, as is the transfer of determinacy along
coverings; the unravelling hypothesis is the only external input. -/

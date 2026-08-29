/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/

theorem len_lt_len_of_lt {s t : Node} (h : s < t) : s.len < t.len := by
  rcases lt_or_eq_of_le h.le.1 with h' | h'
  · exact h'
  · exact absurd (le_antisymm h.le ⟨h'.ge, fun ξ hξ => (h.le.2 ξ (h' ▸ hξ)).symm⟩) h.ne

/-- Each node is a finite-to-one function on its domain. -/

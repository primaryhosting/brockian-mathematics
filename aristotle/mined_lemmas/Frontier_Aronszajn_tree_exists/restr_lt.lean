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

theorem restr_lt (s : Node) (β : Ordinal) (h : β < s.len) : s.restr β h < s := by
  refine lt_of_le_of_ne ⟨h.le, fun ξ hξ => if_pos hξ⟩ (fun hEq => ?_)
  exact absurd (congrArg Node.len hEq) h.ne

/-- The canonical node of length `α`. -/

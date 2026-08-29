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

theorem E_limit {l : Ordinal} (hl : Order.IsSuccLimit l) (ξ : Ordinal) :
    E l ξ = if ξ < l then max (E (cseq l (idx l ξ + 1)) ξ) (idx l ξ) else 0 := by
  unfold E
  rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-! ## Basic properties of `idx` -/


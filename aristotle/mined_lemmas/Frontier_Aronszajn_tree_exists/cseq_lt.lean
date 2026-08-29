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

theorem cseq_lt {l : Ordinal} (hl : Order.IsSuccLimit l) (n : ℕ) : cseq l n < l := by
  unfold cseq
  split
  · rename_i h
    exact h.choose_spec.2.2.1 n
  · exact hl.bot_lt

/-! ## The coherent family `E` -/

/-- Index of the block of `cseq l` containing `ξ`. -/

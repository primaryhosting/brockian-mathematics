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

theorem eq_of_dev_eq {s t : Node} (hlen : s.len = t.len) (hdev : dev s = dev t) : s = t := by
  refine Node.ext hlen (funext fun ξ => ?_)
  rcases lt_or_ge ξ s.len with h | h
  · rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h2 | h2
    · rcases eq_or_ne (t.fn ξ) (E t.len ξ) with h3 | h3
      · rw [h2, h3, hlen]
      · exact dev_key hdev.ge (hlen ▸ h) h3
    · exact (dev_key hdev.le h h2).symm
  · rw [s.fn_zero ξ h, t.fn_zero ξ (hlen ▸ h)]


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

theorem chainFn_eq {C : Set Node} (hC : IsChain (· ≤ ·) C) {s : Node} (hs : s ∈ C) {ξ : Ordinal}
    (hξ : ξ < s.len) : chainFn C ξ = s.fn ξ := by
  classical
  have h : ∃ t : Node, t ∈ C ∧ ξ < t.len := ⟨s, hs, hξ⟩
  rw [chainFn, dif_pos h]
  obtain ⟨hmem, hlt⟩ := h.choose_spec
  rcases eq_or_ne h.choose s with heq | hne
  · rw [heq]
  · rcases hC hmem hs hne with hle | hle
    · exact hle.2 ξ hlt
    · exact (hle.2 ξ hξ).symm


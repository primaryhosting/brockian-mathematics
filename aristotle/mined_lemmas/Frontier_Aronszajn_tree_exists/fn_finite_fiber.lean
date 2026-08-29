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

theorem fn_finite_fiber (s : Node) (n : ℕ) : {ξ : Ordinal | ξ < s.len ∧ s.fn ξ = n}.Finite := by
  apply Set.Finite.subset (s.fn_coh.union ((E_main s.len s.len_lt).1 n))
  rintro ξ ⟨h1, h2⟩
  rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h | h
  · right; exact ⟨h1, by rw [← h, h2]⟩
  · left; exact ⟨h1, h⟩

/-- Restriction of a node to a smaller length. -/

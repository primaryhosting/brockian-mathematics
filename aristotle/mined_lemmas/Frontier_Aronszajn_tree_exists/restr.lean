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

noncomputable def restr (s : Node) (β : Ordinal) (h : β < s.len) : Node where
  len := β
  fn := fun ξ => if ξ < β then s.fn ξ else 0
  len_lt := lt_trans h s.len_lt
  fn_zero := fun ξ hξ => if_neg (not_lt.mpr hξ)
  fn_coh := by
    apply Set.Finite.subset (s.fn_coh.union ((E_main s.len s.len_lt).2 β h))
    rintro ξ ⟨h1, h2⟩
    rw [if_pos h1] at h2
    rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h' | h'
    · right; exact ⟨h1, by rw [← h']; exact h2⟩
    · left; exact ⟨lt_trans h1 h, h'⟩


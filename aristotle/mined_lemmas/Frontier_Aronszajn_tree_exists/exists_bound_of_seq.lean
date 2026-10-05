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

theorem exists_bound_of_seq (f : ℕ → Ordinal) (hf : ∀ n, f n < ω₁) : ∃ α < ω₁, ∀ n, f n < α := by
  have h1 : iSup f < ω₁ := by
    have := Ordinal.iSup_sequence_lt_omega_one f (by simpa [ord_aleph] using hf)
    simpa [ord_aleph] using this
  exact ⟨iSup f + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt h1,
    fun n => lt_of_le_of_lt (Ordinal.le_iSup f n) (lt_add_one _)⟩

/-! ## The tree of nodes -/

/-- A node of the tree: a function `fn : Ordinal → ℕ` which is supported on `Set.Iio len`
(for some countable ordinal `len`) and differs from `E len` only on a finite set. -/
@[ext]
structure Node where
  /-- The length (level) of the node. -/
  len : Ordinal.{0}
  /-- The underlying function, extended by `0` past `len`. -/
  fn : Ordinal.{0} → ℕ
  len_lt : len < ω₁
  fn_zero : ∀ ξ, len ≤ ξ → fn ξ = 0
  fn_coh : {ξ : Ordinal | ξ < len ∧ fn ξ ≠ E len ξ}.Finite

namespace Node

instance : PartialOrder Node where
  le s t := s.len ≤ t.len ∧ ∀ ξ < s.len, s.fn ξ = t.fn ξ
  le_refl s := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans s t u h1 h2 := ⟨h1.1.trans h2.1, fun ξ hξ =>
    (h1.2 ξ hξ).trans (h2.2 ξ (lt_of_lt_of_le hξ h1.1))⟩
  le_antisymm s t h1 h2 := by
    have hlen : s.len = t.len := le_antisymm h1.1 h2.1
    refine Node.ext hlen (funext fun ξ => ?_)
    rcases lt_or_ge ξ s.len with h | h
    · exact h1.2 ξ h
    · rw [s.fn_zero ξ h, t.fn_zero ξ (hlen ▸ h)]


import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem pathLang_mono {S T : Finset σ} (h : S ⊆ T) (i j : σ) :
    pathLang M S i j ≤ pathLang M T i j := by
  rintro w ⟨hw, hint⟩
  exact ⟨hw, fun u v huv hu hv => h (hint u v huv hu hv)⟩

/-- Concatenating two paths through an allowed intermediate state `k`. -/

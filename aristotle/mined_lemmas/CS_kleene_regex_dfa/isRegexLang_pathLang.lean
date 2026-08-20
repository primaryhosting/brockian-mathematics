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

theorem isRegexLang_pathLang [Fintype α] [DecidableEq σ] (S : Finset σ) (i j : σ) :
    IsRegexLang (pathLang M S i j) := by
  induction S using Finset.induction generalizing i j with
  | empty =>
    rw [pathLang_empty]
    refine IsRegexLang.add ?_ (IsRegexLang.sum _ _ fun a _ => IsRegexLang.char a)
    by_cases h : i = j
    · rw [if_pos h]; exact IsRegexLang.one
    · rw [if_neg h]; exact IsRegexLang.zero
  | insert k S hk ih =>
    rw [pathLang_insert]
    exact (ih i j).add ((ih i k).mul (((ih k k).kstar).mul (ih k j)))


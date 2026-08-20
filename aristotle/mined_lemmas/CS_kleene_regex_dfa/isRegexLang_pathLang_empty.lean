import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-! ## Part 1: the language of a regular expression is accepted by a finite DFA

We use the Myhill–Nerode theorem: it suffices to show that a regular expression has only
finitely many left quotients (Brzozowski derivatives, viewed as languages). -/

section RegexToDFA

variable {α : Type u}


theorem isRegexLang_pathLang_empty (p q : σ) : IsRegexLang (pathLang M (∅ : Finset σ) p q) := by
  rw [pathLang_empty]
  refine IsRegexLang.add ?_ (IsRegexLang.finsetSup _ _ fun a _ => IsRegexLang.char a)
  by_cases h : p = q
  · rw [if_pos h]; exact IsRegexLang.one
  · rw [if_neg h]; exact IsRegexLang.zero


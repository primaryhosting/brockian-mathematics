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


theorem isRegexLang_accepts : IsRegexLang M.accepts := by
  rw [accepts_eq_finsetSup]
  exact IsRegexLang.finsetSup _ _ fun q _ => isRegexLang_pathLang M _ _ _

end DFAToRegex

/-- **Kleene's theorem.** Over a finite alphabet, a language is described by a regular expression
if and only if it is accepted by a DFA with finitely many states (`Language.IsRegular`). -/

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


theorem kstar_split {L : Language α} {x y : List α} (hx : x ≠ []) (h : x ++ y ∈ L∗) :
    ∃ u v y₁ y₂, x = u ++ v ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ y₁ ∈ L ∧ y = y₁ ++ y₂ ∧ y₂ ∈ L∗ := by
  obtain ⟨ws, hflat, hws⟩ := Language.mem_kstar.1 h
  exact kstar_split_aux ws hws x y hx hflat

/-- Left quotient of a Kleene star by a nonempty word. -/

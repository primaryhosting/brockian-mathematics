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


theorem singleton_mem_pathLang (S : Finset σ) (p : σ) (a : α) :
    [a] ∈ pathLang M S p (M.step p a) := by
  refine ⟨by simp, fun u v huv hu hv => ?_⟩
  rcases u with _ | ⟨b, u⟩
  · exact absurd rfl hu
  · rcases u with _ | ⟨c, u⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at huv
      exact absurd huv.2 hv
    · simp at huv

variable [DecidableEq σ]

/-- Concatenating a path from `p` to `m` with a path from `m` to `q` yields a path from `p` to
`q` whose intermediate states may additionally include `m`. -/

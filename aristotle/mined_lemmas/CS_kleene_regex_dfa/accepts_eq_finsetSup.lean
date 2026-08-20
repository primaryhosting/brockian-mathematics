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


theorem accepts_eq_finsetSup :
    M.accepts =
      ⨆ q ∈ (Finset.univ.filter fun q : σ => q ∈ M.accept), pathLang M Finset.univ M.start q := by
  ext x
  rw [mem_finsetSup]
  constructor
  · intro h
    refine ⟨M.evalFrom M.start x, ?_, rfl, fun u v _ _ _ => Finset.mem_univ _⟩
    simpa using h
  · rintro ⟨q, hq, h1, -⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [DFA.mem_accepts, DFA.eval, h1]
    exact hq

/-- The other direction of Kleene's theorem: over a finite alphabet, the language accepted by a
DFA with finitely many states is described by a regular expression. -/

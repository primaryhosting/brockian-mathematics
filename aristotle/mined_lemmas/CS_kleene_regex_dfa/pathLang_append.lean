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


theorem pathLang_append {S : Finset σ} {p m q : σ} {x y : List α}
    (hx : x ∈ pathLang M S p m) (hy : y ∈ pathLang M S m q) :
    x ++ y ∈ pathLang M (insert m S) p q := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨by rw [DFA.evalFrom_of_append, hx1, hy1], fun u w huw hu hw => ?_⟩
  rcases List.append_eq_append_iff.1 huw with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · rcases eq_or_ne a' [] with rfl | ha'
    · simp only [List.append_nil] at hx1
      rw [hx1]
      exact Finset.mem_insert_self m S
    · exact Finset.mem_insert_of_mem (hx2 u a' rfl hu ha')
  · rcases eq_or_ne c' [] with rfl | hc'
    · simp only [List.append_nil]
      rw [hx1]
      exact Finset.mem_insert_self m S
    · rw [DFA.evalFrom_of_append, hx1]
      exact Finset.mem_insert_of_mem (hy2 c' w rfl hc' hw)


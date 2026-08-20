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


theorem pathLang_insert_ge (S : Finset σ) (r p q : σ) :
    pathLang M S p q + pathLang M S p r * (pathLang M S r r)∗ * pathLang M S r q ≤
      pathLang M (insert r S) p q := by
  rintro z (hz | hz)
  · exact pathLang_mono M (Finset.subset_insert r S) p q hz
  · obtain ⟨w, ⟨x, hx, c, hc, rfl⟩, y, hy, rfl⟩ := hz
    have hc' : c ∈ pathLang M (insert r S) r r := kstar_pathLang_le M hc
    have hy' : y ∈ pathLang M (insert r S) r q :=
      pathLang_mono M (Finset.subset_insert r S) r q hy
    have hcy : c ++ y ∈ pathLang M (insert r S) r q := by
      have h := pathLang_append M hc' hy'
      rwa [Finset.insert_idem] at h
    have hx' : x ∈ pathLang M (insert r S) p r :=
      pathLang_mono M (Finset.subset_insert r S) p r hx
    have h := pathLang_append M hx' hcy
    rw [Finset.insert_idem] at h
    show (x ++ c) ++ y ∈ _
    rwa [List.append_assoc]


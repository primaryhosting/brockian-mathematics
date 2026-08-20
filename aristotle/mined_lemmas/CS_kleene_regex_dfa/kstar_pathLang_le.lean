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


theorem kstar_pathLang_le {S : Finset σ} {m : σ} :
    (pathLang M S m m)∗ ≤ pathLang M (insert m S) m m := by
  rintro z ⟨ws, rfl, hws⟩
  induction ws with
  | nil => simpa using nil_mem_pathLang M (insert m S) m
  | cons w ws ih =>
    rw [List.flatten_cons]
    have hw : w ∈ pathLang M (insert m S) m m :=
      pathLang_mono M (Finset.subset_insert m S) m m (hws w (by simp))
    have hrest : ws.flatten ∈ pathLang M (insert m S) m m :=
      ih fun z hz => hws z (by simp [hz])
    have h := pathLang_append M hw hrest
    rwa [Finset.insert_idem] at h


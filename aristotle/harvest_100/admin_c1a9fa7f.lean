/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Rice's theorem (extended form).**

Let `C` be a *semantic* property of partial functions, i.e. an arbitrary set of partial
functions `ℕ →. ℕ` (membership only depends on the function computed, not on the index).
If `C` is *nontrivial* in the sense that some partial computable function `f` has the
property and some partial computable function `g` does not, then the index set
`{c | eval c ∈ C}` is not recursive (not a `ComputablePred`).

This is a direct consequence of `ComputablePred.rice`. -/
theorem rice_extended (C : Set (ℕ →. ℕ)) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) (gC : g ∉ C) :
    ¬ ComputablePred fun c : Code => eval c ∈ C :=
  fun h => gC (ComputablePred.rice C h hf hg fC)

/-- Index-set form: a set of codes closed under extensional equality (a semantic property)
which is neither empty nor everything is not recursive. -/
theorem rice_extended_codes (C : Set Code)
    (H : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hne : C.Nonempty) (hnu : C ≠ Set.univ) :
    ¬ ComputablePred fun c : Code => c ∈ C := by
  intro h
  rcases (ComputablePred.rice₂ C H).1 h with h0 | h1
  · exact absurd h0 hne.ne_empty
  · exact hnu h1

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


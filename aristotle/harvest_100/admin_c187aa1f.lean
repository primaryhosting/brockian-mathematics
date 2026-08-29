import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **Rice's theorem (extended form).**

Let `P` be a *semantic* property of programs, i.e. a predicate on the partial functions
`ℕ →. ℕ` (so that `P` depends only on the function computed by a program, not on the
program text).  Assume `P` is *nontrivial* on the partial recursive functions: there is a
partial recursive `f` satisfying `P` and a partial recursive `g` not satisfying `P`.

Then the index set `{c | P (eval c)}` of programs whose computed function satisfies `P`
is not recursive (not decidable). -/
theorem rice_extended (P : (ℕ →. ℕ) → Prop) (f g : ℕ →. ℕ)
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (hPf : P f) (hPg : ¬ P g) :
    ¬ ComputablePred fun c : Code => P (eval c) := by
  intro h
  exact hPg (ComputablePred.rice {x : ℕ →. ℕ | P x} h hf hg hPf)

/-- Rice's theorem, phrased for a set of codes that is closed under semantic equivalence
(*extensional*) and nontrivial: such an index set is not recursive. -/
theorem rice_extended_set (C : Set Code)
    (hext : ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (c₁ ∈ C ↔ c₂ ∈ C))
    (hne : C.Nonempty) (hnu : C ≠ Set.univ) :
    ¬ ComputablePred fun c : Code => c ∈ C := by
  intro h
  rcases (ComputablePred.rice₂ C hext).1 h with h0 | h1
  · exact absurd h0 (Set.nonempty_iff_ne_empty.1 hne)
  · exact hnu h1

end CS


/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Statement: The set of indices of a nontrivial semantic property is not recursive (Rice).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.Halting

/-!
## Rice's theorem, extended form

We work with `Nat.Partrec.Code`, Mathlib's type of indices (codes) for partial recursive
functions `ℕ →. ℕ`, where `Code.eval : Code → (ℕ →. ℕ)` is the universal evaluation map.

A set `C` of codes is *semantic* if membership depends only on the partial function
computed, and *nontrivial* if it is neither empty nor everything.  Rice's theorem says
that such a `C` is never recursive.

The main theorem `CS.rice_extended` is proved directly from Kleene's recursion (fixed
point) theorem, and we then derive several extended forms: the complement is not
recursive either, the index-set formulation for a property of partial functions, and
the concrete instance that halting on a fixed input is undecidable.
-/

namespace CS

open Nat.Partrec (Code)

/-- A set of codes is *semantic* (extensional) when membership depends only on the
partial function computed by the code, not on the code itself. -/
def Semantic (C : Set Code) : Prop :=
  ∀ cf cg : Code, cf.eval = cg.eval → (cf ∈ C ↔ cg ∈ C)

/-- A set of codes is *nontrivial* when it is neither empty nor everything. -/
def Nontrivial (C : Set Code) : Prop :=
  (∃ c, c ∈ C) ∧ ∃ c, c ∉ C

/-- **Rice's theorem (extended form).**  If a set `C` of indices (codes) of partial
recursive functions is semantic (i.e. membership is invariant under passing to another
code computing the same partial function) and nontrivial (some code is in it and some
code is not), then `C` is not recursive: membership in `C` is not a computable predicate.

The proof is the classical one.  Fix `a ∈ C` and `b ∉ C`.  If membership in `C` were
decidable, the map `c ↦ if c ∈ C then b else a` would be computable, so by Kleene's
recursion theorem it has a fixed point `c`, i.e. a code `c` computing the same function
as its image.  Semanticity then forces `c ∈ C ↔ (if c ∈ C then b else a) ∈ C`, which is
a contradiction in both cases. -/
theorem rice_extended (C : Set Code) (hsem : Semantic C) (hnt : Nontrivial C) :
    ¬ ComputablePred (fun c : Code => c ∈ C) := by
  rintro ⟨_, hcomp⟩
  obtain ⟨a, ha⟩ := hnt.1
  obtain ⟨b, hb⟩ := hnt.2
  -- The "diagonalising" map `c ↦ if c ∈ C then b else a` is computable.
  have hf : Computable (fun c : Code => bif (decide (c ∈ C)) then b else a) :=
    Computable.cond hcomp (Computable.const b) (Computable.const a)
  -- Kleene's recursion theorem supplies a fixed point.
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hf
  by_cases h : c ∈ C
  · simp only [h, decide_true, cond_true] at hc
    exact hb ((hsem c b hc.symm).1 h)
  · simp only [h, decide_false, cond_false] at hc
    exact h ((hsem a c hc).1 ha)

/-- The complement of a nontrivial semantic set of codes is not recursive either. -/
theorem rice_extended_compl (C : Set Code) (hsem : Semantic C) (hnt : Nontrivial C) :
    ¬ ComputablePred (fun c : Code => c ∉ C) := by
  intro h
  refine rice_extended C hsem hnt ?_
  have := ComputablePred.not h
  simpa using this

/-- The index set of a nontrivial property `P` of partial recursive functions is not
recursive. -/
theorem rice_extended_index_set (P : (ℕ →. ℕ) → Prop)
    (hf : ∃ cf : Code, P cf.eval) (hg : ∃ cg : Code, ¬ P cg.eval) :
    ¬ ComputablePred (fun c : Code => P c.eval) := by
  refine rice_extended {c : Code | P c.eval} (fun cf cg h => by simp only [Set.mem_setOf_eq, h])
    ⟨hf, hg⟩

/-- There is a code for the everywhere-undefined partial function. -/
theorem exists_code_diverging : ∃ c : Code, c.eval = fun _ => Part.none :=
  Nat.Partrec.Code.exists_code.1 Nat.Partrec.none

/-- **Application.** For any input `n`, the set of codes that halt on `n` is a nontrivial
semantic set, hence by Rice's theorem it is not recursive: the halting problem is
undecidable. -/
theorem halting_not_recursive (n : ℕ) :
    ¬ ComputablePred (fun c : Code => (c.eval n).Dom) := by
  obtain ⟨d, hd⟩ := exists_code_diverging
  refine rice_extended_index_set (fun f => (f n).Dom) ⟨Code.const 0, ?_⟩ ⟨d, ?_⟩
  · simp [Nat.Partrec.Code.eval_const]
  · simp [hd]

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


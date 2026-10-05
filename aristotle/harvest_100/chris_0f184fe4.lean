/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace Isolation

universe u

/-- Syntax of isolation policies over an atom type `α`. -/
inductive Policy (α : Type u) : Type u
  | atom : α → Policy α
  | tru : Policy α
  | fls : Policy α
  | neg : Policy α → Policy α
  | conj : Policy α → Policy α → Policy α
  | disj : Policy α → Policy α → Policy α

namespace Policy

variable {α : Type u}

/-- Semantics of a policy relative to a valuation of atoms. -/
def eval (v : α → Bool) : Policy α → Bool
  | .atom a => v a
  | .tru => true
  | .fls => false
  | .neg p => !(eval v p)
  | .conj p q => eval v p && eval v q
  | .disj p q => eval v p || eval v q

/-- A policy is *disjunction free* when no `disj` node occurs positively in it
(negated subformulas are treated as opaque guards by the isolation engine). -/
def DisjFree : Policy α → Prop
  | .atom _ => True
  | .tru => True
  | .fls => True
  | .neg _ => True
  | .conj p q => DisjFree p ∧ DisjFree q
  | .disj _ _ => False

/-- The isolation engine's *disjunction split*: it decomposes a policy into a list of
disjunction-free branches, to be isolated and discharged independently. -/
def split : Policy α → List (Policy α)
  | .atom a => [.atom a]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg p => [.neg p]
  | .conj p q => (split p).flatMap fun a => (split q).map fun b => .conj a b
  | .disj p q => split p ++ split q

end Policy

variable {α : Type u}

/-- Every branch produced by the split is disjunction free, i.e. genuinely isolated. -/
theorem split_disjFree (p : Policy α) :
    ∀ b ∈ Policy.split p, Policy.DisjFree b := by
  induction p with
  | atom a => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | tru => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | fls => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | neg p _ => intro b hb; simp [Policy.split] at hb; subst hb; trivial
  | conj p q ihp ihq =>
      intro b hb
      simp only [Policy.split, List.mem_flatMap, List.mem_map] at hb
      obtain ⟨x, hx, y, hy, rfl⟩ := hb
      exact ⟨ihp x hx, ihq y hy⟩
  | disj p q ihp ihq =>
      intro b hb
      simp only [Policy.split, List.mem_append] at hb
      rcases hb with h | h
      · exact ihp b h
      · exact ihq b h

/-- The split is never empty: the engine always produces at least one branch. -/
theorem split_ne_nil (p : Policy α) : Policy.split p ≠ [] := by
  induction p with
  | atom a => simp [Policy.split]
  | tru => simp [Policy.split]
  | fls => simp [Policy.split]
  | neg p _ => simp [Policy.split]
  | conj p q ihp ihq =>
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ihp
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ ihq
      intro h
      have hmem : Policy.conj x y ∈ Policy.split (Policy.conj p q) := by
        simp only [Policy.split, List.mem_flatMap, List.mem_map]
        exact ⟨x, hx, y, hy, rfl⟩
      rw [h] at hmem
      simp at hmem
  | disj p q ihp _ => simp [Policy.split, ihp]

/--
**Disjunction split preserves semantics.**

The isolation engine's disjunction split is sound and complete: a valuation satisfies the
original policy exactly when it satisfies one of the isolated, disjunction-free branches.
-/
theorem disjunction_split_preserves_semantics (v : α → Bool) (p : Policy α) :
    Policy.eval v p = (Policy.split p).any (Policy.eval v) := by
  induction p with
  | atom a => simp [Policy.split, Policy.eval]
  | tru => simp [Policy.split, Policy.eval]
  | fls => simp [Policy.split, Policy.eval]
  | neg p _ => simp [Policy.split, Policy.eval]
  | conj p q ihp ihq =>
      simp only [Policy.split, Policy.eval, List.any_flatMap, List.any_map, ihp, ihq,
        Function.comp_def]
      induction Policy.split p with
      | nil => simp
      | cons x xs ih =>
          simp only [List.any_cons, ih, Bool.and_or_distrib_right]
          congr 1
          induction Policy.split q with
          | nil => simp
          | cons y ys ih2 =>
              simp only [List.any_cons, ih2, Bool.and_or_distrib_left]
  | disj p q ihp ihq => simp [Policy.split, Policy.eval, ihp, ihq]

/-- Soundness: any valuation satisfying an isolated branch satisfies the original policy. -/
theorem split_sound (v : α → Bool) (p b : Policy α)
    (hb : b ∈ Policy.split p) (h : Policy.eval v b = true) :
    Policy.eval v p = true := by
  rw [disjunction_split_preserves_semantics v p, List.any_eq_true]
  exact ⟨b, hb, h⟩

/-- Completeness: any valuation satisfying the policy satisfies some isolated branch. -/
theorem split_complete (v : α → Bool) (p : Policy α) (h : Policy.eval v p = true) :
    ∃ b ∈ Policy.split p, Policy.eval v b = true := by
  rw [disjunction_split_preserves_semantics v p, List.any_eq_true] at h
  exact h

end Isolation
end PCA

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


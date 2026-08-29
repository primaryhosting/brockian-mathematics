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

/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace PCA
namespace Isolation

/-- Isolation policies: propositional guard expressions over atomic capability
checks of type `α`, as used by the isolation engine of a proof-carrying app. -/
inductive Policy (α : Type u) where
  | atom : α → Policy α
  | tru : Policy α
  | fls : Policy α
  | neg : Policy α → Policy α
  | and : Policy α → Policy α → Policy α
  | or : Policy α → Policy α → Policy α
  deriving DecidableEq, Repr

variable {α : Type u}

/-- Semantics of a policy relative to an environment assigning a truth value to
each atomic capability check. -/
def eval (env : α → Bool) : Policy α → Bool
  | .atom a => env a
  | .tru => true
  | .fls => false
  | .neg p => !eval env p
  | .and p q => eval env p && eval env q
  | .or p q => eval env p || eval env q

/-- The disjunction split of a policy: the list of disjunction-free *branches*
obtained by distributing conjunction over disjunction (a DNF-style split).  The
isolation engine analyses each branch separately. -/
def split : Policy α → List (Policy α)
  | .or p q => split p ++ split q
  | .and p q => (split p).flatMap fun a => (split q).map fun b => .and a b
  | .atom a => [.atom a]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg p => [.neg p]

/-- A policy contains no disjunction. -/
def IsOrFree : Policy α → Prop
  | .or _ _ => False
  | .and p q => IsOrFree p ∧ IsOrFree q
  | _ => True

/-- Pulling a constant out of `List.any` on the right. -/
private theorem any_and_const_right {β : Type v} (l : List β) (f : β → Bool) (c : Bool) :
    (l.any fun a => f a && c) = (l.any f && c) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.any_cons, ih, Bool.and_or_distrib_right]

/-- Pulling a constant out of `List.any` on the left. -/
private theorem any_const_and_left {β : Type v} (l : List β) (f : β → Bool) (c : Bool) :
    (l.any fun a => c && f a) = (c && l.any f) := by
  simpa [Bool.and_comm] using any_and_const_right l f c

/-- **Main theorem.**  Splitting a policy along its disjunctions preserves its
semantics: a policy holds in an environment exactly when one of the branches
produced by `split` holds. -/
theorem disjunction_split_preserves_semantics (env : α → Bool) (p : Policy α) :
    ((split p).any fun q => eval env q) = eval env p := by
  induction p with
  | atom a => simp [split, eval]
  | tru => simp [split, eval]
  | fls => simp [split, eval]
  | neg p _ => simp [split, eval]
  | and p q ihp ihq =>
      simp only [split, eval, List.any_flatMap, List.any_map, Function.comp_def]
      rw [← ihp, ← ihq]
      simp only [any_const_and_left, any_and_const_right]
  | or p q ihp ihq => simp [split, eval, List.any_append, ihp, ihq]

/-- Propositional form of the main theorem: the policy holds iff some branch of
the split holds. -/
theorem disjunction_split_iff_exists (env : α → Bool) (p : Policy α) :
    eval env p = true ↔ ∃ q ∈ split p, eval env q = true := by
  rw [← disjunction_split_preserves_semantics env p]
  simp

/-- Soundness: every branch of the split entails the original policy. -/
theorem eval_of_mem_split {env : α → Bool} {p q : Policy α}
    (hq : q ∈ split p) (h : eval env q = true) : eval env p = true :=
  (disjunction_split_iff_exists env p).2 ⟨q, hq, h⟩

/-- Completeness: if the policy holds then some branch of the split holds. -/
theorem exists_mem_split_eval {env : α → Bool} {p : Policy α} (h : eval env p = true) :
    ∃ q ∈ split p, eval env q = true :=
  (disjunction_split_iff_exists env p).1 h

/-- The split is never empty. -/
theorem split_ne_nil (p : Policy α) : split p ≠ [] := by
  induction p with
  | atom a => simp [split]
  | tru => simp [split]
  | fls => simp [split]
  | neg p _ => simp [split]
  | and p q ihp ihq =>
      cases hp : split p with
      | nil => exact absurd hp ihp
      | cons a as =>
        cases hq : split q with
        | nil => exact absurd hq ihq
        | cons b bs => simp [split, hp, hq]
  | or p q ihp _ => simp [split, ihp]

/-- Every branch produced by the split is disjunction-free: the isolation engine
only ever has to analyse disjunction-free policies. -/
theorem isOrFree_of_mem_split {p q : Policy α} (hq : q ∈ split p) : IsOrFree q := by
  induction p generalizing q with
  | atom a => simp only [split, List.mem_singleton] at hq; subst hq; trivial
  | tru => simp only [split, List.mem_singleton] at hq; subst hq; trivial
  | fls => simp only [split, List.mem_singleton] at hq; subst hq; trivial
  | neg p _ => simp only [split, List.mem_singleton] at hq; subst hq; trivial
  | and p r ihp ihr =>
      simp only [split, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨a, ha, b, hb, rfl⟩ := hq
      exact ⟨ihp ha, ihr hb⟩
  | or p r ihp ihr =>
      simp only [split, List.mem_append] at hq
      exact hq.elim ihp ihr

end Isolation
end PCA


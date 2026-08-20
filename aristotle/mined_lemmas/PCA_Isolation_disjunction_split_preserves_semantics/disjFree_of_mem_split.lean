/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace PCA
namespace Isolation

universe u

/-- Syntax of isolation constraints over a type `α` of atomic predicates
(e.g. "capability `c` is granted", "resource `r` is reachable"). -/
inductive Constraint (α : Type u) : Type u
  | atom : α → Constraint α
  | tru : Constraint α
  | fls : Constraint α
  | neg : Constraint α → Constraint α
  | conj : Constraint α → Constraint α → Constraint α
  | disj : Constraint α → Constraint α → Constraint α
  deriving Repr

namespace Constraint

variable {α : Type u}

/-- Semantics of an isolation constraint relative to a valuation `v` of the atoms. -/

theorem disjFree_of_mem_split {c b : Constraint α} (hb : b ∈ split c) : disjFree b := by
  induction c with
  | disj c d ihc ihd =>
      rcases List.mem_append.mp hb with h | h
      · exact ihc h
      · exact ihd h
  | atom a => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | tru => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | fls => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | neg c _ => simp only [split, List.mem_singleton] at hb; subst hb; trivial
  | conj c d _ _ => simp only [split, List.mem_singleton] at hb; subst hb; trivial

end Constraint

open Constraint

/-- **Disjunction split preserves semantics.**  For every valuation `v` and every
isolation constraint `c`, the constraint holds exactly when one of the branches
produced by `split` holds.  The forward direction is completeness of the split
(no model is lost) and the backward direction is its soundness (no model is added). -/

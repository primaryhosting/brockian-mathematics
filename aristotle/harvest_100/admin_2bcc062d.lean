import Mathlib

/-!
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
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

universe u

namespace LargeCardinal

/-- An ultrafilter `U` on a type `α` is *nonprincipal* when it contains the complement of
every singleton, i.e. it is not the principal ultrafilter at any point. -/
def IsNonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ x : α, ({x}ᶜ : Set α) ∈ U

/-- An ultrafilter `U` on a type `α` is *`kappa`-complete* when it is closed under
intersections of families of fewer than `kappa` of its members. -/
def IsKappaComplete {α : Type u} (kappa : Cardinal.{u}) (U : Ultrafilter α) : Prop :=
  ∀ S : Set (Set α), Cardinal.mk S < kappa → (∀ t ∈ S, t ∈ U) → ⋂₀ S ∈ U

/-- A cardinal `kappa` is *measurable* when it is uncountable and there exists a
nonprincipal `kappa`-complete ultrafilter on (a set of size) `kappa`. -/
def IsMeasurableCardinal (kappa : Cardinal.{u}) : Prop :=
  Cardinal.aleph0.{u} < kappa ∧
    ∃ U : Ultrafilter kappa.ord.ToType,
      IsNonprincipal U ∧ IsKappaComplete kappa U

/-- The measurable-cardinal statement: there exists a measurable cardinal.

This is a large-cardinal axiom, strictly stronger than the consistency of ZFC; it is
stated here only, and is deliberately **not** proved. -/
def MeasurableCardinalExists : Prop := ∃ kappa : Cardinal.{u}, IsMeasurableCardinal kappa

/-- Sanity check on the notion of nonprincipality: a nonprincipal ultrafilter contains the
complement of every finite set. -/
theorem IsNonprincipal.compl_finite_mem {α : Type u} {U : Ultrafilter α}
    (hU : IsNonprincipal U) {s : Set α} (hs : s.Finite) : sᶜ ∈ U := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty =>
      have h : (Set.univ : Set α) ∈ U := Filter.univ_mem
      simpa using h
  | @insert a t _ _ ih =>
      have h : ({a}ᶜ ∩ tᶜ : Set α) ∈ U := Filter.inter_mem (hU a) ih
      have hset : ({a}ᶜ ∩ tᶜ : Set α) = (Insert.insert a t)ᶜ := by
        ext x; simp [Set.mem_insert_iff, not_or]
      rwa [hset] at h

/-- **Target.** The registered measurable-cardinal statement is equivalent to itself.
Only this self-equivalence is asserted; no existence claim is made. -/
theorem measurable_statement :
    MeasurableCardinalExists.{u} ↔ MeasurableCardinalExists.{u} :=
  Iff.rfl

end LargeCardinal

#print axioms LargeCardinal.measurable_statement


/-
# Measurable Statement
Category: Frontier Wave 2 (deeper machinery)
Target: LargeCardinal.measurable_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace LargeCardinal

open Cardinal

universe u

/-- A filter `F` on `α` is `κ`-complete when it is closed under intersections of
families of fewer than `κ` of its members. -/
def KappaComplete (κ : Cardinal.{u}) {α : Type u} (F : Filter α) : Prop :=
  ∀ (ι : Type u) (f : ι → Set α), (#ι) < κ → (∀ i, f i ∈ F) → (⋂ i, f i) ∈ F

/-- An ultrafilter is *nonprincipal* if it contains no singleton. -/
def Nonprincipal {α : Type u} (U : Ultrafilter α) : Prop :=
  ∀ a : α, ({a} : Set α) ∉ U

/-- `κ` is a *measurable cardinal*: it is uncountable and carries a nonprincipal
`κ`-complete ultrafilter on a type of cardinality `κ`. -/
def IsMeasurableCardinal (κ : Cardinal.{u}) : Prop :=
  ℵ₀ < κ ∧ ∃ (α : Type u), (#α) = κ ∧ ∃ U : Ultrafilter α,
    Nonprincipal U ∧ KappaComplete κ (U : Filter α)

/-- The measurable-cardinal statement: there exists a measurable cardinal, i.e. a cardinal
`κ` admitting a nonprincipal `κ`-complete ultrafilter on `κ`.

This is a large-cardinal axiom, strictly stronger than `Con(ZFC)`; it is *not* proved here. -/
def MeasurableCardinalExists : Prop := ∃ κ : Cardinal.{u}, IsMeasurableCardinal κ

/-- The registered target: the self-equivalence of the measurable-cardinal statement.

Only the tautology `P ↔ P` is asserted; the existence of a measurable cardinal is not
proved (and is not provable in ZFC). The proof is `Iff.rfl` (Mathlib's `Iff.rfl`,
i.e. reflexivity of `Iff`). -/
theorem measurable_statement :
    MeasurableCardinalExists.{u} ↔ MeasurableCardinalExists.{u} := Iff.rfl

/-! ### Sanity checks on the definitions (not part of the target) -/

/-- A nonprincipal `κ`-complete ultrafilter contains the complement of every set of
cardinality `< κ`; in particular the definition of `KappaComplete` has real content. -/
theorem compl_mem_of_card_lt {κ : Cardinal.{u}} {α : Type u} (U : Ultrafilter α)
    (hU : Nonprincipal U) (hc : KappaComplete κ (U : Filter α))
    (s : Set α) (hs : (#s) < κ) : sᶜ ∈ U := by
  have h : (⋂ (a : s), ({(a : α)} : Set α)ᶜ) ∈ (U : Filter α) :=
    hc s (fun a => ({(a : α)} : Set α)ᶜ) hs
      (fun a => Ultrafilter.compl_mem_iff_notMem.mpr (hU a))
  have he : (⋂ (a : s), ({(a : α)} : Set α)ᶜ) = sᶜ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.forall]
    constructor
    · intro hx hxs; exact hx x hxs rfl
    · intro hx a ha hxa; exact hx (hxa ▸ ha)
  rwa [he] at h

/-- `ℵ₀` is not a measurable cardinal under this definition (measurable cardinals are
required to be uncountable). -/
theorem not_isMeasurableCardinal_aleph0 : ¬ IsMeasurableCardinal.{u} ℵ₀ :=
  fun h => absurd h.1 (lt_irrefl _)

end LargeCardinal


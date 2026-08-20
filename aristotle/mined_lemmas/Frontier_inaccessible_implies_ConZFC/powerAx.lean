/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
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

set_option grind.warning false

universe u

namespace Frontier

open Cardinal Ordinal ZFSet Order

/-- `IsZFCModel M` says that the ZFC set `M`, equipped with the inherited membership
relation, is a model of ZFC: every axiom of ZFC, *relativized to* `M` (all quantifiers
bounded by `M`), holds.

The separation and replacement schemes are stated in their *second-order* form, i.e. for
arbitrary (meta-level) predicates and functions; this is stronger than the first-order
schemes, whose instances are obtained by taking the predicate/function defined by a
formula. Choice is stated in Zermelo's transversal form (every family of pairwise disjoint
nonempty sets has a choice set), which is equivalent to the axiom of choice over ZF. -/
structure IsZFCModel (M : ZFSet.{u}) : Prop where
  /-- The model is nonempty. -/
  nonempty : ∃ x, x ∈ M
  /-- The domain is transitive, so that membership is absolute. -/
  transitive : M.IsTransitive
  /-- Extensionality. -/
  ext : ∀ x ∈ M, ∀ y ∈ M, (∀ z ∈ M, z ∈ x ↔ z ∈ y) → x = y
  /-- Existence of the empty set. -/
  empty : ∃ e ∈ M, ∀ z ∈ M, z ∉ e
  /-- Pairing. -/
  pairing : ∀ x ∈ M, ∀ y ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ z = x ∨ z = y)
  /-- Union. -/
  union : ∀ x ∈ M, ∃ u ∈ M, ∀ z ∈ M, (z ∈ u ↔ ∃ y ∈ M, y ∈ x ∧ z ∈ y)
  /-- Power set. -/
  powerset : ∀ x ∈ M, ∃ p ∈ M, ∀ z ∈ M, (z ∈ p ↔ ∀ w ∈ M, w ∈ z → w ∈ x)
  /-- Infinity: there is an inductive set. -/
  infinity : ∃ i ∈ M, (∃ e ∈ M, e ∈ i ∧ ∀ z ∈ M, z ∉ e) ∧
      ∀ x ∈ M, x ∈ i → ∃ y ∈ M, y ∈ i ∧ ∀ z ∈ M, (z ∈ y ↔ z ∈ x ∨ z = x)
  /-- Separation, in second-order form. -/
  separation : ∀ (p : ZFSet.{u} → Prop), ∀ x ∈ M, ∃ s ∈ M, ∀ z ∈ M, (z ∈ s ↔ z ∈ x ∧ p z)
  /-- Replacement, in second-order form. -/
  replacement : ∀ (F : ZFSet.{u} → ZFSet.{u}), ∀ x ∈ M, (∀ a ∈ M, a ∈ x → F a ∈ M) →
      ∃ r ∈ M, ∀ z ∈ M, (z ∈ r ↔ ∃ a ∈ M, a ∈ x ∧ F a = z)
  /-- Foundation. -/
  foundation : ∀ x ∈ M, (∃ z ∈ M, z ∈ x) → ∃ y ∈ M, y ∈ x ∧ ∀ z ∈ M, z ∈ y → z ∉ x
  /-- Choice, in Zermelo's transversal form. -/
  choice : ∀ x ∈ M, (∀ y ∈ M, y ∈ x → ∃ z ∈ M, z ∈ y) →
      (∀ y ∈ M, ∀ y' ∈ M, y ∈ x → y' ∈ x → y ≠ y' → ¬ ∃ z ∈ M, z ∈ y ∧ z ∈ y') →
      ∃ c ∈ M, ∀ y ∈ M, y ∈ x → ∃! z, z ∈ M ∧ z ∈ y ∧ z ∈ c

/-! ### Cardinal arithmetic below an inaccessible -/

/-- Below an inaccessible cardinal `κ`, all the stages `V_ a` of the cumulative hierarchy
have size `< κ`: this is `preBeth a < κ` for `a < κ.ord`. Strong limitness handles the
successor step and regularity the limit step. -/

def powerAx : setLang.Sentence :=
  ∀' ∃' ∀' ((memF (&⟨2, by omega⟩) (&⟨1, by omega⟩)) ⇔
    (∀' ((memF (&⟨3, by omega⟩) (&⟨2, by omega⟩)) ⟹ (memF (&⟨3, by omega⟩) (&⟨0, by omega⟩)))))

/-- Infinity. -/

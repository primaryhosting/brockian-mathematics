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

/-
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/

lemma finite_Qt_of_both {a b c : Submodule k M} (hab : a ≤ b) (hbc : b ≤ c)
    [Module.Finite k (Qt a b)] [Module.Finite k (Qt b c)] : Module.Finite k (Qt a c) := by
  have h := rank_Qt_add hab hbc
  have h1 : Module.rank k (Qt a b) < Cardinal.aleph0 := Module.rank_lt_aleph0 k _
  have h2 : Module.rank k (Qt b c) < Cardinal.aleph0 := Module.rank_lt_aleph0 k _
  have : Module.rank k (Qt a c) < Cardinal.aleph0 := by
    rw [← h]; exact Cardinal.add_lt_aleph0 h1 h2
  exact Module.rank_lt_aleph0_iff.mp this

end Math2

/-
Basic valuation-theoretic setup for the function field of a smooth projective curve.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open scoped Classical

/-- Valuation data on a field `K` over a base field `k`, indexed by a type `Place`
of closed points. Each place carries a normalized discrete valuation of `K`
which is trivial on `k`. -/
structure PlaceData (k K : Type*) [Field k] [Field K] [Algebra k K] (Place : Type*) where
  /-- The order of vanishing of `x` at the place `P` (junk value `0` at `x = 0`). -/
  v : Place → K → ℤ
  v_zero : ∀ P, v P 0 = 0
  v_mul : ∀ (P : Place) {x y : K}, x ≠ 0 → y ≠ 0 → v P (x * y) = v P x + v P y
  v_add : ∀ (P : Place) {x y : K}, x + y ≠ 0 → min (v P x) (v P y) ≤ v P (x + y)
  v_algebraMap : ∀ (P : Place) (c : k), v P (algebraMap k K c) = 0
  exists_uniformizer : ∀ P : Place, ∃ t : K, t ≠ 0 ∧ v P t = 1
  v_finite_support : ∀ {x : K}, x ≠ 0 → {P | v P x ≠ 0}.Finite

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)


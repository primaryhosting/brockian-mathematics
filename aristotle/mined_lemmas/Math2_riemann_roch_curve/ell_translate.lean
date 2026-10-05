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

lemma ell_translate (D : Divisor Place) {x : K} (hx : x ≠ 0) :
    V.ell (D - V.divisorOf x) = V.ell D := by
  have e : V.Lspace D ≃ₗ[k] V.Lspace (D - V.divisorOf x) :=
    ((mulEquiv (k := k) hx).submoduleMap (V.Lspace D)).trans
      (LinearEquiv.ofEq _ _ (V.map_Lspace D hx))
  exact (e.finrank_eq).symm

end PlaceData

/-! ### Curve data -/

/-- The data of a smooth projective curve over `k`, presented through its function field `K`,
its set of closed points, and the orders of vanishing at those points.

The axioms are the standard elementary facts about the function field of a smooth
projective curve: the residue field at a closed point is a finite extension of `k`, a
principal divisor has degree `0`, the functions without poles are the constants, and
Riemann's inequality `ℓ(D) ≥ deg D + 1 - g₀` holds for some `g₀`. -/
structure CurveData (k K : Type*) [Field k] [Field K] [Algebra k K] (Place : Type*)
    extends PlaceData k K Place where
  /-- There is at least one closed point. -/
  place_nonempty : Nonempty Place
  /-- Residue fields are finite over `k`. -/
  residue_finite : ∀ P : Place,
    Module.Finite k (Qt (toPlaceData.Kge P 1) (toPlaceData.Kge P 0))
  /-- Principal divisors have degree zero. -/
  deg_principal : ∀ {x : K}, x ≠ 0 → toPlaceData.deg (toPlaceData.divisorOf x) = 0
  /-- A function without poles is constant. -/
  constants : ∀ x : K, (∀ P : Place, (0 : WithTop ℤ) ≤ toPlaceData.ord P x) →
    ∃ c : k, x = algebraMap k K c
  /-- Riemann's inequality. -/
  riemann : ∃ g₀ : ℕ, ∀ D : Divisor Place,
    toPlaceData.deg D + 1 - (g₀ : ℤ) ≤ (toPlaceData.ell D : ℤ)

end Math2


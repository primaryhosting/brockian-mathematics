import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
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

namespace Frontier

/-- **Descent theorem** (the group-theoretic heart of the Mordell–Weil theorem).

Let `A` be an abelian group equipped with a real-valued "height" function `h` such that

* `hfin`  : every sublevel set `{P | h P ≤ C}` is finite;
* `htrans`: translation by a fixed element at worst doubles the height, up to a constant;
* `hdup`  : duplication at least quadruples the height, up to a constant;
* `hweak` : (weak Mordell–Weil) `A / 2A` is finite, phrased as the existence of a finite set
            of coset representatives `S` for the subgroup `2A`.

Then `A` is a finitely generated abelian group. -/

theorem Mordell_finite_generation {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h : E.toAffine.Point → ℝ)
    (hfin : ∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite)
    (htrans : ∀ Q : E.toAffine.Point, ∃ C : ℝ,
      ∀ P : E.toAffine.Point, h (P - Q) ≤ 2 * h P + C)
    (hdup : ∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P ≤ h (2 • P) + C)
    (hweak : ∃ S : Finset E.toAffine.Point, ∀ P : E.toAffine.Point,
      ∃ Q ∈ S, ∃ R : E.toAffine.Point, P = Q + 2 • R) :
    AddGroup.FG E.toAffine.Point :=
  fg_of_height_descent h hfin htrans hdup hweak

end Frontier


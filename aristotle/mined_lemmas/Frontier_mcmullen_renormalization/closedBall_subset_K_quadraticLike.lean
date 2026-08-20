import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

/-!
## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a proper holomorphic map of degree two `f : U → V` between topological
discs in `ℂ` with `closure U` a compact subset of `V`.

We encode this as a structure.  The degree-two condition is encoded by:
* surjectivity of `f : U → V` (`surjOn`),
* every fibre over `V` has at most two points (`deg_le_two`),
* there is a unique critical point `crit ∈ U` (`crit_mem`, `deriv_crit`, `crit_unique`).

Properness of `f : U → V` is recorded in the field `proper`.
-/

/-- A quadratic-like map: a proper degree-two holomorphic map `f : U → V` of plane domains
with `closure U` compact and contained in `V`. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the big domain -/
  V : Set ℂ
  /-- the map, given as a globally defined function which is holomorphic on `U` -/
  f : ℂ → ℂ
  /-- the (unique) critical point -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  surjOn : V ⊆ f '' U
  proper : ∀ C ⊆ V, IsCompact C → IsCompact (U ∩ f ⁻¹' C)
  crit_mem : crit ∈ U
  deriv_crit : deriv f crit = 0
  crit_unique : ∀ z ∈ U, deriv f z = 0 → z = crit
  deg_le_two : ∀ w ∈ V, (U ∩ f ⁻¹' {w}).ncard ≤ 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit stays
in the small domain `U`. -/

theorem closedBall_subset_K_quadraticLike (c : ℂ) (hc : ‖c‖ < 2) (hc4 : ‖c‖ ≤ 1 / 4) :
    Metric.closedBall (0 : ℂ) (1 / 2) ⊆ (quadraticLike c hc).K := by
  intro z hz n
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have key : ∀ m : ℕ, ‖(fun w : ℂ => w ^ 2 + c)^[m] z‖ ≤ 1 / 2 := by
    intro m
    induction m with
    | zero => simpa using hz'
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact norm_sq_add_le c hc4 ih
  have h1 : ‖((quadraticLike c hc).f^[n] z) ^ 2 + c‖ ≤ 1 / 2 :=
    norm_sq_add_le c hc4 (key n)
  have : ‖((quadraticLike c hc).f^[n] z) ^ 2 + c‖ < 2 := by linarith
  exact this

/-!
## Rigidity in the quadratic family

No two distinct members of the quadratic family `z ↦ z² + c` are conjugate by an affine map;
this is the base case of the rigidity statements for quadratic-like maps.
-/

/-- **Rigidity, base case.**  If the affine map `z ↦ a z + b` (with `a ≠ 0`) conjugates
`z ↦ z² + c` to `z ↦ z² + c'`, then the conjugacy is the identity and `c = c'`. -/

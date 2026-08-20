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

theorem affine_conjugacy_rigidity {a b c c' : ℂ} (ha : a ≠ 0)
    (h : ∀ z : ℂ, a * (z ^ 2 + c) + b = (a * z + b) ^ 2 + c') :
    a = 1 ∧ b = 0 ∧ c = c' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  have hb : b = 0 := by
    have hab : (4 : ℂ) * (a * b) = 0 := by linear_combination h2 - h1
    have hab' : a * b = 0 := by linear_combination (1 / 4 : ℂ) * hab
    rcases mul_eq_zero.mp hab' with h' | h'
    · exact absurd h' ha
    · exact h'
  subst hb
  have ha1 : a = 1 := by
    have hsq : a * a = 1 * a := by linear_combination h0 - h1
    exact mul_right_cancel₀ ha hsq
  refine ⟨ha1, rfl, ?_⟩
  subst ha1
  linear_combination h0

/-!
## The main statement
-/

/-- **McMullen renormalization / rigidity for quadratic-like maps.**

This packages:

1. *Structure of the filled Julia set*: for every quadratic-like map `F`, the filled Julia set
   `K(F)` is compact, forward invariant and totally invariant.
2. *Base case*: for `‖c‖ < 2` the quadratic polynomial `z ↦ z² + c` is quadratic-like on
   suitable domains, for `c = 0` the filled Julia set is exactly the closed unit disc, and for
   `‖c‖ ≤ 1/4` the filled Julia set contains the disc of radius `1/2` (so it is nonempty).
3. *Renormalization reduction*: if `F` is renormalizable with period `p ≥ 2`, with
   renormalization `G ≃ F^p`, then the small filled Julia set `K(G)` is a compact subset of
   `K(F)` which is invariant under `F^p`.
4. *Rigidity base case*: distinct members of the quadratic family are not affinely conjugate.
5. *Composition*: renormalizing a renormalization of period `p` with period `q` yields a
   renormalization of period `p * q` with the same small quadratic-like map.
6. *Consistency*: the axioms describing a quadratic-like restriction of period `p` are
   satisfiable (the period-one restriction of `F` by itself).
-/

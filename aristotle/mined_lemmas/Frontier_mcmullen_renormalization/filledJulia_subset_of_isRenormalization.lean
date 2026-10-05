/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a module
-- docstring before the `import` line; the same text is reproduced as the module docstring below.)

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

/-! ## Quadratic-like maps (Douady–Hubbard) -/

/-- A *quadratic-like map* in the sense of Douady–Hubbard: a proper degree-two
holomorphic branched covering `f : V → U` between two bounded, connected open subsets of `ℂ`
with `closure V ⊆ U`.

Degree two is encoded concretely: there is a (unique) critical point `c ∈ V` whose fibre is the
singleton `{c}`, and every other fibre over `U` consists of exactly two points. -/
structure QuadraticLike : Type where
  /-- The larger domain. -/
  U : Set ℂ
  /-- The smaller domain, compactly contained in `U`. -/
  V : Set ℂ
  /-- The map (defined on all of `ℂ`, but only its restriction to `V` matters). -/
  f : ℂ → ℂ
  /-- The critical point. -/
  c : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  closure_V_subset : closure V ⊆ U
  isBounded_V : Bornology.IsBounded V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  analyticOn : AnalyticOnNhd ℂ f V
  mapsTo : Set.MapsTo f V U
  surjOn : Set.SurjOn f V U
  /-- Properness of `f : V → U`. -/
  proper : ∀ L ⊆ U, IsCompact L → IsCompact (V ∩ f ⁻¹' L)
  crit_mem : c ∈ V
  /-- The critical fibre is a single point. -/
  crit_fiber : V ∩ f ⁻¹' {f c} = {c}
  /-- Every non-critical fibre has exactly two points: `f : V → U` has degree two. -/
  deg_two : ∀ w ∈ U, w ≠ f c → (V ∩ f ⁻¹' {w}).ncard = 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points of `V` whose whole forward
orbit stays in `V`. -/

theorem filledJulia_subset_of_isRenormalization {F G : QuadraticLike} {n : ℕ}
    (h : IsRenormalization F n G) : G.filledJulia ⊆ F.filledJulia := by
  obtain ⟨hn, _hVsub, _hc, hEq, horb, _hconn⟩ := h
  intro z hz M
  have hzV : ∀ j : ℕ, G.f^[j] z ∈ G.V := hz
  have hkey : F.f^[n * (M / n)] z = G.f^[M / n] z := by
    rw [Function.iterate_mul]
    exact (iterate_eq_of_orbit_mem hEq (fun j _ => hzV j)).symm
  have hMsplit : M % n + n * (M / n) = M := Nat.mod_add_div M n
  have : F.f^[M] z = F.f^[M % n] (G.f^[M / n] z) := by
    conv_lhs => rw [← hMsplit]
    rw [Function.iterate_add_apply, hkey]
  rw [this]
  exact horb (M % n) (Nat.mod_lt _ (by omega)) (hzV (M / n))

/-- Renormalizations compose: an `m`-th renormalization of an `n`-th renormalization of `F` is an
`(n*m)`-th renormalization of `F`. -/

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

theorem filledJulia_eq_preimage : F.filledJulia = F.V ∩ F.f ⁻¹' F.filledJulia := by
  ext z
  simp only [filledJulia, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun n => by simpa [Function.iterate_succ_apply] using h (n + 1)⟩
  · rintro ⟨hzV, h⟩ n
    cases n with
    | zero => simpa using hzV
    | succ n => simpa [Function.iterate_succ_apply] using h n

/-- The filled Julia set is forward invariant. -/

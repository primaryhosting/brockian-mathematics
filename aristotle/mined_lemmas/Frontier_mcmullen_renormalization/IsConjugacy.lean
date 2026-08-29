/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a holomorphic map `f : U → V` between bounded open subsets of `ℂ`
with `U ⋐ V`, which is a proper degree-two branched covering onto `V`.

We encode "proper degree two branched covering" concretely and checkably:
`f` maps `U` into `V`, `f` is onto `V`, every fibre over `V` has at most two points,
and `f` has a unique critical point in `U`.
-/

/-- A quadratic-like map: a holomorphic degree-two proper map `f : U → V` with
`closure U ⊆ V` and `U` bounded. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- `U ⋐ V` : the closure of `U` is contained in `V`. -/
  closure_subset : closure U ⊆ V
  bounded_U : Bornology.IsBounded U
  /-- `f` is holomorphic on `U`. -/
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is onto. -/
  surjOn : Set.SurjOn f U V
  /-- every fibre of `f : U → V` has at most two points (degree two). -/
  fiber_le_two : ∀ w ∈ V, {z | z ∈ U ∧ f z = w}.ncard ≤ 2
  /-- `f` has a unique critical point in `U`. -/
  unique_crit : ∃! c : ℂ, c ∈ U ∧ deriv f c = 0

namespace QuadraticLike

variable (Q : QuadraticLike)


theorem IsConjugacy.image_filledJulia {Q₁ Q₂ : QuadraticLike} {h : ℂ → ℂ}
    (H : IsConjugacy Q₁ Q₂ h) : h '' Q₁.filledJulia = Q₂.filledJulia := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have key : ∀ n : ℕ, Q₂.f^[n] (h z) = h (Q₁.f^[n] z) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
          exact (H.conj _ (hz n)).symm
    intro n
    rw [key n]
    exact H.bijOn.mapsTo (hz n)
  · intro w hw
    obtain ⟨z, hzU, rfl⟩ := H.bijOn.surjOn (hw 0)
    have key : ∀ n : ℕ, Q₁.f^[n] z ∈ Q₁.U ∧ Q₂.f^[n] (h z) = h (Q₁.f^[n] z) := by
      intro n
      induction n with
      | zero => exact ⟨by simpa using hzU, by simp⟩
      | succ n ih =>
          obtain ⟨hmem, heq⟩ := ih
          have hstep : Q₂.f^[n + 1] (h z) = h (Q₁.f^[n + 1] z) := by
            rw [Function.iterate_succ_apply', heq, Function.iterate_succ_apply']
            exact (H.conj _ hmem).symm
          refine ⟨?_, hstep⟩
          -- the image point lies in `Q₂.U`, hence comes from a point of `Q₁.U`;
          -- injectivity on `Q₁.V` identifies it with the orbit point.
          have hx : Q₁.f^[n + 1] z ∈ Q₁.V := by
            rw [Function.iterate_succ_apply']
            exact Q₁.mapsTo hmem
          have himg : h (Q₁.f^[n + 1] z) ∈ Q₂.U := by
            rw [← hstep]; exact hw (n + 1)
          obtain ⟨y, hyU, hy⟩ := H.bijOn.surjOn himg
          have : y = Q₁.f^[n + 1] z := H.injOn (Q₁.subset_V hyU) hx hy
          rwa [← this]
    exact ⟨z, fun n => (key n).1, rfl⟩

/-! ## Main statement -/

/--
**McMullen renormalization / rigidity for quadratic-like maps.**

This packages the formalized statements together with the parts that are proved here:

1. *Base case*: every quadratic polynomial `z ↦ z² + c` is quadratic-like on suitable
   domains, with critical point `0` in its domain (so the notion is non-vacuous).
2. *Trivial (period one) renormalization*: every quadratic-like map is a renormalization
   of itself of period `1`.
3. *Renormalization tower (reduction)*: renormalizations compose — a renormalization of
   period `m` of a renormalization of period `n` is a renormalization of period `n · m`.
4. *Filled Julia sets*: they are forward invariant and bounded.
5. *Rigidity*: a conjugacy between quadratic-like maps carries the filled Julia set of one
   onto that of the other.
-/

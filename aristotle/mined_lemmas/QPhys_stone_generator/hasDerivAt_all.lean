import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = ContinuousLinearMap.id ℂ H
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  inner_map : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  cont : ∀ x, Continuous fun t => U t x

variable {U : ℝ → H →L[ℂ] H}

/-- The natural domain of the generator: those vectors for which `t ↦ U t x` is
differentiable at `0`. -/

theorem hasDerivAt_all (hU : IsUnitaryGroup U) {x : H} (hx : x ∈ domain U) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s x) (U t (Complex.I • generator U x)) t := by
  have h0 := hasDerivAt_of_mem_domain hx
  have h1 : HasDerivAt (fun s : ℝ => U (s - t) x) (Complex.I • generator U x) t :=
    HasDerivAt.comp_sub_const (f := fun u : ℝ => U u x) t t (by simpa using h0)
  have h2 := clm_comp_hasDerivAt (U t) h1
  have key : ∀ s : ℝ, U t (U (s - t) x) = U s x := by
    intro s
    have e : t + (s - t) = s := by ring
    rw [← ContinuousLinearMap.comp_apply, ← hU.map_add, e]
  simpa only [key] using h2

/-- The domain is invariant, and the generator commutes with the group. -/

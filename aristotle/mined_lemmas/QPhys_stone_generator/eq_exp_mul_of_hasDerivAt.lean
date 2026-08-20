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

/-!
# Stone's theorem

A strongly continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)` on a complex Hilbert
space `H` has a self-adjoint (in general unbounded) generator `A`, characterized by
`d/dt (U t x) |_{t=0} = i • A x`.
-/

namespace QPhys

open scoped InnerProductSpace
open Complex (I)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- Each `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- The group law. -/
  map_add : ∀ s t : ℝ, U (s + t) = U s * U t
  /-- Strong continuity. -/
  strong_continuous : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU


theorem eq_exp_mul_of_hasDerivAt {g : ℝ → ℂ} (r : ℝ)
    (hg : ∀ t : ℝ, HasDerivAt g ((r : ℂ) * g t) t) (t : ℝ) :
    g t = Complex.exp ((r : ℂ) * t) * g 0 := by
  set G : ℝ → ℂ := fun t => Complex.exp (-(r : ℂ) * t) * g t with hGdef
  have hofReal : ∀ u : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 u := by
    intro u
    simpa using (Complex.ofRealCLM.hasDerivAt (x := u))
  have hG : ∀ u : ℝ, HasDerivAt G 0 u := by
    intro u
    have h1 : HasDerivAt (fun s : ℝ => -(r : ℂ) * (s : ℂ)) (-(r : ℂ)) u := by
      simpa using (hofReal u).const_mul (-(r : ℂ))
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-(r : ℂ) * (s : ℂ)))
        (Complex.exp (-(r : ℂ) * (u : ℂ)) * (-(r : ℂ))) u := h1.cexp
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(r : ℂ) * (s : ℂ)) * g s)
        (Complex.exp (-(r : ℂ) * (u : ℂ)) * (-(r : ℂ)) * g u
          + Complex.exp (-(r : ℂ) * (u : ℂ)) * ((r : ℂ) * g u)) u := h2.mul (hg u)
    rw [hGdef]
    convert h4 using 1
    ring
  have hdiff : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have hfd : ∀ u : ℝ, fderiv ℝ G u = 0 := by
    intro u
    have := (hG u).hasFDerivAt.fderiv
    simpa using this
  have hconst : G t = G 0 := is_const_of_fderiv_eq_zero hdiff hfd t 0
  have hG0 : G 0 = g 0 := by simp [hGdef]
  rw [hG0] at hconst
  have hkey : Complex.exp (-(r : ℂ) * t) * g t = g 0 := hconst
  calc g t = Complex.exp ((r : ℂ) * t) * (Complex.exp (-(r : ℂ) * t) * g t) := by
        rw [← mul_assoc, ← Complex.exp_add]
        norm_num
    _ = Complex.exp ((r : ℂ) * t) * g 0 := by rw [hkey]

/-! ### Analytic properties -/

section Analysis

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU

/-- For `x` in the domain of the generator, `t ↦ U t x` is differentiable everywhere. -/

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

theorem generator_maximal (hU : IsUnitaryGroup U) {y z : H}
    (h : ∀ x ∈ domain U, ⟪generator U x, y⟫_ℂ = ⟪x, z⟫_ℂ) :
    y ∈ domain U ∧ generator U y = z := by
  have hzc : Continuous fun s : ℝ => U (-s) z := (hU.cont z).comp continuous_neg
  set W : ℝ → H := fun t => ∫ s in (0:ℝ)..t, U (-s) z with hWdef
  have key : ∀ t : ℝ, U (-t) y - y = -Complex.I • W t := by
    intro t
    have hall : ∀ x ∈ domain U, ⟪x, (U (-t) y - y) + Complex.I • W t⟫_ℂ = 0 := by
      intro x hx
      have hderiv : ∀ s : ℝ, HasDerivAt (fun u : ℝ => ⟪U u x, y⟫_ℂ)
          (-Complex.I * ⟪U s x, z⟫_ℂ) s := by
        intro s
        have h1 := (hasDerivAt_all hU hx s).inner ℂ (hasDerivAt_const s y)
        have h2 : ⟪U s (Complex.I • generator U x), y⟫_ℂ = -Complex.I * ⟪U s x, z⟫_ℂ := by
          rw [map_smul, inner_smul_left, Complex.conj_I,
            ← (translate_mem_domain hU hx s).2, h _ (translate_mem_domain hU hx s).1]
        simpa [h2] using h1
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => ⟪U u x, y⟫_ℂ) (f' := fun s : ℝ => -Complex.I * ⟪U s x, z⟫_ℂ)
        (a := 0) (b := t) (fun s _ => hderiv s)
        ((continuous_const.mul ((hU.cont x).inner continuous_const)).intervalIntegrable 0 t)
      have hsplit : (∫ s in (0:ℝ)..t, -Complex.I * ⟪U s x, z⟫_ℂ)
          = -Complex.I * ⟪x, W t⟫_ℂ := by
        have h3 : ∀ s : ℝ, -Complex.I * ⟪U s x, z⟫_ℂ
            = -Complex.I * (innerSL ℂ x) (U (-s) z) := by
          intro s; rw [inner_left_shift hU s x z]; rfl
        simp_rw [h3]
        rw [intervalIntegral.integral_const_mul,
          ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ x)
            (hzc.intervalIntegrable 0 t)]
        rfl
      rw [hsplit, inner_left_shift hU t x y, hU.map_zero] at hFTC
      simp only [ContinuousLinearMap.id_apply] at hFTC
      rw [inner_add_right, inner_sub_right, inner_smul_right]
      linear_combination hFTC
    have hzero := eq_zero_of_inner_domain hU hall
    have := sub_eq_zero.mp ?_
    · exact this
    · rw [sub_eq_iff_eq_add] at *
      linear_combination (norm := module) hzero
  have hW : HasDerivAt W z 0 := by
    have := intervalIntegral.integral_hasDerivAt_right (f := fun s : ℝ => U (-s) z)
      (a := 0) (b := 0) (hzc.intervalIntegrable 0 0)
      hzc.stronglyMeasurable.stronglyMeasurableAtFilter hzc.continuousAt
    simpa [hWdef, hU.map_zero] using this
  have hneg : HasDerivAt (fun t : ℝ => U (-t) y) (-Complex.I • z) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + (-Complex.I) • W t) ((-Complex.I) • z) 0 :=
      (hW.const_smul (-Complex.I)).const_add y
    have h2 : (fun t : ℝ => y + (-Complex.I) • W t) = fun t : ℝ => U (-t) y := by
      funext t
      rw [← key t]
      abel
    rwa [h2] at h1
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (g₁ := fun t : ℝ => U (-t) y)
    (h := fun t : ℝ => -t) 0 (by simpa using hneg) (hasDerivAt_neg 0)
  have hfun : ((fun t : ℝ => U (-t) y) ∘ fun t : ℝ => -t) = fun t : ℝ => U t y := by
    funext t; simp
  rw [hfun] at hcomp
  have hval : ((-1 : ℝ) • (-Complex.I • z)) = Complex.I • z := by
    rw [← Complex.coe_smul, smul_smul]
    norm_num
  rw [hval] at hcomp
  exact ⟨⟨_, hcomp⟩, by rw [generator_eq hcomp, smul_smul]; simp⟩

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group
is a densely defined, linear, self-adjoint operator.  Here self-adjointness means both that
the generator is symmetric on its domain and that it is maximal in the sense that any vector
`y` in the domain of the adjoint already lies in the domain of the generator, with matching
value. -/

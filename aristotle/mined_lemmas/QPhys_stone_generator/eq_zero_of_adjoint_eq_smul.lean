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


theorem eq_zero_of_adjoint_eq_smul (c : ℂ) (hc : c = I ∨ c = -I)
    (f : ((generator U).adjoint).domain) (h : (generator U).adjoint f = c • (f : H)) :
    (f : H) = 0 := by
  obtain ⟨r, hr2, hrc⟩ : ∃ r : ℝ, r * r = 1 ∧ (starRingEnd ℂ) I * c = (r : ℂ) := by
    rcases hc with rfl | rfl
    · exact ⟨1, by norm_num, by simp [Complex.I_mul_I]⟩
    · exact ⟨-1, by norm_num, by simp [Complex.I_mul_I]⟩
  have hdense := dense_domain hU
  have hformal := LinearPMap.adjoint_isFormalAdjoint (T := generator U) hdense
  refine hdense.eq_zero_of_inner_right ?_
  intro ψ
  set g : ℝ → ℂ := fun t => ⟪U t (ψ : H), (f : H)⟫_ℂ with hgdef
  have hgderiv : ∀ t : ℝ, HasDerivAt g ((r : ℂ) * g t) t := by
    intro t
    have h1 := hasDerivAt_of_mem_domain hU ψ t
    have h2 : HasDerivAt (fun _ : ℝ => (f : H)) 0 t := hasDerivAt_const t _
    have h3 := HasDerivAt.inner ℂ h1 h2
    have h5 : U t (generator U ψ) = generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩ :=
      (generator_comm hU ψ t).symm
    have hfa := hformal f ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩
    have h6 : ⟪generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩, (f : H)⟫_ℂ
        = c * g t := by
      have hconj : ⟪generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩, (f : H)⟫_ℂ
          = (starRingEnd ℂ) ⟪(f : H), generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩⟫_ℂ := by
        rw [inner_conj_symm]
      rw [hconj, ← hfa, h, inner_smul_left]
      simp only [hgdef]
      rw [← inner_conj_symm ((f : H)) (U t (ψ : H))]
      simp [mul_comm]
    have h7 : ⟪(I : ℂ) • U t (generator U ψ), (f : H)⟫_ℂ = (r : ℂ) * g t := by
      rw [inner_smul_left, h5, h6, ← mul_assoc, hrc]
    simpa [h7] using h3
  have hbound : ∀ t : ℝ, ‖g t‖ ≤ ‖(ψ : H)‖ * ‖(f : H)‖ := by
    intro t
    have h1 : ‖g t‖ ≤ ‖U t (ψ : H)‖ * ‖(f : H)‖ := norm_inner_le_norm _ _
    rwa [hU.norm_map t (ψ : H)] at h1
  have hg0 : g 0 = 0 := by
    by_contra hne
    set a : ℝ := ‖g 0‖ with hadef
    have hapos : 0 < a := by
      rw [hadef, norm_pos_iff]
      exact hne
    set C : ℝ := ‖(ψ : H)‖ * ‖(f : H)‖ with hCdef
    have hCnonneg : 0 ≤ C := by positivity
    set T : ℝ := (C + 1) / a with hTdef
    have hTpos : 0 < T := by positivity
    have hval := eq_exp_mul_of_hasDerivAt r hgderiv (r * T)
    have hexp : ((r : ℂ) * ((r * T : ℝ) : ℂ)) = ((T : ℝ) : ℂ) := by
      push_cast
      rw [← mul_assoc]
      norm_cast
      rw [hr2, one_mul]
    rw [hexp] at hval
    have hnorm : ‖g (r * T)‖ = Real.exp T * a := by
      rw [hval, norm_mul, hadef]
      congr 1
      rw [← Complex.ofReal_exp]
      simp
    have hle := hbound (r * T)
    rw [hnorm] at hle
    have hexpge : 1 + T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
    have hTa : T * a = C + 1 := by
      rw [hTdef]
      field_simp
    have h9 : (1 + T) * a ≤ Real.exp T * a := mul_le_mul_of_nonneg_right hexpge hapos.le
    nlinarith [h9, hTa, hapos, hle]
  have h0 : U 0 (ψ : H) = (ψ : H) := by rw [hU.apply_zero]; rfl
  rw [hgdef] at hg0
  simpa [h0] using hg0

/-- `A - i` is surjective. -/

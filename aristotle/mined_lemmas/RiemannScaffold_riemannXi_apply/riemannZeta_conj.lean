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

namespace RiemannScaffold


theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) with hg
  have hUopen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
  have hUconn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (by simp [Complex.rank_real_complex]) 1).isPreconnected
  have hzeta : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hgan : AnalyticOnNhd ℂ g ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hz' : (starRingEnd ℂ) z ≠ 1 := by
      intro h
      apply hz
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    have hd : DifferentiableAt ℂ riemannZeta ((starRingEnd ℂ) z) :=
      differentiableAt_riemannZeta hz'
    have := hd.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] g := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      norm_num
    filter_upwards [hmem] with z hz
    exact (riemannZeta_conj_of_one_lt_re hz).symm
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (2 : ℂ).re = (1 : ℂ).re := by rw [h]
    norm_num at this
  have := hzeta.eqOn_of_preconnected_of_eventuallyEq hgan hUconn h2 hev
  have hval := this (Set.mem_compl_singleton_iff.mpr hs)
  rw [hg] at hval
  simp only at hval
  rw [hval, Complex.conj_conj]


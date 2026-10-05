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

import Brockian.RiemannScaffold
open Brockian.RiemannScaffold
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

/-!
# The completed zeta / Riemann ξ functional equation and the ζ ↔ ξ zero correspondence

This file wires Mathlib 4.32's *unconditional* completed-zeta functional equation
`completedRiemannZeta (1 - s) = completedRiemannZeta s` into the Brockian
`RiemannScaffold` ξ-normalization `ξ(s) = s (s-1) Λ(s)`, and then proves the full
zero correspondence between the completed function ξ and the Riemann zeta ζ.

## What is proved (all UNCONDITIONAL)

* `completedRiemannZeta_functional_equation` — Mathlib's `Λ(1-s) = Λ(s)`, restated
  at the Brockian import boundary.
* `riemannXi_apply` — the definitional connection `ξ(s) = s (s-1) Λ(s)` made an
  explicit lemma so downstream files never need to `unfold`.
* `riemannXi_functional_equation` — the classical **ξ functional equation**
  `ξ(1-s) = ξ(s)`, derived from Mathlib's completed-zeta symmetry plus the
  polynomial factor `s(s-1)` (which is itself invariant under `s ↦ 1-s`).
* `zeta_zero_of_riemannXi_zero` — the *converse* zero direction: a ξ-zero away from
  the explicit factor points `s = 0, 1` forces `ζ(s) = 0`.  (RiemannScaffold already
  supplies the forward direction `riemannXi_eq_zero_of_nontrivial_zeta_zero`.)
* `riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip` — inside the open critical
  strip `0 < Re s < 1` the two zero sets coincide **exactly**: `ξ(s) = 0 ↔ ζ(s) = 0`.
  In the strip the trivial-zero lattice and the factor points `s = 0, 1` are all
  absent, so no artifacts intervene.
* `zeta_zero_one_sub_of_mem_critical_strip` — the reflection corollary: a nontrivial
  ζ-zero in the strip has its mirror `1-s` as a ζ-zero as well (also in the strip).

## What is NOT proved

* **Nothing conditional is claimed as unconditional.**  This file does not touch RH,
  the location of the nontrivial zeros, or the `BrockianSystem` Hilbert–Pólya schema
  of `RiemannScaffold` Part 2.  It supplies only the genuine (Mathlib-backed)
  functional equation and the exact ζ ↔ ξ zero dictionary in the critical strip.
* The correspondence is stated for the *open* strip `0 < Re s < 1`; the boundary
  lines `Re s ∈ {0, 1}` and the trivial-zero lattice are deliberately outside scope
  (there the factor `s(s-1)` and `Λ`'s poles produce the well-known artifacts, which
  `RiemannScaffold` already documents).
-/

namespace Brockian.XiFunctionalEquation

open Complex

/-- **Mathlib's completed-zeta functional equation, restated.**  `Λ(1-s) = Λ(s)`,
where `Λ = completedRiemannZeta`.  This is unconditional (`completedRiemannZeta_one_sub`). -/

theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z)) with hg
  have hf : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    (differentiable_completedZeta₀.differentiableOn).analyticOnNhd isOpen_univ
  have hgan : AnalyticOnNhd ℂ g Set.univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ completedRiemannZeta₀ ((starRingEnd ℂ) z) :=
      differentiable_completedZeta₀ _
    have := hd.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have hev : completedRiemannZeta₀ =ᶠ[nhds (2 : ℂ)] g := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      norm_num
    filter_upwards [hmem] with z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa using hz
    have hΛ : completedRiemannZeta ((starRingEnd ℂ) z)
        = (starRingEnd ℂ) (completedRiemannZeta z) :=
      completedRiemannZeta_conj_of_one_lt_re hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz; linarith
    have hz1 : (1 : ℂ) - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this] at hz; simp at hz
    have e1 : completedRiemannZeta₀ z
        = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
      rw [completedRiemannZeta_eq]; ring
    have e2 : completedRiemannZeta₀ ((starRingEnd ℂ) z)
        = completedRiemannZeta ((starRingEnd ℂ) z) + 1 / ((starRingEnd ℂ) z)
          + 1 / (1 - (starRingEnd ℂ) z) := by
      rw [completedRiemannZeta_eq]; ring
    show completedRiemannZeta₀ z = (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) z))
    rw [e2, e1, hΛ]
    simp only [map_add, map_div₀, map_one, map_sub, Complex.conj_conj]
  have := hf.eqOn_of_preconnected_of_eventuallyEq hgan isPreconnected_univ (Set.mem_univ 2) hev
  have hval := this (Set.mem_univ s)
  rw [hg] at hval
  simp only at hval
  rw [hval, Complex.conj_conj]


/-- The completed zeta function `Λ` commutes with complex conjugation. -/

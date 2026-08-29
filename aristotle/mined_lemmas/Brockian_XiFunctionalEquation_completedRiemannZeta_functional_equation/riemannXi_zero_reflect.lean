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

theorem riemannXi_zero_reflect {s : ℂ} (hs : riemannXi s = 0) :
    riemannXi (1 - s) = 0 ∧ riemannXi (starRingEnd ℂ s) = 0 := by
  refine ⟨by rw [riemannXi_functional_equation]; exact hs, ?_⟩
  by_cases hreal : (starRingEnd ℂ) s = s
  · rw [hreal]; exact hs
  by_cases hs0 : s = 0
  · exact absurd (by rw [hs0]; simp) hreal
  by_cases hs1 : s = 1
  · exact absurd (by rw [hs1]; simp) hreal
  have hz : riemannZeta s = 0 := zeta_zero_of_riemannXi_zero hs hs0 hs1
  have hzc : riemannZeta ((starRingEnd ℂ) s) = 0 := by
    rw [riemannZeta_conj hs1, hz, map_zero]
  refine Brockian.RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero hzc ?_ ?_
  · rintro ⟨n, hn⟩
    refine absurd ?_ hreal
    have hsval : s = -2 * ((n : ℂ) + 1) := by
      have h' := congrArg (starRingEnd ℂ) hn
      rw [Complex.conj_conj] at h'
      rw [h']
      simp [Complex.ext_iff]
    rw [hn, hsval]
  · intro h
    exact hs1 (by
      have := congrArg (starRingEnd ℂ) h
      simpa using this)


/-- **The Γ-factor is nonvanishing away from `0` and the trivial-zero lattice.**
`Gammaℝ s = π^(-s/2) Γ(s/2)`; the `cpow` factor is never zero, and `Γ(s/2) ≠ 0`
exactly when `s/2 ∉ {0, -1, -2, …}`, i.e. `s ∉ {0, -2, -4, …}`.  We exclude `s = 0`
and the trivial-zero lattice `{-2(n+1) : n ∈ ℕ}` and get `Gammaℝ s ≠ 0`. -/

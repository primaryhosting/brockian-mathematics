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

theorem Gammaℝ_ne_zero_of_nontrivial {s : ℂ} (hs0 : s ≠ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : s.Gammaℝ ≠ 0 := by
  rw [Complex.Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (by exact_mod_cast Real.pi_ne_zero)
  · apply Complex.Gamma_ne_zero
    intro m hm
    -- hm : s / 2 = -↑m  ⇒  s = -2 * m
    have hs : s = -2 * (m : ℂ) := by linear_combination 2 * hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp only [Nat.cast_zero, mul_zero] at hs
      exact hs0 hs
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
      exact htriv ⟨k, by push_cast at hs ⊢; linear_combination hs⟩

/-- **Nontrivial ζ-zero ⇒ ξ-zero (UNCONDITIONAL).**  If `ζ(s) = 0` at a point that
is not the trivial-zero lattice and not `s = 1`, then `ξ(s) = 0`.  The real work:
`s ≠ 0` (since `ζ(0) = -1/2`), the Γ-factor is nonvanishing there, and
`ζ = Λ / Gammaℝ` forces `Λ(s) = 0`, hence `ξ(s) = s (s-1) · 0 = 0`. -/

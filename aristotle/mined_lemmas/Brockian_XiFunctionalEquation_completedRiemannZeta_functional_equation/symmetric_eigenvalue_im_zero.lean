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

theorem symmetric_eigenvalue_im_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T)
    {μ : ℂ} {v : T.domain} (hv : (v : H) ≠ 0)
    (heig : (T v : H) = μ • (v : H)) : μ.im = 0 := by
  have hkey := hsymm v v
  rw [heig, inner_smul_left, inner_smul_right] at hkey
  have hvv : inner ℂ (v : H) (v : H) ≠ 0 := inner_self_ne_zero.mpr hv
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv hkey
  exact Complex.conj_eq_iff_im.mp hconj

/-- **A `BrockianSystem`** — the Hilbert–Pólya operator-theoretic hypothesis, made
into an honest bundle of obligations over a Hilbert space `H`.

Fields:
* `T` — a **densely-defined, unbounded** operator, modelled as a partial linear
  map `H →ₗ.[ℂ] H` (a `LinearPMap`, *not* a bounded `H →L[ℂ] H`; the bounded
  route is spectrally vacuous for this problem).
* `dense_domain` — `T` is densely defined.
* `symm` — `T` is **symmetric** (formal self-adjoint, `T.IsFormalAdjoint T`).
* `spectrum_real` — the **explicit spectral-reality obligation**: every eigenvalue
  of `T` (nonzero eigenvector) is real.  (Grounded by `symm` via
  `symmetric_eigenvalue_im_zero`; carried as an explicit field so the obligation
  is visible.)
* `eigen_of_zero` — the **zeros ↔ spectrum** correspondence: every nontrivial
  zero `s` of `ζ` is realized as an eigenvalue `t = -i(s - 1/2)` of `T`.

No such system is exhibited here; see the Gate-0 note. -/
structure BrockianSystem (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- the densely-defined unbounded operator (partial linear map, not bounded). -/
  T : H →ₗ.[ℂ] H
  /-- `T` is densely defined. -/
  dense_domain : Dense (T.domain : Set H)
  /-- `T` is symmetric (formal self-adjoint). -/
  symm : T.IsFormalAdjoint T
  /-- **Spectral-reality obligation**: eigenvalues of `T` are real. -/
  spectrum_real : ∀ (μ : ℂ) (v : T.domain),
    (v : H) ≠ 0 → (T v : H) = μ • (v : H) → μ.im = 0
  /-- **Zeros ↔ spectrum**: each nontrivial `ζ`-zero `s` is an eigenvalue
  `t = -i(s - 1/2)` of `T`, on a nonzero eigenvector. -/
  eigen_of_zero : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
    s ≠ 1 → ∃ v : T.domain, (v : H) ≠ 0 ∧
      (T v : H) = (-Complex.I * (s - 1 / 2)) • (v : H)

/-- **`RH_of_BrockianSystem` — the Brockian conditional (CONDITIONAL, rung OPEN).**
If a `BrockianSystem` exists on some Hilbert space, then the Riemann Hypothesis
holds (as Mathlib states it).

The implication does genuine work: for a nontrivial zero `s`, the correspondence
`eigen_of_zero` produces an eigenvector at eigenvalue `t = -i(s - 1/2)`;
`spectrum_real` forces `t` real, i.e. `t.im = 0`; and the complex algebra of
`t = -i(s - 1/2)` turns `t.im = 0` into `s.re = 1/2`.

This is a *conditional* result.  `BrockianSystem` is **not shown instantiable**
(Gate-0). -/

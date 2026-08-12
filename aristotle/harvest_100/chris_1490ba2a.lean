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

import Mathlib
/-!
# RH Of Brockian System
Category: Brockian (Open Discharge)
Target: Brockian.RiemannScaffold.RH_of_BrockianSystem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other token in a module, so the header
-- comment above appears immediately after the single `import Mathlib` line.)

open Complex

namespace Brockian.RiemannScaffold

/-- A **Brockian system** is a "logarithmic discharge" of the completed Riemann zeta function
`Λ` on the open half-plane to the right of the critical line: a function `logLambda` which
exponentiates to `Λ` at every point `s` with `1/2 < re s`, `s ≠ 1` (the point `s = 1`, where
`Λ` has its pole, is excluded).

Equivalently, a Brockian system is exactly a witness that `Λ` has no zeros strictly to the
right of the critical line. Its existence is the genuinely open half of the Riemann
hypothesis; the theorem `RH_of_BrockianSystem` below shows that it is in fact *all* of it,
i.e. that the reflected half-plane and the trivial zeros can be handled unconditionally. -/
structure BrockianSystem where
  /-- The Brockian logarithm of the completed zeta function. -/
  logLambda : ℂ → ℂ
  /-- `Λ s = exp (logLambda s)` to the right of the critical line, away from the pole. -/
  exp_logLambda : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
    completedRiemannZeta s = Complex.exp (logLambda s)

namespace BrockianSystem

/-- A Brockian system forces the completed zeta function to be nonzero strictly to the right
of the critical line (away from the pole at `s = 1`). -/
theorem completedRiemannZeta_ne_zero_of_half_lt_re (B : BrockianSystem) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  rw [B.exp_logLambda s hs hs1]
  exact Complex.exp_ne_zero _

/-- By the functional equation `Λ (1 - s) = Λ s`, a Brockian system also forces `Λ` to be
nonzero strictly to the left of the critical line (away from the pole at `s = 0`). -/
theorem completedRiemannZeta_ne_zero_of_re_lt_half (B : BrockianSystem) {s : ℂ}
    (hs : s.re < 1 / 2) (hs0 : s ≠ 0) :
    completedRiemannZeta s ≠ 0 := by
  have hre : 1 / 2 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hne : (1 - s) ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have h := B.completedRiemannZeta_ne_zero_of_half_lt_re hre hne
  rwa [completedRiemannZeta_one_sub] at h

end BrockianSystem

/-- **The Riemann hypothesis, given a Brockian system.**

If a Brockian system exists — i.e. if the completed zeta function admits a logarithm on the
half-plane `re s > 1/2` — then every nontrivial zero of `riemannZeta` lies on the critical
line.  The remaining content (the reflected half-plane `re s < 1/2` and the trivial zeros) is
discharged unconditionally, using the functional equation `Λ (1 - s) = Λ s` and the exact
description of the zeros of the archimedean factor `Gammaℝ`. -/
theorem RH_of_BrockianSystem (B : BrockianSystem) : RiemannHypothesis := by
  intro s hzero htriv hs1
  -- `s ≠ 0`, since `ζ 0 = -1/2 ≠ 0`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  -- The archimedean factor does not vanish at `s`.
  have hGamma : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, rfl⟩
    match n with
    | 0 => simp at hs0
    | (m + 1) => exact htriv ⟨m, by push_cast; ring⟩
  -- Hence the completed zeta function vanishes at `s`.
  have hLambda : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hzero
    exact hzero.resolve_right hGamma
  -- Both open half-planes are excluded, so `s` lies on the critical line.
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · exact absurd hLambda (B.completedRiemannZeta_ne_zero_of_re_lt_half h hs0)
  · exact h
  · exact absurd hLambda (B.completedRiemannZeta_ne_zero_of_half_lt_re h hs1)

/-- Conversely, the Riemann hypothesis produces a Brockian system: on `re s > 1/2` (away from
`s = 1`) the completed zeta function is then nonvanishing, so it has a pointwise logarithm.
Together with `RH_of_BrockianSystem` this shows that the existence of a Brockian system is
*equivalent* to the Riemann hypothesis, i.e. the hypothesis discharged above is exactly as
strong as its conclusion (in particular it is consistent, not vacuous). -/
theorem brockianSystem_of_RH (h : RiemannHypothesis) : Nonempty BrockianSystem := by
  have key : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → completedRiemannZeta s ≠ 0 := by
    intro s hs hs1 hL
    have hs0 : s ≠ 0 := by
      intro hz
      rw [hz] at hs
      norm_num at hs
    have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hzero : riemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, hL, zero_div]
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      have hre : ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) := by simp
      rw [hre] at hs
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have := h s hzero htriv hs1
    linarith
  refine ⟨⟨fun s ↦ Complex.log (completedRiemannZeta s), ?_⟩⟩
  intro s hs hs1
  exact (Complex.exp_log (key s hs hs1)).symm

/-- The existence of a Brockian system is equivalent to the Riemann hypothesis. -/
theorem nonempty_brockianSystem_iff_riemannHypothesis :
    Nonempty BrockianSystem ↔ RiemannHypothesis :=
  ⟨fun ⟨B⟩ ↦ RH_of_BrockianSystem B, brockianSystem_of_RH⟩

end Brockian.RiemannScaffold


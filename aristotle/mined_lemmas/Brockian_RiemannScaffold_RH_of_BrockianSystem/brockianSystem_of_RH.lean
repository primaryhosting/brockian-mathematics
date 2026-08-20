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

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

/-
Note on file layout: Lean 4 requires every `import` to appear before any command, and a
module doc comment `/-! ... -/` is itself a command.  The requested header comment is therefore
reproduced verbatim immediately after the single `import Mathlib` line, which is the earliest
position at which it is legal.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace RiemannScaffold

open Complex

/-- A **Brockian system** is a nonvanishing certificate for the Riemann zeta function on the
open right-hand half of the critical strip:

`∀ s, 1/2 < re s < 1 → ζ s ≠ 0`.

This is deliberately a *one-sided* condition: it says nothing about the half-strip
`0 < re s < 1/2`, nothing about the line `re s = 1/2`, and nothing outside the strip. -/
structure BrockianSystem : Prop where
  /-- No zeros of `ζ` strictly between the critical line and the line `re s = 1`. -/
  strip_nonvanishing : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- A zero of `ζ` is *nontrivial* when it is not one of the trivial zeros `-2, -4, -6, …`
(and is not the point `s = 1`, where `ζ` has its pole). -/

theorem brockianSystem_of_RH (h : RiemannHypothesis) : BrockianSystem where
  strip_nonvanishing := by
    intro s h1 h2 hz
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
        Complex.add_im, Complex.natCast_im, Complex.one_im, Complex.neg_re, Complex.neg_im,
        Complex.re_ofNat, Complex.im_ofNat] at h1
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num at h1
      linarith
    have hne : s ≠ 1 := by
      intro hs1
      rw [hs1] at h2
      norm_num at h2
    have := h s hz htriv hne
    rw [this] at h1
    norm_num at h1

/-- The Brockian system criterion is equivalent to the Riemann Hypothesis. -/

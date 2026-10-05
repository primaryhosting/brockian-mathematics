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
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-!
## Step 1: nonvanishing to the right of the critical line

The Brockian system only supplies nonvanishing inside the strip; on `re s ≥ 1` we use the
classical (unconditional) nonvanishing theorem.
-/

theorem zeta_ne_zero_of_half_lt_re (B : BrockianSystem) {s : ℂ} (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 := by
  rcases lt_or_ge s.re 1 with h | h
  · exact B.strip_nonvanishing s hs h
  · exact riemannZeta_ne_zero_of_one_le_re h

/-!
## Step 2: the archimedean factor is nonzero at a nontrivial zero
-/

theorem Gammaℝ_ne_zero_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) :
    Gammaℝ s ≠ 0 := by
  obtain ⟨hz, htriv, -⟩ := hs
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, rfl⟩
  match n with
  | 0 =>
      rw [show (-(2 * ((0 : ℕ) : ℂ)) : ℂ) = 0 by norm_num, riemannZeta_zero] at hz
      norm_num at hz
  | (m + 1) =>
      exact htriv ⟨m, by push_cast; ring⟩

/-!
## Step 3: a nontrivial zero of `ζ` is a zero of the completed zeta function `Λ`

Here the exclusion of the trivial zeros is essential: at `s = -2n` the factor `Gammaℝ` has a
pole, and `Λ` does not vanish there.
-/

theorem completedZeta_eq_zero_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) :
    completedRiemannZeta s = 0 := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_isNontrivialZero hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 := hs.1
    rw [riemannZeta_zero] at h0
    norm_num at h0
  have h := riemannZeta_def_of_ne_zero hs0
  rw [hs.1, eq_comm, div_eq_zero_iff] at h
  exact h.resolve_right hG

/-!
## Step 4: the reflected point `1 - s` is again a zero of `ζ`

This is the sub-lemma that a conditional scaffold would name as a hypothesis: instead of
assuming a reflection principle we derive it from the functional equation
`Λ (1 - s) = Λ s` for the completed zeta function.
-/

theorem zeta_one_sub_eq_zero_of_isNontrivialZero {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (1 - s) = 0 := by
  have hL : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact completedZeta_eq_zero_of_isNontrivialZero hs
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero_of_ne (Ne.symm hs.2.2)
  rw [riemannZeta_def_of_ne_zero h1, hL, zero_div]

/-!
## The main theorem
-/

/-- **Riemann Hypothesis from a Brockian system.**

If a Brockian system exists — i.e. `ζ` has no zeros in the open half-strip
`1/2 < re s < 1` — then every nontrivial zero of `ζ` lies on the critical line.

The statement carries no hypotheses beyond the Brockian system itself: the reflection step,
which relates a hypothetical zero with `re s < 1/2` to one with `re s > 1/2`, is proved here
from the functional equation rather than assumed. -/
theorem RH_of_BrockianSystem (B : BrockianSystem) : RiemannHypothesis := by
  intro s hz htriv hne
  have hs : IsNontrivialZero s := ⟨hz, htriv, hne⟩
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · exfalso
    have hzero : riemannZeta (1 - s) = 0 := zeta_one_sub_eq_zero_of_isNontrivialZero hs
    have hre : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact zeta_ne_zero_of_half_lt_re B hre hzero
  · exact h
  · exact absurd hz (zeta_ne_zero_of_half_lt_re B h)

/-- Conversely, the Riemann Hypothesis supplies a Brockian system.  Together with
`RH_of_BrockianSystem` this shows that the hypothesis fed to the main theorem is *exactly*
equivalent to RH: it is neither a disguised triviality nor a strictly stronger assumption. -/
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
theorem brockianSystem_iff_RH : BrockianSystem ↔ RiemannHypothesis :=
  ⟨RH_of_BrockianSystem, brockianSystem_of_RH⟩

end RiemannScaffold
end Brockian


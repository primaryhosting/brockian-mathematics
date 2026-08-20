/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace Frontier

/-- A *nontrivial zero* of the Riemann zeta function: a zero lying in the open critical
strip `0 < Re s < 1`.  All other zeros of `ζ` are the *trivial* zeros `s = -2, -4, -6, …`
(see `Frontier.eq_trivial_zero_of_zero_of_re_le_zero` and
`Frontier.riemannHypothesis_iff`). -/

theorem riemannHypothesis_iff : RiemannHypothesis ↔ CriticalLine := by
  constructor
  · intro h s hs
    obtain ⟨hz, h0, h1⟩ := hs
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩
      simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.one_re,
        Complex.add_im, Complex.natCast_im, Complex.one_im, Complex.neg_re,
        Complex.neg_im] at h0
      norm_num at h0
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · intro h'
      rw [h'] at h1
      simp only [Complex.one_re] at h1
      linarith
  · intro h s hz htriv _
    rcases le_or_gt s.re 0 with hle | hgt
    · exact absurd (eq_trivial_zero_of_zero_of_re_le_zero hz hle) htriv
    · rcases lt_or_ge s.re 1 with hlt1 | hge1
      · exact h s ⟨hz, hgt, hlt1⟩
      · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)

end Frontier

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


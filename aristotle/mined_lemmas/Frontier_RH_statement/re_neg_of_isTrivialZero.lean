import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex
open scoped Real

namespace Frontier

/-- `s` is a *trivial* zero of the Riemann zeta function, i.e. `s = -2, -4, -6, …`. -/

lemma re_neg_of_isTrivialZero {s : ℂ} (hs : IsTrivialZero s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := hs
  simp only [mul_re, neg_re, neg_im, re_ofNat, im_ofNat, add_re, natCast_re, one_re, add_im,
    natCast_im, one_im]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- In the half-plane `Re s ≤ 0` the only zeros of `ζ` are the trivial ones.  This is the
substantive input coming from the functional equation together with the nonvanishing of `ζ`
on `Re s ≥ 1`. -/

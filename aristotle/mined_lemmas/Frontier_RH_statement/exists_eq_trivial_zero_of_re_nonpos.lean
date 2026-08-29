/-
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 requires `import` commands to
-- precede any module docstring; the docstring form is repeated immediately after the import.)

import Mathlib

/-!
# RH Statement
Category: Frontier — Moonshot
Target: Frontier.RH_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real

namespace Frontier

/-
The Riemann Hypothesis itself is an open problem, so `RH_statement` is *stated* here (and shown
to agree with Mathlib's `RiemannHypothesis`) rather than proved. What is proved below,
unconditionally and axiom-cleanly, is:

* the zero-free regions `Re s ≤ 0` (only trivial zeros) and `Re s ≥ 1` (no zeros), i.e. every
  nontrivial zero lies in the critical strip `0 < Re s < 1`;
* the symmetry `s ↦ 1 - s` of the set of nontrivial zeros, coming from the functional equation;
* the resulting reduction: RH is equivalent to the one-sided statement that no nontrivial zero
  has `Re s > 1/2` (and, symmetrically, to `Re s < 1/2` being excluded).
-/

/-- A complex number `s` is a *nontrivial zero* of the Riemann zeta function if `ζ s = 0`,
`s` is not one of the trivial zeros `-2, -4, -6, …`, and `s ≠ 1` (the point `s = 1` is a pole,
where Mathlib's `riemannZeta` takes a junk value). -/

theorem exists_eq_trivial_zero_of_re_nonpos {s : ℂ} (hs : riemannZeta s = 0) (hre : s.re ≤ 0) :
    ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by simp [hw, Complex.sub_re]; linarith
  have hw1 : w ≠ 1 := by
    simp only [hw, ne_eq, sub_eq_self]
    exact hs0
  have hwn : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    rw [hn] at hwre
    simp at hwre
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hzw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have key := riemannZeta_one_sub hwn hw1
  have h1w : (1 : ℂ) - w = s := by rw [hw]; ring
  rw [h1w, hs] at key
  have hcos : Complex.cos (π * w / 2) = 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hpow : ((2 * (π : ℂ)) ^ (-w)) ≠ 0 := by
      apply Complex.cpow_ne_zero_iff_of_exponent_ne_zero ?_ |>.mpr
      · exact_mod_cast mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      · intro h
        rw [neg_eq_zero] at h
        exact hw1 (by rw [h] at hwre; simp at hwre; linarith)
    have hgam : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hprod := key.symm
    simp only [mul_eq_zero] at hprod
    tauto
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hwk : w = 2 * (k : ℂ) + 1 := by
    field_simp at hk
    linear_combination hk
  have hk1 : 1 ≤ k := by
    by_contra hcon
    push_neg at hcon
    have hk0 : k ≤ 0 := by omega
    have : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    have hkr : (k : ℝ) ≤ 0 := by exact_mod_cast hk0
    rw [this] at hwre
    have : (k : ℝ) = 0 := by linarith
    have : k = 0 := by exact_mod_cast this
    subst this
    exact hw1 (by rw [hwk]; norm_num)
  refine ⟨(k - 1).toNat, ?_⟩
  have hs' : s = 1 - w := by rw [hw]; ring
  rw [hs', hwk]
  have : ((k - 1).toNat : ℂ) = (k : ℂ) - 1 := by
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast congrArg (fun m : ℤ => (m : ℂ)) this
  rw [this]
  ring

/-- A nontrivial zero has positive real part (there are no zeros with `Re s ≤ 0` other than the
trivial ones). -/

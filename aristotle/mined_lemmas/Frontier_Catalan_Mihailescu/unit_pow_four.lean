import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

lemma unit_pow_four {u : GaussianInt} (hu : IsUnit u) : u ^ 4 = 1 := by
  have hn : u.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.2 hu
  have hnorm : u.norm = u.re * u.re + u.im * u.im := by rw [Zsqrtd.norm_def]; ring
  have hpos : (0:ℤ) ≤ u.norm := by
    rw [hnorm]; nlinarith [mul_self_nonneg u.re, mul_self_nonneg u.im]
  have h1 : u.re * u.re + u.im * u.im = 1 := by rw [← hnorm]; omega
  have hzero : u.re = 0 ∨ u.im = 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h2, h3⟩ := hc
    have ha := one_le_mul_self h2
    have hb := one_le_mul_self h3
    omega
  have hsq : u ^ 2 = (((u.re * u.re - u.im * u.im : ℤ)) : GaussianInt) := by
    have hAB : u.re * u.im = 0 := by rcases hzero with h | h <;> simp [h]
    apply Zsqrtd.ext <;>
      simp only [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;>
      nlinarith [hAB]
  have h4 : (u.re * u.re - u.im * u.im) ^ 2 = 1 := by
    rcases hzero with h | h <;> rw [h] at h1 ⊢ <;> nlinarith
  calc u ^ 4 = (u ^ 2) ^ 2 := by ring
  _ = (((u.re * u.re - u.im * u.im : ℤ)) : GaussianInt) ^ 2 := by rw [hsq]
  _ = 1 := by rw [← Int.cast_pow, h4]; norm_num

/-- If `Y` is even then `Y + i` and `Y - i` are coprime Gaussian integers. -/

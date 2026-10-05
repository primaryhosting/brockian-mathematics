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

lemma gauss_coprime {Y : ℤ} (hY : Even Y) :
    IsCoprime (⟨Y, 1⟩ : GaussianInt) (⟨Y, -1⟩ : GaussianInt) := by
  obtain ⟨m, rfl⟩ := hY
  have h2 : IsCoprime ((m + m) ^ 2 + 1 : ℤ) 2 := ⟨1, -(2 * m ^ 2), by ring⟩
  have h4 : IsCoprime ((m + m) ^ 2 + 1 : ℤ) 4 := by
    have h := h2.pow_right (n := 2); norm_num at h; exact h
  obtain ⟨A, B, hAB⟩ := h4
  set s : GaussianInt := ⟨m + m, 1⟩ with hs
  set t : GaussianInt := ⟨m + m, -1⟩ with ht
  have hst : s * t = ((((m + m) ^ 2 + 1 : ℤ)) : GaussianInt) := by
    simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast]
    constructor <;> ring
  have hsub : (4 : GaussianInt) = -(s - t) ^ 2 := by
    simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, pow_two, Zsqrtd.re_neg,
      Zsqrtd.im_neg, Zsqrtd.re_sub, Zsqrtd.im_sub]
    constructor <;> ring_nf <;> rfl
  have hcast : ((A : GaussianInt)) * ((((m + m) ^ 2 + 1 : ℤ)) : GaussianInt)
      + ((B : GaussianInt)) * 4 = 1 := by
    have h := congrArg (fun n : ℤ => ((n : GaussianInt))) hAB
    push_cast at h
    push_cast
    linear_combination h
  rw [← hst, hsub] at hcast
  exact ⟨(A : GaussianInt) * t - (B : GaussianInt) * s + 2 * (B : GaussianInt) * t,
    -(B : GaussianInt) * t, by linear_combination hcast⟩


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

lemma im_pow_add_gi (a : ℤ) (r : ℕ) :
    (((a : GaussianInt) + gi) ^ r).im
      = ∑ k ∈ Finset.range (r + 1), a ^ k * (r.choose k : ℤ) * eps (r - k) := by
  rw [add_pow]
  have hsum : (((∑ k ∈ Finset.range (r + 1),
        (a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt))).im)
      = ∑ k ∈ Finset.range (r + 1),
          imHom ((a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt)) :=
    map_sum imHom _ _
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  show ((a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt)).im = _
  have h1 : ((a : GaussianInt)) ^ k = ((a ^ k : ℤ) : GaussianInt) := by push_cast; ring
  have h2 : ((r.choose k : GaussianInt)) = (((r.choose k : ℤ)) : GaussianInt) := by
    push_cast; ring
  rw [h1, h2]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, eps]
  ring

/-! ## The 2-adic key lemma -/


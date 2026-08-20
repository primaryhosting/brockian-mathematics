import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_bounded {x y p q : ℕ} (hx : 1 < x) (hy : 1 < y) (hp : 1 < p) (hq : 1 < q)
    (hbound : x ^ p ≤ 10000) (h : x ^ p = y ^ q + 1) : x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  have hxb : x < 101 := by
    by_contra hc
    push_neg at hc
    have h1 : x ^ 2 ≤ x ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (101:ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at h2
    omega
  have hpb : p < 14 := by
    by_contra hc
    push_neg at hc
    have h1 : (2:ℕ) ^ p ≤ x ^ p := Nat.pow_le_pow_left (by omega) p
    have h2 : (2:ℕ) ^ 14 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hc
    norm_num at h2
    omega
  have hyq : y ^ q ≤ 10000 := by omega
  have hyb : y < 101 := by
    by_contra hc
    push_neg at hc
    have h1 : y ^ 2 ≤ y ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (101:ℕ) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at h2
    omega
  have hqb : q < 14 := by
    by_contra hc
    push_neg at hc
    have h1 : (2:ℕ) ^ q ≤ y ^ q := Nat.pow_le_pow_left (by omega) q
    have h2 : (2:ℕ) ^ 14 ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hc
    norm_num at h2
    omega
  exact catalan_check x (Finset.mem_range.2 hxb) p (Finset.mem_range.2 hpb) hx hp hbound
    y (Finset.mem_range.2 hyb) q (Finset.mem_range.2 hqb) hy hq h

/-- If `z ^ n = v < 4` with `z > 1` and `n ≥ 1`, then `n = 1` and `z = v`. -/

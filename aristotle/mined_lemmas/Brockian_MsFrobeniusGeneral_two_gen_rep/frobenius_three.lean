import Mathlib
namespace Brockian.MsFrobeniusGeneral

/-- Two-generator case: if `p` and `q` are coprime and `p > 0`, every `n ≥ p * q`
    is a nonnegative combination of `p` and `q`. -/

theorem frobenius_three (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hg : Nat.gcd a (Nat.gcd b c) = 1) :
    ∃ N : ℕ, ∀ m : ℕ, N < m → ∃ x y z : ℕ, a * x + b * y + c * z = m := by
  -- Let g = gcd(b, c)
  let g := Nat.gcd b c
  -- b' = b / g, c' = c / g, so b = g * b', c = g * c', and gcd(b', c') = 1
  let b' := b / g
  let c' := c / g
  -- Key facts about g, b', c'
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left c hb
  have hb_eq : b = g * b' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left b c)).symm
  have hc_eq : c = g * c' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right b c)).symm
  have hcop_bc' : Nat.Coprime b' c' := by
    apply Nat.coprime_div_gcd_div_gcd hg_pos
  -- We have gcd(a, g) = 1
  have hcop_ag : Nat.Coprime a g := hg
  -- Set N = g * (b' * c' + a)
  use g * (b' * c' + a)
  intro m hm
  -- First, use exists_small_mul_add to write m = a * z + g * k with z < g
  have hm_bound : a * g ≤ m := by
    nlinarith
  obtain ⟨z, k, hz, hm_eq⟩ := exists_small_mul_add g a m hg_pos hcop_ag hm_bound
  -- Now we need k >= b' * c' to apply two_gen_rep b' c'
  have hk_bound : b' * c' ≤ k := by
    nlinarith
  -- Use two_gen_rep to write k = b' * y + c' * z'
  have hb'_pos : 0 < b' := by
    nlinarith
  have hc'_pos : 0 < c' := by
    nlinarith
  obtain ⟨y, z', hb'c'_eq⟩ := two_gen_rep b' c' k hb'_pos hcop_bc' hk_bound
  -- Now combine: m = a * z + g * k = a * z + g * (b' * y + c' * z') = a * z + b * y + c * z'
  use z, y, z'
  calc a * z + b * y + c * z'
      = a * z + g * b' * y + g * c' * z' := by rw [hb_eq, hc_eq]
    _ = a * z + g * (b' * y + c' * z') := by ring
    _ = a * z + g * k := by rw [hb'c'_eq]
    _ = m := hm_eq

end Brockian.MsFrobeniusGeneral


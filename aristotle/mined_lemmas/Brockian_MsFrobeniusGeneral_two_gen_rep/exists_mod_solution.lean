import Mathlib
namespace Brockian.MsFrobeniusGeneral

/-- Two-generator case: if `p` and `q` are coprime and `p > 0`, every `n ≥ p * q`
    is a nonnegative combination of `p` and `q`. -/

lemma exists_mod_solution (g c m : ℕ) (hg : 0 < g) (hcop : Nat.Coprime c g) :
    ∃ z : ℕ, z < g ∧ (c * z) % g = m % g := by
  by_cases hg1 : g = 1
  · use 0
    simp [hg1, Nat.mod_one]
  · -- g > 1, use the multiplicative inverse
    have hg1' : 1 < g := Nat.lt_of_le_of_ne hg (Ne.symm hg1)
    obtain ⟨d, hd_lt, hd_eq⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hg1'
    use m * d % g
    refine ⟨Nat.mod_lt _ hg, ?_⟩
    -- (c * (m * d % g)) % g = (c * m * d) % g = (m * (c * d)) % g = (m * 1) % g = m % g
    have h1 : (c * (m * d % g)) % g = (c * (m * d)) % g := by
      have : m * d = m * d % g + g * (m * d / g) := (Nat.mod_add_div (m * d) g).symm
      calc (c * (m * d % g)) % g = (c * (m * d % g) + g * (c * (m * d / g))) % g := by
             rw [Nat.add_mul_mod_self_left]
        _ = (c * ((m * d % g) + g * (m * d / g))) % g := by ring_nf
        _ = (c * (m * d)) % g := by rw [← this]
    rw [h1]
    have h2 : (c * (m * d)) % g = (m * (c * d)) % g := by ring_nf
    rw [h2]
    have h3 : (m * (c * d)) % g = (m * (c * d % g)) % g := by
      conv_lhs => rw [← Nat.mod_add_div (c * d) g]
      rw [Nat.mul_add, mul_left_comm m g]
      simp [Nat.add_mul_mod_self_left]
    rw [h3, hd_eq, Nat.mul_one]

/-- If `c` is coprime to `g > 0`, then any `m ≥ c * g` can be written as `c * z + g * k`
    with `z < g`. -/

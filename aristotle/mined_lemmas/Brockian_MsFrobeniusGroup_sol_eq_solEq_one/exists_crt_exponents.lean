import Mathlib

/-!
# Frobenius's theorem

For a finite group `G` and any `n`, `gcd (n, |G|)` divides the number of solutions of `xⁿ = 1`.

The proof is organised as follows.

* `sol G n` is the number of solutions of `x ^ n = 1`, `solEq n y` the number of solutions of
  `x ^ n = y`.
* `solEq_prime_pow_dvd`: if `y` has order `p ^ k` with `k ≥ 1`, then `p ^ a` divides the number
  of solutions of `x ^ (p ^ a) = y`.  (Each solution generates a cyclic group of order `p ^ (a+k)`
  containing `y`, and each such cyclic subgroup contains exactly `p ^ a` solutions.)
* Consequently `sol G (p ^ (a+1)) ≡ sol G (p ^ a) [MOD p ^ a]`, so all the numbers
  `sol G (p ^ b)` for `b ≥ a` are congruent mod `p ^ a`.
* `sol_mul_eq_sum`: writing `n = p ^ α * u` with `p ∤ u`, decomposing an element into its
  `p`-part and `p'`-part gives `sol G n = ∑_{w ^ u = 1} sol (centralizer w) (p ^ α)`.
* `pPart_dvd_sol_pPart` (the key theorem): the number of `p`-elements of `G` is divisible by the
  order of a Sylow `p`-subgroup.  This follows by induction on `|G|` from the previous identity
  applied to `n = |G|`, grouping the sum into conjugacy classes.
* Everything is then assembled.
-/

namespace Brockian.MsFrobeniusGroup

open scoped Classical
open Finset

universe u

variable {G : Type u} [Group G]

/-- The number of solutions of `x ^ n = 1` in `G`. -/

lemma exists_crt_exponents {p α u : ℕ} (hp : p.Prime) (hu : ¬ p ∣ u) (hu0 : 0 < u) :
    ∃ e f : ℕ, p ^ α ∣ e ∧ u ∣ f ∧ e ≡ 1 [MOD u] ∧ f ≡ 1 [MOD p ^ α] ∧
      (e + f) ≡ 1 [MOD p ^ α * u] := by
  have hcop : Nat.Coprime (p ^ α) u := by
    have : Nat.Coprime p u := hp.coprime_iff_not_dvd.mpr hu
    exact Nat.Coprime.pow_left α this
  -- Use Int.gcd_eq_gcd_ab to get Bezout coefficients
  have hgcd : Int.gcd (p ^ α) u = 1 := by exact_mod_cast hcop
  have zabr := Int.gcd_eq_gcd_ab (p ^ α) u
  rw [hgcd] at zabr
  -- zabr : 1 = (p^α) * gcdA + u * gcdB
  set a := Int.gcdA (p ^ α : ℕ) u
  set b := Int.gcdB (p ^ α : ℕ) u
  have zab : ↑p ^ α * a + ↑u * b = 1 := by
    have hpc : ((p ^ α : ℕ) : ℤ) = (p : ℤ) ^ α := by push_cast; ring
    simp only [a, b, hpc]
    push_cast at zabr
    linarith
  -- From zab: a * p^α ≡ 1 [MOD u] and b * u ≡ 1 [MOD p^α]
  have ha_mod : ↑p ^ α * a ≡ 1 [ZMOD ↑u] := by
    rw [Int.modEq_iff_dvd]
    have : (1 : ℤ) - ↑p ^ α * a = ↑u * b := by linarith
    rw [this]
    exact dvd_mul_right _ _
  have hb_mod : ↑u * b ≡ 1 [ZMOD ↑p ^ α] := by
    rw [Int.modEq_iff_dvd]
    have : (1 : ℤ) - ↑u * b = ↑p ^ α * a := by linarith
    rw [this]
    exact dvd_mul_right _ _
  -- Define e = (a % u).toNat * p^α and f = (b % p^α).toNat * u
  set k := (a % ↑u).toNat with hk_def
  set m := (b % ↑(p ^ α)).toNat with hm_def
  use k * p ^ α, m * u
  -- First prove k * p ^ α ≡ 1 [MOD u]
  have hk_pa : k * p ^ α ≡ 1 [MOD u] := by
    have hu_pos : (0 : ℤ) < u := by positivity
    have h_anonneg : 0 ≤ a % ↑u := Int.emod_nonneg _ hu_pos.ne'
    have hk_eq : (k : ℤ) = a % ↑u := Int.toNat_of_nonneg h_anonneg
    have : (k : ℤ) * p ^ α ≡ a % ↑u * p ^ α [ZMOD ↑u] := by simp [hk_eq]
    have h2 : (a % ↑u : ℤ) * p ^ α ≡ a * p ^ α [ZMOD ↑u] := by
      exact Int.ModEq.mul_right _ (Int.emod_emod_of_dvd a (dvd_refl _))
    have h3 : (a : ℤ) * p ^ α ≡ 1 [ZMOD ↑u] := by simpa [mul_comm] using ha_mod
    have h4 : (k : ℤ) * p ^ α ≡ 1 [ZMOD ↑u] := this.trans (h2.trans h3)
    rw [← Int.natCast_modEq_iff]
    convert h4 using 2 <;> (push_cast; try ring)
  -- Then prove m * u ≡ 1 [MOD p^α]
  have hm_u : m * u ≡ 1 [MOD p ^ α] := by
    have hp_pos : (0 : ℕ) < p := hp.pos
    have hpa_pos : (0 : ℤ) < p ^ α := by positivity
    have h_banonneg : 0 ≤ b % ↑(p ^ α) := Int.emod_nonneg _ hpa_pos.ne'
    have hm_eq : (m : ℤ) = b % ↑(p ^ α) := Int.toNat_of_nonneg h_banonneg
    have : (m : ℤ) * u ≡ b % ↑(p ^ α) * u [ZMOD ↑p ^ α] := by simp [hm_eq]
    have h2 : (b % ↑(p ^ α) : ℤ) * u ≡ b * u [ZMOD ↑p ^ α] := Int.ModEq.mul_right _ (Int.emod_emod_of_dvd b (dvd_refl _))
    have h3 : (b : ℤ) * u ≡ 1 [ZMOD ↑p ^ α] := by simpa [mul_comm] using hb_mod
    have h4 : (m : ℤ) * u ≡ 1 [ZMOD ↑p ^ α] := this.trans (h2.trans h3)
    simp only [Int.ModEq] at h4
    exact_mod_cast h4
  refine ⟨dvd_mul_left _ _, dvd_mul_left _ _, hk_pa, hm_u, ?_⟩
  -- Goal: k * p ^ α + m * u ≡ 1 [MOD p^α * u]
  · -- k * p^α ≡ 1 [MOD u] and k * p^α ≡ 0 [MOD p^α]
    -- m * u ≡ 1 [MOD p^α] and m * u ≡ 0 [MOD u]
    -- So k * p^α + m * u ≡ 1 [MOD p^α] and ≡ 1 [MOD u]
    -- By CRT, k * p^α + m * u ≡ 1 [MOD p^α * u]
    have hk0 : k * p ^ α ≡ 0 [MOD p ^ α] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    have hm0 : m * u ≡ 0 [MOD u] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left _ _)
    have hpa_pos : 0 < p ^ α := Nat.one_le_pow _ _ hp.pos
    have hu_pos : 0 < u := hu0
    -- Prove k * p^α + m * u ≡ 1 [MOD p^α]
    have hab_pa : k * p ^ α + m * u ≡ 1 [MOD p ^ α] := by
      calc k * p ^ α + m * u ≡ 0 + 1 [MOD p ^ α] := Nat.ModEq.add hk0 hm_u
        _ = 1 := by ring
    -- Prove k * p^α + m * u ≡ 1 [MOD u]
    have hab_u : k * p ^ α + m * u ≡ 1 [MOD u] := by
      calc k * p ^ α + m * u ≡ 1 + 0 [MOD u] := Nat.ModEq.add hk_pa hm0
        _ = 1 := by ring
    -- By CRT: since gcd(p^α, u) = 1, a ≡ b [MOD p^α] and a ≡ b [MOD u] implies a ≡ b [MOD p^α * u]
    rw [Nat.ModEq] at hab_pa hab_u ⊢
    -- Need to show: (k * p^α + m * u) % (p^α * u) = 1 % (p^α * u)
    -- We have: (k * p^α + m * u) % p^α = 1 % p^α and (k * p^α + m * u) % u = 1 % u
    -- By CRT this implies (k * p^α + m * u) % (p^α * u) = 1 % (p^α * u)
    -- hab_pa : (k * p^α + m*u) % p^α = 1 % p^α
    -- hab_u : (k * p^α + m*u) % u = 1 % u
    -- Need: (k * p^α + m*u) % (p^α * u) = 1 % (p^α * u)
    -- hab_pa : (k * p^α + m*u) % p^α = 1 % p^α
    -- hab_u : (k * p^α + m*u) % u = 1 % u
    -- Need: (k * p^α + m*u) % (p^α * u) = 1 % (p^α * u)
    -- Use Int conversion
    have hi : (k * p ^ α + m * u : ℤ) % (p ^ α * u : ℤ) = (1 : ℤ) % (p ^ α * u : ℤ) := by
      have hab_pa' : (k * p ^ α + m * u : ℤ) ≡ 1 [ZMOD p ^ α] := by
        rw [Int.ModEq]; exact_mod_cast hab_pa
      have hab_u' : (k * p ^ α + m * u : ℤ) ≡ 1 [ZMOD u] := by
        rw [Int.ModEq]; exact_mod_cast hab_u
      -- Need: p^α * u ∣ (k*p^α + m*u - 1)
      -- From hab_pa': p^α ∣ (k*p^α + m*u - 1)
      -- From hab_u': u ∣ (k*p^α + m*u - 1)
      -- Since gcd(p^α, u) = 1, p^α * u ∣ (k*p^α + m*u - 1)
      -- Int.modEq_iff_dvd: a ≡ b [ZMOD n] ↔ n ∣ (b - a)
      rw [Int.modEq_iff_dvd] at hab_pa' hab_u'
      have hcop' : IsCoprime (p ^ α : ℤ) u := by exact_mod_cast hcop
      have hdiv : (p ^ α : ℤ) * u ∣ (1 - (k * p ^ α + m * u)) := hcop'.mul_dvd hab_pa' hab_u'
      have hdiv' : (p ^ α : ℤ) * u ∣ (k * p ^ α + m * u - 1) := by
        exact dvd_sub_comm.mp hdiv
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact Int.emod_eq_zero_of_dvd hdiv'
    exact_mod_cast hi

/-- If `x ^ m = 1` and `m ∣ k` then `x ^ k = 1`. -/

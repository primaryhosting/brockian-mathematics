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

lemma card_fiber_zpowers [Fintype G] {p a k : ℕ} (hp : p.Prime) {y : G} (hk : 0 < k)
    (hy : orderOf y = p ^ k) {x₀ : G} (hx₀ : x₀ ^ (p ^ a) = y) :
    (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀)).card
      = p ^ a := by
  -- First establish that orderOf x₀ = p^(a+k)
  have hord : orderOf x₀ = p ^ (a + k) := orderOf_of_pow_eq hp hk hy hx₀
  let S := (univ.filter (fun x : G => x ^ (p ^ a) = y ∧ Subgroup.zpowers x = Subgroup.zpowers x₀))
  -- Define the map from Fin (p^a) to our set
  let f : Fin (p ^ a) → G := fun t => x₀ ^ (1 + t.val * p ^ k)
  -- Show that f maps into S
  have hf_in_S : ∀ t : Fin (p ^ a), f t ∈ S := by
    intro t
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- Show (f t) ^ (p ^ a) = y
      simp only [f]
      rw [← pow_mul, add_mul, one_mul]
      rw [pow_add, hx₀]
      rw [mul_assoc]
      have h1 : p ^ k * p ^ a = p ^ (a + k) := by ring
      rw [h1]
      have h2 : x₀ ^ (p ^ (a + k)) = 1 := by rw [← hord, pow_orderOf_eq_one]
      rw [mul_comm, pow_mul, h2, one_pow, mul_one]
    · -- Show zpowers (f t) = zpowers x₀
      -- This follows because gcd(1 + t*p^k, p^(a+k)) = 1
      apply le_antisymm
      · -- zpowers (f t) ≤ zpowers x₀
        apply Subgroup.zpowers_le.mpr
        simp only [f]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x₀) _
      · -- zpowers x₀ ≤ zpowers (f t)
        apply Subgroup.zpowers_le.mpr
        -- Need to show x₀ ∈ zpowers (x₀^(1 + t*p^k))
        -- This is true because gcd(1 + t*p^k, p^(a+k)) = 1
        simp only [f]
        -- x₀ = (x₀^(1 + t*p^k))^m for some m with m*(1 + t*p^k) ≡ 1 (mod p^(a+k))
        have hcop : Nat.Coprime (1 + t.val * p ^ k) (p ^ (a + k)) := by
          apply Nat.Coprime.pow_right
          rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
          have hdvd : p ∣ t.val * p ^ k := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
          rw [Nat.dvd_add_left hdvd]
          exact Nat.Prime.not_dvd_one hp
        -- Use Euler's theorem: a^(φ(n)) ≡ 1 (mod n) when gcd(a, n) = 1
        let n := orderOf x₀
        have hn : n = p ^ (a + k) := hord
        have hnpos : 0 < n := Nat.pos_of_ne_zero (hn.symm ▸ pow_ne_zero _ hp.ne_zero)
        have hcop' : Nat.Coprime (1 + t.val * p ^ k) n := by rw [hn]; exact hcop
        -- The inverse of (1 + t*p^k) mod n is (1 + t*p^k)^(φ(n) - 1)
        have h_tot : (1 + t.val * p ^ k) ^ Nat.totient n ≡ 1 [MOD n] :=
          Nat.ModEq.pow_totient hcop'
        -- We claim x₀ = (x₀^(1 + t*p^k))^((1 + t*p^k)^(φ(n)-1))
        -- Let m = (1 + t*p^k)^(φ(n)-1)
        set m := (1 + t.val * p ^ k) ^ (Nat.totient n - 1) with hm_def
        use m
        -- Goal involves zpow (integer exponent) since zpowers uses zpow
        -- Convert zpow to pow
        simp only [zpow_natCast]
        -- Goal: (x₀ ^ (1 + ↑t * p ^ k)) ^ m = x₀
        -- Using pow_mul: (x₀ ^ A) ^ m = x₀ ^ (A * m)
        -- Note: after substituting hm_def, m = A^(φ-1), so we need pow_mul for (x₀^A)^(A^(φ-1))
        rw [hm_def]
        -- Goal is now: (x₀ ^ A) ^ (A ^ (φ-1)) = x₀ where A = 1 + ↑t * p ^ k
        have hφpos : 0 < Nat.totient n := Nat.totient_pos.mpr hnpos
        have heq : (1 + t.val * p ^ k) * (1 + t.val * p ^ k) ^ (Nat.totient n - 1) = (1 + t.val * p ^ k) ^ Nat.totient n := by
          rw [← pow_succ', Nat.sub_add_cancel hφpos]
        have pow_mul_applied : (x₀ ^ (1 + t.val * p ^ k)) ^ ((1 + t.val * p ^ k) ^ (Nat.totient n - 1))
                             = x₀ ^ ((1 + t.val * p ^ k) * (1 + t.val * p ^ k) ^ (Nat.totient n - 1)) := by
          exact (pow_mul x₀ (1 + t.val * p ^ k) ((1 + t.val * p ^ k) ^ (Nat.totient n - 1))).symm
        rw [pow_mul_applied, heq]
        -- Goal: x₀ ^ (1 + ↑t * p ^ k) ^ n.totient = x₀
        -- Since (1 + ↑t * p ^ k) ^ n.totient ≡ 1 (mod n) and x₀ ^ n = 1
        -- We have x₀ ^ ((1 + ↑t * p ^ k) ^ n.totient) = x₀ ^ 1 = x₀
        -- x₀^m = x₀^(m % n) when orderOf x₀ = n
        have key : x₀ ^ ((1 + t.val * p ^ k) ^ Nat.totient n) = x₀ ^ (((1 + t.val * p ^ k) ^ Nat.totient n) % n) := by
          rw [pow_mod_orderOf]
        rw [key]
        rw [h_tot]
        have h1lt : 1 < n := hn.symm ▸ Nat.one_lt_pow (by omega : a + k ≠ 0) hp.one_lt
        simp [Nat.mod_eq_of_lt h1lt]
  -- Now show f is a bijection between Fin (p^a) and S
  -- First, f is injective
  have hf_inj : Function.Injective f := by
    intro t t' h_eq
    simp only [f] at h_eq
    -- Use pow_right_inj: x^m = x^n ↔ m ≡ n (mod orderOf x) when x has finite order
    have hmod : (1 + t.val * p ^ k) ≡ (1 + t'.val * p ^ k) [MOD orderOf x₀] := by
      -- If x^m = x^n, then m ≡ n (mod orderOf x)
      -- This follows from x^(m-n) = 1 when m ≥ n, so orderOf x | (m-n)
      wlog h : 1 + t.val * p ^ k ≥ 1 + t'.val * p ^ k generalizing t t'
      · push Not at h
        exact (this h_eq.symm (le_of_lt h)).symm
      have hdiff : x₀ ^ (1 + t.val * p ^ k - (1 + t'.val * p ^ k)) = 1 := by
        have heq' : x₀ ^ (1 + t.val * p ^ k) = x₀ ^ (1 + t.val * p ^ k - (1 + t'.val * p ^ k)) * x₀ ^ (1 + t'.val * p ^ k) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq] at heq'
        have := congr_arg (· * (x₀ ^ (1 + t'.val * p ^ k))⁻¹) heq'
        simp at this
        exact this.symm
      have hdvd : orderOf x₀ ∣ (1 + t.val * p ^ k) - (1 + t'.val * p ^ k) := orderOf_dvd_of_pow_eq_one hdiff
      simp only [add_tsub_add_eq_tsub_left] at hdvd
      rw [Nat.modEq_iff_dvd]
      simp_all
      have : (p ^ (a + k) : ℤ) ∣ (t'.val : ℤ) * p ^ k - (t.val : ℤ) * p ^ k := by
        have hdvd' : (p ^ (a + k) : ℤ) ∣ (t.val : ℤ) * p ^ k - (t'.val : ℤ) * p ^ k := by
          exact_mod_cast hdvd
        exact dvd_sub_comm.mp hdvd'
      exact this
    -- Simplify: t * p^k ≡ t' * p^k (mod p^(a+k))
    -- So p^a | (t - t')
    have ht_eq : t.val = t'.val := by
      -- From hmod: (1 + t*p^k) ≡ (1 + t'*p^k) [MOD p^(a+k)]
      -- So t*p^k ≡ t'*p^k [MOD p^(a+k)], hence p^(a+k) | (t - t')*p^k in ℤ
      rw [hord] at hmod
      -- We need to show t.val = t'.val given that t, t' < p^a and the modular condition
      -- The condition implies p^a | (t - t') in ℤ
      have key : (p ^ (a + k) : ℤ) ∣ ((t.val : ℤ) - (t'.val : ℤ)) * p ^ k := by
        have hmod' : ((1 + t.val * p ^ k : ℕ) : ℤ) ≡ ((1 + t'.val * p ^ k : ℕ) : ℤ) [ZMOD (p ^ (a + k) : ℤ)] := by
          rw [Int.ModEq]
          norm_cast
        have hsimp : ((t.val : ℤ) * p ^ k) ≡ ((t'.val : ℤ) * p ^ k) [ZMOD (p ^ (a + k) : ℤ)] := by
          rw [Int.ModEq] at hmod' ⊢
          have h1 : ((1 + t.val * p ^ k : ℕ) : ℤ) = 1 + (t.val : ℤ) * p ^ k := by push_cast; ring
          have h2 : ((1 + t'.val * p ^ k : ℕ) : ℤ) = 1 + (t'.val : ℤ) * p ^ k := by push_cast; ring
          rw [h1, h2] at hmod'
          have hpow_gt : 1 < (p : ℤ) ^ (a + k) := by
            norm_cast; exact one_lt_pow₀ hp.one_lt (by omega : a + k ≠ 0)
          -- hmod' says (1 + t.val * p^k) % n = (1 + t'.val * p^k) % n in ℤ
          -- We need t.val * p^k % n = t'.val * p^k % n in ℤ
          -- (1 + a) % n = (1 + b) % n → a % n = b % n
          -- Because (1 + a) ≡ (1 + b) (mod n) → a ≡ b (mod n)
          have hmod2 : ((1 : ℤ) + (t.val : ℤ) * p ^ k) ≡ ((1 : ℤ) + (t'.val : ℤ) * p ^ k) [ZMOD (p : ℤ) ^ (a + k)] := by
            rw [Int.ModEq, hmod']
          have hmod3 := hmod2.sub_right 1
          simp at hmod3
          exact hmod3
        rw [Int.modEq_iff_dvd] at hsimp
        have h' := dvd_sub_comm.mp hsimp
        rw [sub_mul]
        exact h'
      have hdvd' : (p ^ a : ℤ) ∣ (t.val : ℤ) - (t'.val : ℤ) := by
        have : (p ^ (a + k) : ℤ) = (p ^ a : ℤ) * (p ^ k : ℤ) := by ring
        rw [this] at key
        exact Int.mul_dvd_mul_iff_right (pow_ne_zero k (Nat.cast_ne_zero.mpr hp.ne_zero)) |>.mp key
      -- Since t, t' < p^a and p^a | (t - t'), we have t = t'
      have ht_bound : t.val < p ^ a := t.is_lt
      have ht'_bound : t'.val < p ^ a := t'.is_lt
      have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
      -- From hdvd' and the bounds, conclude t.val = t'.val
      have habs : Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) < p ^ a := by
        omega
      have hdvd_nat : p ^ a ∣ Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) := by
        exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd')
      have hzero : Int.natAbs ((t.val : ℤ) - (t'.val : ℤ)) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_nat habs
      omega
    exact Fin.val_injective ht_eq
  -- Show S = image of f, then use card_image_of_injective
  have hf_image_eq_S : S = Finset.image f Finset.univ := by
    apply Finset.eq_of_subset_of_card_le
    · -- S ⊆ image f univ: need surjectivity
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      obtain ⟨hx_pow, hx_zpow⟩ := hx
      -- x ∈ zpowers x₀, so x = x₀^m for some m
      have hx_mem : x ∈ Subgroup.zpowers x₀ := hx_zpow ▸ Subgroup.mem_zpowers x
      obtain ⟨m, hm⟩ := hx_mem
      -- hm : x₀ ^ m = x
      -- Reduce m to [0, orderOf x₀)
      let m' := Int.toNat (m % orderOf x₀)
      have hord_pos : (0 : ℤ) < orderOf x₀ := by exact_mod_cast orderOf_pos x₀
      have hm'_lt : m' < orderOf x₀ := by
        simp only [m']
        have h1 : 0 ≤ m % orderOf x₀ := Int.emod_nonneg m hord_pos.ne'
        have h2 : m % orderOf x₀ < orderOf x₀ := Int.emod_lt_of_pos m hord_pos
        omega
      have hx_eq : x = x₀ ^ m' := by
        rw [← hm]
        have heq : m = (m % orderOf x₀ : ℤ) + orderOf x₀ * (m / orderOf x₀) := by
          linarith [Int.emod_add_mul_ediv m (orderOf x₀)]
        have h_nonneg : 0 ≤ m % orderOf x₀ := Int.emod_nonneg m hord_pos.ne'
        show x₀ ^ m = x₀ ^ m'
        rw [heq, zpow_add, zpow_mul]
        have h1 : x₀ ^ (orderOf x₀ : ℤ) = 1 := by
          rw [zpow_natCast, pow_orderOf_eq_one]
        have h2 : (x₀ ^ (orderOf x₀ : ℤ)) ^ (m / (orderOf x₀ : ℤ)) = 1 := by
          rw [h1, one_zpow]
        rw [h2, mul_one]
        -- Now need: x₀ ^ (m % orderOf x₀) = x₀ ^ m'
        -- Since m' = (m % orderOf x₀).toNat and m % orderOf x₀ ≥ 0
        rw [← zpow_natCast, Int.toNat_of_nonneg h_nonneg]
      -- Since x^(p^a) = y = x₀^(p^a), we have x₀^(m'*p^a) = x₀^(p^a)
      -- So m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- Hence p^k | (m' - 1), so m' = 1 + t*p^k for some t
      have hpow_eq : x₀ ^ (m' * p ^ a) = x₀ ^ (p ^ a) := by
        calc x₀ ^ (m' * p ^ a) = (x₀ ^ m') ^ (p ^ a) := by rw [← pow_mul]
          _ = x ^ (p ^ a) := by rw [← hx_eq]
          _ = y := hx_pow
          _ = x₀ ^ (p ^ a) := hx₀.symm
      -- From hpow_eq: m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- So p^(a+k) | (m' - 1)*p^a, hence p^k | (m' - 1)
      -- Thus m' = 1 + t*p^k for some t with 0 ≤ t < p^a
      -- x₀^(m'*p^a) = x₀^(p^a) with orderOf x₀ = p^(a+k)
      -- For finite order elements, x^A = x^B implies A ≡ B (mod orderOf x)
      -- From hpow_eq: m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
      -- So p^(a+k) | (m' - 1)*p^a, hence p^k | (m' - 1)
      -- Thus m' = 1 + t*p^k for some t with 0 ≤ t < p^a
      -- x₀^(m'*p^a) = x₀^(p^a) with orderOf x₀ = p^(a+k)
      -- For finite order elements, x^A = x^B implies A ≡ B (mod orderOf x)
      have hm'_eq : m' * p ^ a ≡ p ^ a [MOD p ^ (a + k)] := by
        -- x₀^(m'*p^a) = x₀^(p^a) implies m'*p^a ≡ p^a (mod orderOf x₀ = p^(a+k))
        rcases le_total (m' * p ^ a) (p ^ a) with hle | hge
        · -- m' * p^a ≤ p^a case
          have hdiff : x₀ ^ (p ^ a - m' * p ^ a) = 1 := by
            have heq' : x₀ ^ (p ^ a) = x₀ ^ (p ^ a - m' * p ^ a) * x₀ ^ (m' * p ^ a) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hpow_eq] at heq'
            have := congr_arg (· * (x₀ ^ (m' * p ^ a))⁻¹) heq'
            simp at this
            exact this
          have hdvd : orderOf x₀ ∣ p ^ a - m' * p ^ a := orderOf_dvd_of_pow_eq_one hdiff
          rw [hord] at hdvd
          rw [Nat.modEq_iff_dvd]
          exact_mod_cast hdvd
        · -- p^a ≤ m' * p^a case
          have hdiff : x₀ ^ (m' * p ^ a - p ^ a) = 1 := by
            have heq' : x₀ ^ (m' * p ^ a) = x₀ ^ (m' * p ^ a - p ^ a) * x₀ ^ (p ^ a) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hpow_eq] at heq'
            have := congr_arg (· * (x₀ ^ (p ^ a))⁻¹) heq'
            simp at this
            exact this.symm
          have hdvd : orderOf x₀ ∣ m' * p ^ a - p ^ a := orderOf_dvd_of_pow_eq_one hdiff
          rw [hord] at hdvd
          rw [Nat.modEq_iff_dvd]
          have hdvd' : (p ^ (a + k) : ℤ) ∣ (m' : ℤ) * p ^ a - p ^ a := by norm_cast
          push_cast
          exact dvd_sub_comm.mp hdvd'
      -- First show m' ≥ 1 (otherwise x₀^0 = 1 = y contradicts orderOf y = p^k with k ≥ 1)
      have hm'_pos : m' ≥ 1 := by
        by_contra hm'0
        push Not at hm'0
        have hm'_eq0 : m' = 0 := by omega
        rw [hm'_eq0, zero_mul] at hpow_eq
        have h1 : x₀ ^ p ^ a = 1 := by rw [hpow_eq.symm]; exact pow_zero x₀
        have : orderOf (x₀ ^ p ^ a) = 1 := by rw [h1]; exact orderOf_one
        rw [hx₀] at this
        rw [hy] at this
        have hk0 : k = 0 := (Nat.pow_right_injective hp.one_lt).eq_iff.mp this
        omega
      -- From hm'_eq: p^(a+k) | (m' - 1) * p^a
      have hdvd : p ^ (a + k) ∣ (m' - 1) * p ^ a := by
        have h1 : (m' - 1) * p ^ a = m' * p ^ a - p ^ a := by
          rw [tsub_mul, one_mul]
        rw [h1]
        have hge : m' * p ^ a ≥ p ^ a := by
          have : 1 ≤ m' := hm'_pos
          nlinarith [pow_pos hp.pos a]
        -- m' * p^a ≡ p^a [MOD p^(a+k)] means p^(a+k) | (m' * p^a - p^a) = (m' - 1) * p^a
        have hm'_eq' : (m' * p ^ a : ℤ) ≡ (p ^ a : ℤ) [ZMOD (p ^ (a + k) : ℤ)] := by
          simp only [Int.ModEq]
          norm_cast
        have hdvd_int : (p ^ (a + k) : ℤ) ∣ ((m' : ℤ) * p ^ a - p ^ a) := Int.ModEq.dvd hm'_eq'.symm
        have hdvd_nat : (p ^ (a + k) : ℤ) ∣ ((m' * p ^ a - p ^ a : ℕ) : ℤ) := by
          rw [Int.ofNat_sub hge]
          exact hdvd_int
        norm_cast at hdvd_nat
      -- From p^(a+k) ∣ (m' - 1) * p^a, we get p^k ∣ (m' - 1)
      have hdvd' : p ^ k ∣ (m' - 1) := by
        have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
        have heq : p ^ (a + k) = p ^ a * p ^ k := by ring
        rw [heq] at hdvd
        rw [mul_comm (m' - 1)] at hdvd
        exact Nat.mul_dvd_mul_iff_left hpa_pos |>.mp hdvd
      -- So m' = 1 + t * p^k for some t
      obtain ⟨t, ht⟩ := hdvd'
      -- Since m' < p^(a+k), we have t < p^a
      have hm'_lt' : m' < p ^ (a + k) := hord ▸ hm'_lt
      have ht_lt : t < p ^ a := by
        have hm'_eq' : m' = 1 + t * p ^ k := by
          have := ht
          rw [mul_comm] at this
          omega
        rw [hm'_eq'] at hm'_lt'
        have hpow_eq : p ^ (a + k) = p ^ a * p ^ k := by ring
        rw [hpow_eq] at hm'_lt'
        have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
        nlinarith
      -- x = x₀^m' = x₀^(1 + t*p^k) = f ⟨t, ht_lt⟩
      use ⟨t, ht_lt⟩
      simp only [f]
      rw [hx_eq]
      congr 1
      have := ht
      rw [mul_comm] at this
      omega
    · -- card (image f univ) ≤ card S
      have h1 : #(Finset.image f Finset.univ) = p ^ a := by
        rw [Finset.card_image_of_injective _ hf_inj]
        simp
      have h2 : #(Finset.image f Finset.univ) ≤ #S :=
        Finset.card_le_card (Finset.image_subset_iff.mpr fun t _ => hf_in_S t)
      linarith
  show #S = p ^ a
  rw [hf_image_eq_S, Finset.card_image_of_injective _ hf_inj]
  simp

/-- **Key counting lemma.**  If `y` has order `p ^ k` with `k ≥ 1`, then the number of solutions
of `x ^ (p ^ a) = y` is divisible by `p ^ a`.  Indeed every solution `x` has order `p ^ (a + k)`,
and for each cyclic subgroup `C` of order `p ^ (a+k)` containing `y` the solutions lying in `C`
form a coset of `{z ∈ C | z ^ (p ^ a) = 1}`, which has exactly `p ^ a` elements. -/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# AKS core: the introspective-numbers argument

This file contains the mathematical heart of the Agrawal–Kayal–Saxena primality test.
-/

namespace AKS

open Polynomial

section Introspective

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m` is *introspective* for the polynomial `f` (with respect to `r`-th roots of unity in the
field `F` of characteristic `p`) if `f(y)^m = f(y^m)` for every `r`-th root of unity `y ∈ F`. -/

theorem eq_minFac_pow_of_cond {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hsmall : ∀ m, 2 ≤ m → m ≤ r → ¬ m ∣ n)
    (hord : ∀ i, 1 ≤ i → i ≤ 4 * (Nat.log 2 n + 1) ^ 2 → ¬ (n ^ i ≡ 1 [MOD r]))
    (hcond : ∀ a, 1 ≤ a → a ≤ (Nat.log 2 n + 1) * (Nat.sqrt r + 1) + 2 →
      (X ^ r - 1 : (ZMod n)[X]) ∣ ((X + C (a : ZMod n)) ^ n - (X ^ n + C (a : ZMod n)))) :
    ∃ k, n = n.minFac ^ k := by
  classical
  by_contra hnpow
  push_neg at hnpow
  set L := Nat.log 2 n + 1 with hLdef
  have hL2 : 2 ≤ L := by
    have h1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
    omega
  have hnlt : n < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) n
  have hn1 : n ≠ 1 := by omega
  haveI : NeZero r := ⟨by omega⟩
  -- `n` is coprime to `r`
  have hcop : Nat.Coprime n r := by
    by_contra hc
    have h0 : 0 < Nat.gcd n r := Nat.gcd_pos_of_pos_right n hr
    have h2 : 2 ≤ Nat.gcd n r := by
      rcases Nat.lt_or_ge (Nat.gcd n r) 2 with h | h
      · exact absurd (by unfold Nat.Coprime; omega) hc
      · exact h
    exact hsmall _ h2 (Nat.le_of_dvd hr (Nat.gcd_dvd_right n r)) (Nat.gcd_dvd_left n r)
  have hKtot : 4 * L ^ 2 < Nat.totient r := by
    by_contra hc
    push_neg at hc
    exact hord (Nat.totient r) (Nat.totient_pos.mpr (by omega)) hc (Nat.ModEq.pow_totient hcop)
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · exfalso
      interval_cases r
      · rw [Nat.totient_one] at hKtot
        have : 0 < L ^ 2 := pow_pos (by omega) 2
        omega
    · exact h
  have hrK : 4 * L ^ 2 < r := lt_of_lt_of_le hKtot (le_of_lt (Nat.totient_lt r hr2))
  -- the smallest prime factor
  set P := n.minFac with hPdef
  have hP : P.Prime := Nat.minFac_prime hn1
  haveI : Fact P.Prime := ⟨hP⟩
  have hPn : P ∣ n := Nat.minFac_dvd n
  have hrP : r < P := by
    by_contra hc
    push_neg at hc
    exact hsmall P hP.two_le hc hPn
  have hPcop : Nat.Coprime P r := (Nat.Prime.coprime_iff_not_dvd hP).mpr
    (fun hd => absurd (Nat.le_of_dvd hr hd) (by omega))
  -- the auxiliary finite field
  set d := orderOf (ZMod.unitOfCoprime P hPcop) with hddef
  have hd0 : d ≠ 0 := (orderOf_pos _).ne'
  set F := GaloisField P d with hFdef
  have hcardF : Nat.card F = P ^ d := GaloisField.card P d hd0
  have hrdvd : r ∣ Nat.card F - 1 := by
    rw [hcardF]
    have h1 : (ZMod.unitOfCoprime P hPcop) ^ d = 1 := pow_orderOf_eq_one _
    have h2 : ((P : ZMod r)) ^ d = 1 := by
      have h3 := congrArg (Units.val) h1
      simpa [ZMod.coe_unitOfCoprime] using h3
    have h4 : (P ^ d : ℕ) ≡ 1 [MOD r] := by
      have h5 : ((P ^ d : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by push_cast; simpa using h2
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h5
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hP.pos)).mp h4.symm
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_of_dvd (F := F) hrdvd
  have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  haveI : Fintype F := Fintype.ofFinite F
  set q := n / P with hqdef
  have hqP : q * P = n := Nat.div_mul_cancel hPn
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hqP; omega
    · exact h
  -- introspective numbers
  set ℓ := L * (Nat.sqrt r + 1) + 2 with hℓdef
  have hIq : ∀ a, 1 ≤ a → a ≤ ℓ → Introspective F r q (X + C (a : ZMod P)) := by
    intro a h1 h2
    refine Introspective.of_mul_char ?_
    rw [hqP]
    exact introspective_of_dvd hPn (hcond a h1 h2)
  have hIall : ∀ (i j a : ℕ), 1 ≤ a → a ≤ ℓ →
      Introspective F r (q ^ i * P ^ j) (X + C (a : ZMod P)) := fun i j a h1 h2 =>
    ((hIq a h1 h2).pow i).mul_exp ((introspective_char (F := F) (r := r) _).pow j)
  -- the set of powers of ζ that occur
  set T : Finset F := Finset.univ.filter (fun x : F => ∃ i j : ℕ, x = ζ ^ (q ^ i * P ^ j))
    with hTdef
  set t := T.card with htdef
  have hmemT : ∀ i j : ℕ, ζ ^ (q ^ i * P ^ j) ∈ T := by
    intro i j
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, j, rfl⟩
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hζr
    exact zero_ne_one hζr
  have hζu : orderOf (Units.mk0 ζ hζ0) = r := by
    rw [← hζ, ← orderOf_units]
    rfl
  have hpowinj : ∀ u v : ℕ, ζ ^ u = ζ ^ v ↔ u ≡ v [MOD r] := by
    intro u v
    rw [← hζu, ← pow_eq_pow_iff_modEq (x := Units.mk0 ζ hζ0)]
    constructor
    · intro h
      exact Units.ext (by simpa using h)
    · intro h
      simpa using congrArg (Units.val) h
  have hKt : 4 * L ^ 2 < t := by
    have key : ∀ k l : ℕ, k < l → l ≤ 4 * L ^ 2 → ζ ^ (n ^ k) ≠ ζ ^ (n ^ l) := by
      intro k l hkl hl he
      rw [hpowinj] at he
      have hcopk : Nat.Coprime (n ^ k) r := Nat.Coprime.pow_left _ hcop
      have h1 : (1 : ℕ) ≡ n ^ (l - k) [MOD r] := by
        have h2 : n ^ k * 1 ≡ n ^ k * n ^ (l - k) [MOD r] := by
          rw [mul_one, ← pow_add, Nat.add_sub_cancel' hkl.le]
          exact he
        exact Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hcopk) h2
      exact hord (l - k) (by omega) (by omega) h1.symm
    have hmaps : ∀ k ∈ Finset.range (4 * L ^ 2 + 1), ζ ^ (n ^ k) ∈ T := by
      intro k _
      have hnk : n ^ k = q ^ k * P ^ k := by rw [← hqP, mul_pow]
      rw [hnk]; exact hmemT k k
    have hinj : Set.InjOn (fun k => ζ ^ (n ^ k)) (Finset.range (4 * L ^ 2 + 1)) := by
      intro k hk l hl hkl
      simp only [Finset.coe_range, Set.mem_Iio] at hk hl
      rcases lt_trichotomy k l with h | h | h
      · exact absurd hkl (key k l h (by omega))
      · exact h
      · exact absurd hkl.symm (key l k h (by omega))
    have hle := Finset.card_le_card_of_injOn (fun k => ζ ^ (n ^ k))
      (fun k hk => hmaps k (by simpa using hk)) hinj
    simp only [Finset.card_range] at hle
    omega
  have htr : t ≤ r := by
    have hsub : T ⊆ (Finset.range r).image (fun k => ζ ^ k) := by
      intro x hx
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨i, j, rfl⟩ := hx
      refine Finset.mem_image.mpr ⟨(q ^ i * P ^ j) % r,
        Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
      rw [← hζ, pow_mod_orderOf]
    calc t ≤ ((Finset.range r).image (fun k => ζ ^ k)).card := Finset.card_le_card hsub
      _ ≤ (Finset.range r).card := Finset.card_image_le
      _ = r := Finset.card_range r
  set S := Nat.sqrt t with hSdef
  set s := L * S + 1 with hsdef
  have hst : s < t := num_s_lt_t hL2 hKt
  have hS0 : 4 ≤ S := by
    rw [hSdef, Nat.le_sqrt]
    nlinarith
  have hSr : S ≤ Nat.sqrt r := Nat.sqrt_le_sqrt htr
  have hsl : s + 1 ≤ ℓ := by
    have h1 : L * S ≤ L * Nat.sqrt r := Nat.mul_le_mul_left L hSr
    have h2 : L * (Nat.sqrt r + 1) + 2 = L * Nat.sqrt r + L + 2 := by ring
    rw [hsdef, hℓdef, h2]
    omega
  have hlP : ℓ < P := lt_of_le_of_lt (num_l_le_r hL2 hrK) hrP
  -- the set of `a`'s used
  have hmodinj : ∀ a b : ℕ, a ≤ ℓ → b ≤ ℓ → a ≡ b [MOD P] → a = b := by
    intro a b ha hb hab
    have h1 : a % P = a := Nat.mod_eq_of_lt (by omega)
    have h2 : b % P = b := Nat.mod_eq_of_lt (by omega)
    unfold Nat.ModEq at hab
    omega
  set A₀ : Finset ℕ := (Finset.Icc 1 ℓ).filter (fun a : ℕ => (ζ + (a : F)) ≠ 0) with hA₀def
  have hA₀card : s ≤ A₀.card := by
    have hbad : ((Finset.Icc 1 ℓ).filter (fun a : ℕ => ¬ ((ζ + (a : F)) ≠ 0))).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_Icc, not_not] at ha hb
      have hab : (a : F) = (b : F) := by
        have h1 := ha.2
        have h2 := hb.2
        linear_combination h1 - h2
      exact hmodinj a b ha.1.2 hb.1.2 ((CharP.natCast_eq_natCast F P).mp hab)
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.Icc 1 ℓ) (p := fun a : ℕ => (ζ + (a : F)) ≠ 0)
    rw [Nat.card_Icc, ← hA₀def] at hsum
    omega
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hA₀card
  have hAle : ∀ a ∈ A, 1 ≤ a ∧ a ≤ ℓ := by
    intro a ha
    have hm := hAsub ha
    simp only [hA₀def, Finset.mem_filter, Finset.mem_Icc] at hm
    exact hm.1
  have hAinj : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod P) = (b : ZMod P) → a = b := by
    intro a ha b hb hab
    exact hmodinj a b (hAle a ha).2 (hAle b hb).2 ((ZMod.natCast_eq_natCast_iff _ _ _).mp hab)
  -- the products
  set B : Finset F := A.powerset.image (fun S' : Finset ℕ => ∏ a ∈ S', (ζ + (a : F)))
    with hBdef
  have hBcard : B.card = 2 ^ s := by
    rw [hBdef, Finset.card_image_of_injOn, Finset.card_powerset, hAcard]
    intro S₁ h₁ S₂ h₂ he
    refine finset_eq_of_prod_eq (t := t) (I := {m | ∃ i j : ℕ, m = q ^ i * P ^ j}) (T := T)
      hζr (by omega) hAinj ?_ le_rfl ?_ (Finset.mem_powerset.mp h₁) (Finset.mem_powerset.mp h₂) he
    · rintro m ⟨i, j, rfl⟩ a ha
      exact hIall i j a (hAle a ha).1 (hAle a ha).2
    · intro y hy
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨i, j, rfl⟩ := hy
      exact ⟨q ^ i * P ^ j, ⟨i, j, rfl⟩, rfl⟩
  -- the main contradiction
  have main : ∀ m₁ m₂ : ℕ, m₂ < m₁ → m₁ ≤ n ^ S → ζ ^ m₁ = ζ ^ m₂ →
      (∀ a ∈ A, Introspective F r m₁ (X + C (a : ZMod P))) →
      (∀ a ∈ A, Introspective F r m₂ (X + C (a : ZMod P))) → False := by
    intro m₁ m₂ hlt hle hpow hI1 hI2
    have hBpow : ∀ z ∈ B, z ^ m₁ = z ^ m₂ := by
      intro z hz
      simp only [hBdef, Finset.mem_image, Finset.mem_powerset] at hz
      obtain ⟨S', hS', rfl⟩ := hz
      have haeval : ∀ m : ℕ, (∀ a ∈ A, Introspective F r m (X + C (a : ZMod P))) →
          (∏ a ∈ S', (ζ + (a : F))) ^ m = aeval (ζ ^ m) (∏ a ∈ S', (X + C (a : ZMod P))) := by
        intro m hIm
        have hpr : Introspective F r m (∏ a ∈ S', (X + C (a : ZMod P))) :=
          Introspective.prod S' _ fun a ha => hIm a (hS' ha)
        have hh := hpr ζ hζr
        rw [← hh, map_prod]
        exact congrArg (· ^ m) (Finset.prod_congr rfl fun a _ => by simp [map_natCast])
      rw [haeval m₁ hI1, haeval m₂ hI2, hpow]
    have hcard := card_le_of_pow_eq_pow hlt B hBpow
    rw [hBcard] at hcard
    have h1 : n ^ S < 2 ^ (L * S) := by
      calc n ^ S < (2 ^ L) ^ S := Nat.pow_lt_pow_left hnlt (by omega)
        _ = 2 ^ (L * S) := by rw [← pow_mul]
    have h2 : (2 : ℕ) ^ s = 2 * 2 ^ (L * S) := by
      rw [hsdef, pow_succ]
      ring
    omega
  -- pigeonhole
  have hcardlt : T.card < ((Finset.range (S + 1)) ×ˢ (Finset.range (S + 1))).card := by
    rw [Finset.card_product, Finset.card_range]
    simpa [pow_two] using Nat.lt_succ_sqrt' t
  obtain ⟨u, hu, v, hv, huv, hfuv⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardlt
      (f := fun ij : ℕ × ℕ => ζ ^ (q ^ ij.1 * P ^ ij.2))
      (fun ij _ => Finset.mem_coe.mpr (hmemT ij.1 ij.2))
  have hbound : ∀ ij : ℕ × ℕ, ij ∈ (Finset.range (S + 1)) ×ˢ (Finset.range (S + 1)) →
      q ^ ij.1 * P ^ ij.2 ≤ n ^ S := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    calc q ^ ij.1 * P ^ ij.2 ≤ q ^ S * P ^ S :=
          Nat.mul_le_mul (Nat.pow_le_pow_right hq1 (by omega))
            (Nat.pow_le_pow_right hP.pos (by omega))
      _ = n ^ S := by rw [← mul_pow, hqP]
  have hintro : ∀ ij : ℕ × ℕ, ∀ a ∈ A,
      Introspective F r (q ^ ij.1 * P ^ ij.2) (X + C (a : ZMod P)) :=
    fun ij a ha => hIall ij.1 ij.2 a (hAle a ha).1 (hAle a ha).2
  have hne : q ^ u.1 * P ^ u.2 ≠ q ^ v.1 * P ^ v.2 := by
    intro he
    obtain ⟨h1, h2⟩ := pow_mul_pow_injective hP hn hqP hnpow he
    exact huv (Prod.ext h1 h2)
  rcases lt_trichotomy (q ^ u.1 * P ^ u.2) (q ^ v.1 * P ^ v.2) with h | h | h
  · exact main _ _ h (hbound v hv) hfuv.symm (hintro v) (hintro u)
  · exact hne h
  · exact main _ _ h (hbound u hu) hfuv (hintro u) (hintro v)

end MainCriterion

end AKS


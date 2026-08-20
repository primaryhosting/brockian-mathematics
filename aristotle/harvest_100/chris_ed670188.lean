import RequestProject.Mertens

/-!
# The main term: `∏_{3 ≤ p ≤ z} (1 - 2/p) ≤ 16 / (log z)^2`

This is proved by the elementary Euler-type argument: expanding `∏ (1 + 1/(p-1))` over
subsets dominates `∑_{a ≤ z squarefree} 1/a`, which in turn is at least half the harmonic
sum, hence at least `(log z)/2`.
-/

namespace Brun

open Finset

lemma sum_inv_sq_le' : ∀ B : ℕ, 1 ≤ B → ∑ b ∈ Icc 1 B, (1 / (b : ℝ) ^ 2) ≤ 2 - 1 / B := by
  intro B hB
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hB0 : (0:ℝ) < B := by exact_mod_cast hB
    have key : 1 / ((B : ℝ) + 1) ^ 2 ≤ 1 / B - 1 / ((B : ℝ) + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff (by positivity)
        (by positivity)]
      ring_nf
      nlinarith
    push_cast
    linarith

lemma sum_inv_sq_le (B : ℕ) : ∑ b ∈ Icc 1 B, (1 / (b : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  · have := sum_inv_sq_le' B hB
    have : (0:ℝ) < B := by exact_mod_cast hB
    have h2 := sum_inv_sq_le' B hB
    have : (0:ℝ) ≤ 1 / B := by positivity
    linarith

/-- Squarefree numbers in `[1, z]`. -/
def sqfreeLE (z : ℕ) : Finset ℕ := (Icc 1 z).filter Squarefree

/-- Half the harmonic sum is dominated by the sum of reciprocals of squarefree numbers. -/
lemma harmonic_le_two_mul_sum_sqfree (z : ℕ) :
    ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤ 2 * ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by
  classical
  set F : ℕ × ℕ → ℕ := fun q => q.1 * q.2 ^ 2 with hF
  have hsub : Icc 1 z ⊆ (sqfreeLE z ×ˢ Icc 1 z).image F := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
    have hn0 : 0 < n := hn.1
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · simp at hab; omega
      · exact h
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · simp at hab; omega
      · exact h
    have haz : a ≤ z := by
      have : a ≤ n := by
        calc a ≤ b ^ 2 * a := Nat.le_mul_of_pos_left _ (by positivity)
        _ = n := hab
      omega
    have hbz : b ≤ z := by
      have : b ≤ n := by
        calc b ≤ b ^ 2 * a := by nlinarith
        _ = n := hab
      omega
    refine Finset.mem_image.mpr ⟨(a, b), ?_, ?_⟩
    · simp only [Finset.mem_product, sqfreeLE, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨⟨ha0, haz⟩, ha⟩, ⟨hb0, hbz⟩⟩
    · simp only [hF]
      omega
  calc ∑ n ∈ Icc 1 z, (1 / (n : ℝ))
      ≤ ∑ n ∈ (sqfreeLE z ×ˢ Icc 1 z).image F, (1 / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro i _ _; positivity
  _ ≤ ∑ q ∈ sqfreeLE z ×ˢ Icc 1 z, (1 / ((F q : ℕ) : ℝ)) := by
        refine Finset.sum_image_le _ _ _ ?_
        intro i _; positivity
  _ = (∑ a ∈ sqfreeLE z, (1 / (a : ℝ))) * ∑ b ∈ Icc 1 z, (1 / (b : ℝ) ^ 2) := by
        rw [Finset.sum_product, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        simp only [hF]
        push_cast
        rw [one_div, one_div, one_div, mul_inv]
  _ ≤ (∑ a ∈ sqfreeLE z, (1 / (a : ℝ))) * 2 := by
        have hnn : 0 ≤ ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by
          refine Finset.sum_nonneg (fun a _ => by positivity)
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_le z) hnn
  _ = 2 * ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by ring

/-- The sum of reciprocals of squarefree numbers `≤ z` is dominated by the Euler product. -/
lemma sum_sqfree_le_prod (z : ℕ) :
    ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) ≤ ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hexp : ∏ p ∈ primesLE z, (1 / ((p : ℝ) - 1) + 1)
      = ∑ s ∈ (primesLE z).powerset, ∏ p ∈ s, (1 / ((p : ℝ) - 1)) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl (fun s _ => by simp)
  have hstep : ∑ s ∈ (primesLE z).powerset, (1 / ((∏ p ∈ s, p : ℕ) : ℝ))
      ≤ ∑ s ∈ (primesLE z).powerset, ∏ p ∈ s, (1 / ((p : ℝ) - 1)) := by
    refine Finset.sum_le_sum (fun s hs => ?_)
    rw [Finset.mem_powerset] at hs
    have hprod : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := by push_cast; ring
    rw [hprod, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
    have hp2 : 2 ≤ p := (mem_primesLE.mp (hs hp)).2.two_le
    have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hp2
    rw [one_div]
    apply inv_le_inv_of_le <;> linarith
  have hinj : Set.InjOn (fun s => ∏ p ∈ s, p) ((primesLE z).powerset : Set (Finset ℕ)) := by
    intro s hs t ht hst
    have hs' : ∀ p ∈ s, p.Prime := by
      intro p hp
      exact (mem_primesLE.mp ((Finset.mem_powerset.mp hs) hp)).2
    have ht' : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact (mem_primesLE.mp ((Finset.mem_powerset.mp ht) hp)).2
    have := congrArg Nat.primeFactors hst
    rwa [Nat.primeFactors_prod hs', Nat.primeFactors_prod ht'] at this
  have himg : sqfreeLE z ⊆ ((primesLE z).powerset).image (fun s => ∏ p ∈ s, p) := by
    intro a ha
    simp only [sqfreeLE, Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, haz⟩, hsq⟩ := ha
    refine Finset.mem_image.mpr ⟨a.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsq⟩
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact mem_primesLE.mpr ⟨le_trans (Nat.le_of_dvd (by omega) hp.2.1) haz, hp.1⟩
  calc ∑ a ∈ sqfreeLE z, (1 / (a : ℝ))
      ≤ ∑ a ∈ ((primesLE z).powerset).image (fun s => ∏ p ∈ s, p), (1 / (a : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg himg ?_
        intro i _ _; positivity
  _ = ∑ s ∈ (primesLE z).powerset, (1 / ((∏ p ∈ s, p : ℕ) : ℝ)) := Finset.sum_image hinj
  _ ≤ ∏ p ∈ primesLE z, (1 / ((p : ℝ) - 1) + 1) := by rw [hexp]; exact hstep
  _ = ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) := by
        exact Finset.prod_congr rfl (fun p _ => by ring)

lemma log_le_harmonic_sum (z : ℕ) : Real.log z ≤ ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
  have h := log_add_one_le_harmonic z
  have h2 : ((harmonic z : ℚ) : ℝ) = ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl (fun n _ => by rw [one_div])
  rw [h2] at h
  refine le_trans ?_ h
  apply Real.log_le_log_of_le
  · push_cast; linarith
  · push_cast; linarith

/-- Euler's upper bound `∏_{p ≤ z} (1 - 1/p) ≤ 2 / log z`. -/
lemma prod_one_sub_inv_le (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ primesLE z, (1 - 1 / (p : ℝ)) ≤ 2 / Real.log z := by
  have hlog : 0 < Real.log z := by
    apply Real.log_pos
    exact_mod_cast hz
  have h1 : (1/2 : ℝ) * Real.log z ≤ ∑ a ∈ sqfreeLE z, (1 / (a : ℝ)) := by
    have := log_le_harmonic_sum z
    have := harmonic_le_two_mul_sum_sqfree z
    linarith
  have h2 : (1/2 : ℝ) * Real.log z ≤ ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) :=
    le_trans h1 (sum_sqfree_le_prod z)
  have hpos : (0:ℝ) < ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) := by
    linarith [h2, hlog]
  have hprodone : (∏ p ∈ primesLE z, (1 - 1 / (p : ℝ)))
      * ∏ p ∈ primesLE z, (1 + 1 / ((p : ℝ) - 1)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun p hp => ?_)
    have hp2 : 2 ≤ p := (mem_primesLE.mp hp).2.two_le
    have hp2' : (2:ℝ) ≤ p := by exact_mod_cast hp2
    field_simp
  rw [le_div_iff₀ hlog]
  nlinarith [hprodone, h2, hlog, hpos]

/-- The main-term bound for Brun's sieve. -/
lemma prod_oddPrimes_le (z : ℕ) (hz : 2 ≤ z) :
    ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ)) ≤ 16 / (Real.log z) ^ 2 := by
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)
  have hins : primesLE z = insert 2 (oddPrimes z) := by
    ext p
    simp only [mem_primesLE, Finset.mem_insert, mem_oddPrimes]
    constructor
    · rintro ⟨hpz, hp⟩
      by_cases h2 : p = 2
      · exact Or.inl h2
      · exact Or.inr ⟨hpz, hp, h2⟩
    · rintro (rfl | ⟨hpz, hp, -⟩)
      · exact ⟨hz, Nat.prime_two⟩
      · exact ⟨hpz, hp⟩
  have h2mem : (2:ℕ) ∉ oddPrimes z := by
    simp [mem_oddPrimes]
  have hsplit : ∏ p ∈ primesLE z, (1 - 1 / (p : ℝ))
      = (1/2) * ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) := by
    rw [hins, Finset.prod_insert h2mem]
    norm_num
  have hle : ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have := three_le_of_mem_oddPrimes hp
      have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    · have := three_le_of_mem_oddPrimes hp
      have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
      have hp0 : (0:ℝ) < p := by linarith
      rw [div_add_div_same, sub_sq]
      have : (1 / (p:ℝ)) ^ 2 ≥ 0 := by positivity
      have hh : 2 * 1 * (1 / (p:ℝ)) = 2 / p := by ring
      nlinarith [this]
  have hnn : 0 ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have := three_le_of_mem_oddPrimes hp
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast this
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hkey : ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ≤ 4 / Real.log z := by
    have := prod_one_sub_inv_le z hz
    rw [hsplit] at this
    linarith
  calc ∏ p ∈ oddPrimes z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ)) ^ 2 := hle
  _ = (∏ p ∈ oddPrimes z, (1 - 1 / (p : ℝ))) ^ 2 := by rw [Finset.prod_pow]
  _ ≤ (4 / Real.log z) ^ 2 := by
        apply pow_le_pow_left hnn hkey
  _ = 16 / (Real.log z) ^ 2 := by
        rw [div_pow]; norm_num

end Brun

import Mathlib

/-!
# Basic definitions for Brun's theorem on twin primes
-/

namespace Brun

open Finset

/-- The set of odd primes `≤ z`. -/
def oddPrimes (z : ℕ) : Finset ℕ := (range (z + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- The number of odd `n < N` such that every prime in `s` divides `n * (n + 2)`. -/
def sieveCount (N : ℕ) (s : Finset ℕ) : ℕ :=
  ((range N).filter (fun n => ¬ 2 ∣ n ∧ ∀ p ∈ s, p ∣ n * (n + 2))).card

/-- The number of odd `n < N` such that no odd prime `≤ z` divides `n * (n + 2)`. -/
def sifted (N z : ℕ) : ℕ :=
  ((range N).filter (fun n => ¬ 2 ∣ n ∧ ∀ p ∈ oddPrimes z, ¬ p ∣ n * (n + 2))).card

/-- The number of twin primes `p < N` (i.e. `p` and `p + 2` both prime). -/
def twinCount (N : ℕ) : ℕ := ((range N).filter (fun n => n.Prime ∧ (n + 2).Prime)).card

lemma mem_oddPrimes {z p : ℕ} : p ∈ oddPrimes z ↔ p ≤ z ∧ p.Prime ∧ p ≠ 2 := by
  simp [oddPrimes, Nat.lt_succ_iff, and_assoc]

lemma oddPrimes_prime {z p : ℕ} (h : p ∈ oddPrimes z) : p.Prime := (mem_oddPrimes.mp h).2.1

lemma three_le_of_mem_oddPrimes {z p : ℕ} (h : p ∈ oddPrimes z) : 3 ≤ p := by
  obtain ⟨-, hp, h2⟩ := mem_oddPrimes.mp h
  have := hp.two_le
  omega

end Brun

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

import RequestProject.Defs

/-!
# A weak Mertens-type upper bound

We show `∑_{p ≤ 2^J} 1/p ≤ 1/2 + 8 √J`, which is all the prime-density input Brun's
argument needs.  The only external input is Chebyshev's bound `primorial n ≤ 4 ^ n`.
-/

namespace Brun

open Finset

/-- The primes `≤ x`. -/
def primesLE (x : ℕ) : Finset ℕ := (range (x + 1)).filter Nat.Prime

lemma mem_primesLE {x p : ℕ} : p ∈ primesLE x ↔ p ≤ x ∧ p.Prime := by
  simp [primesLE, Nat.lt_succ_iff]

lemma prod_primesLE_le (x : ℕ) : ∏ p ∈ primesLE x, p ≤ 4 ^ x := primorial_le_4_pow x

/-- The primes in `(2^i, 2^(i+1)]`. -/
def block (i : ℕ) : Finset ℕ := (primesLE (2 ^ (i + 1))).filter (fun p => 2 ^ i < p)

lemma block_card_le (i : ℕ) : i * (block i).card ≤ 2 ^ (i + 2) := by
  have h1 : (2 ^ i) ^ (block i).card ≤ ∏ p ∈ block i, p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' ?_
    intro p hp
    exact le_of_lt (Finset.mem_filter.mp hp).2
  have h2 : ∏ p ∈ block i, p ≤ ∏ p ∈ primesLE (2 ^ (i + 1)), p := by
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    intro p hp _
    exact (mem_primesLE.mp hp).2.one_lt.le
  have h3 : ∏ p ∈ primesLE (2 ^ (i + 1)), p ≤ 4 ^ (2 ^ (i + 1)) := prod_primesLE_le _
  have h4 : (2:ℕ) ^ (i * (block i).card) ≤ 2 ^ (2 ^ (i + 2)) := by
    calc (2:ℕ) ^ (i * (block i).card) = (2 ^ i) ^ (block i).card := by rw [pow_mul]
    _ ≤ 4 ^ (2 ^ (i + 1)) := le_trans h1 (le_trans h2 h3)
    _ = 2 ^ (2 ^ (i + 2)) := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        ring_nf
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4

lemma sum_inv_block_le (i : ℕ) (hi : 1 ≤ i) :
    ∑ p ∈ block i, (1 / p : ℝ) ≤ 4 / i := by
  have hcard : ((block i).card : ℝ) ≤ 2 ^ (i + 2) / i := by
    have := block_card_le i
    rw [le_div_iff₀ (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hi)]
    calc ((block i).card : ℝ) * i = ((i * (block i).card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (i + 2) : ℕ) : ℝ) := by exact_mod_cast this
    _ = 2 ^ (i + 2) := by push_cast; ring
  have hstep : ∀ p ∈ block i, (1 / p : ℝ) ≤ 1 / 2 ^ i := by
    intro p hp
    have hp' : (2:ℝ) ^ i < p := by exact_mod_cast (Finset.mem_filter.mp hp).2
    have : (0:ℝ) < 2 ^ i := by positivity
    exact one_div_le_one_div_of_le this hp'.le
  calc ∑ p ∈ block i, (1 / p : ℝ) ≤ ∑ _p ∈ block i, (1 / 2 ^ i : ℝ) :=
        Finset.sum_le_sum hstep
  _ = (block i).card * (1 / 2 ^ i) := by rw [Finset.sum_const, nsmul_eq_mul]
  _ ≤ (2 ^ (i + 2) / i) * (1 / 2 ^ i) := by gcongr
  _ = 4 / i := by
        rw [pow_add]
        field_simp
        ring

lemma sum_inv_primesLE_pow_le (J : ℕ) :
    ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) ≤ 1 / 2 + ∑ i ∈ Ico 1 J, (4 / i : ℝ) := by
  induction J with
  | zero =>
    have h : primesLE (2 ^ 0) = ∅ := by
      ext p
      simp only [mem_primesLE, pow_zero, Finset.notMem_empty, iff_false, not_and]
      intro hp hpp
      have := hpp.two_le
      omega
    rw [h]; simp
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with rfl | hJ
    · have h : primesLE (2 ^ (0 + 1)) = {2} := by
        ext p
        simp only [mem_primesLE, Finset.mem_singleton, zero_add, pow_one]
        constructor
        · rintro ⟨hp, hpp⟩; have := hpp.two_le; omega
        · rintro rfl; exact ⟨le_rfl, Nat.prime_two⟩
      rw [h]; norm_num
    · have hsplit : ∑ p ∈ primesLE (2 ^ (J + 1)), (1 / p : ℝ)
          = ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) + ∑ p ∈ block J, (1 / p : ℝ) := by
        rw [← Finset.sum_filter_add_sum_filter_not (primesLE (2 ^ (J + 1)))
          (fun p => p ≤ 2 ^ J)]
        congr 1
        · congr 1
          ext p
          simp only [Finset.mem_filter, mem_primesLE]
          constructor
          · rintro ⟨⟨-, hp⟩, hle⟩; exact ⟨hle, hp⟩
          · rintro ⟨hle, hp⟩
            exact ⟨⟨hle.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), hp⟩, hle⟩
        · congr 1
          ext p
          simp only [Finset.mem_filter, block, not_le]
      rw [hsplit, Finset.sum_Ico_succ_top (by omega)]
      have := sum_inv_block_le J hJ
      linarith [ih]

lemma sum_inv_le_two_sqrt (J : ℕ) : ∑ i ∈ Icc 1 J, (1 / i : ℝ) ≤ 2 * Real.sqrt J := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ha : Real.sqrt J ^ 2 = J := Real.sq_sqrt (by positivity)
    have hb : Real.sqrt (J + 1) ^ 2 = (J : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hab : Real.sqrt J ≤ Real.sqrt (J + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hb1 : 1 ≤ Real.sqrt (J + 1) := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt ((J : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg J : (0:ℝ) ≤ J)])
      simpa using h1
    have key : 1 / ((J : ℝ) + 1) ≤ 2 * Real.sqrt (J + 1) - 2 * Real.sqrt J := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (J:ℝ), Real.sqrt_nonneg ((J:ℝ)+1)]
    push_cast
    push_cast at ih
    linarith

/-- The Mertens-type bound we need: the sum of `2/p` over odd primes `p ≤ 2^J`. -/
lemma sum_two_div_oddPrimes_le (J : ℕ) :
    ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ 1 + 16 * Real.sqrt J := by
  have hsub : oddPrimes (2 ^ J) ⊆ primesLE (2 ^ J) := by
    intro p hp
    rw [mem_oddPrimes] at hp
    exact mem_primesLE.mpr ⟨hp.1, hp.2.1⟩
  have h1 : ∑ p ∈ oddPrimes (2 ^ J), (2 / p : ℝ) ≤ ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _ _
    positivity
  have h2 : ∑ p ∈ primesLE (2 ^ J), (2 / p : ℝ) = 2 * ∑ p ∈ primesLE (2 ^ J), (1 / p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h3 := sum_inv_primesLE_pow_le J
  have h4 : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ 8 * Real.sqrt J := by
    have : ∑ i ∈ Ico 1 J, (4 / i : ℝ) ≤ ∑ i ∈ Icc 1 J, (4 / i : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      exact Finset.Ico_subset_Icc_self
    have h5 : ∑ i ∈ Icc 1 J, (4 / i : ℝ) = 4 * ∑ i ∈ Icc 1 J, (1 / i : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have := sum_inv_le_two_sqrt J
    linarith
  linarith

end Brun


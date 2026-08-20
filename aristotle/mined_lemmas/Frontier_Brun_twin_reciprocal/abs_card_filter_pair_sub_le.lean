import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma abs_card_filter_pair_sub_le (N a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) :
    |(((range N).filter (fun n => a ∣ n ∧ b ∣ (n + 2))).card : ℝ) - (N : ℝ) / (a * b)| ≤ 1 := by
  -- find a solution of the pair of congruences
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab 0 (b * b - 2)
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  set r := k % (a * b) with hr_def
  have hrlt : r < a * b := Nat.mod_lt _ hab0
  have hkr : r ≡ k [MOD a * b] := Nat.mod_modEq k (a * b)
  have hra : a ∣ r := by
    have : r ≡ k [MOD a] := hkr.of_dvd ⟨b, rfl⟩
    have : r ≡ 0 [MOD a] := this.trans hk1
    simpa [Nat.modEq_zero_iff_dvd] using this
  have hrb : b ∣ r + 2 := by
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · interval_cases b
      · exact one_dvd _
    · have h2 : r ≡ k [MOD b] := hkr.of_dvd ⟨a, mul_comm a b⟩
      have h3 : r ≡ b * b - 2 [MOD b] := h2.trans hk2
      have h4 : r + 2 ≡ (b * b - 2) + 2 [MOD b] := h3.add_right 2
      have h5 : (b * b - 2) + 2 = b * b := by
        have : 2 ≤ b * b := by nlinarith
        omega
      rw [h5] at h4
      have : b ∣ b * b := ⟨b, rfl⟩
      exact (Nat.modEq_zero_iff_dvd.mp (h4.trans ((Nat.modEq_zero_iff_dvd).mpr this)))
  have hset : (range N).filter (fun n => a ∣ n ∧ b ∣ (n + 2))
      = (range N).filter (fun n => n % (a * b) = r) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    constructor
    · rintro ⟨hna, hnb⟩
      have e1 : n ≡ r [MOD a] := by
        have h1 : n ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hna
        have h2 : r ≡ 0 [MOD a] := (Nat.modEq_zero_iff_dvd).mpr hra
        exact h1.trans h2.symm
      have e2 : n ≡ r [MOD b] := by
        have h1 : n + 2 ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr hnb
        have h2 : r + 2 ≡ 0 [MOD b] := (Nat.modEq_zero_iff_dvd).mpr hrb
        have : n + 2 ≡ r + 2 [MOD b] := h1.trans h2.symm
        exact Nat.ModEq.add_right_cancel' 2 this
      have : n ≡ r [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨e1, e2⟩
      calc n % (a * b) = r % (a * b) := this
        _ = r := Nat.mod_eq_of_lt hrlt
    · intro hn
      have hmod : n ≡ r [MOD a * b] := by
        unfold Nat.ModEq
        rw [hn, Nat.mod_eq_of_lt hrlt]
      have e1 : n ≡ r [MOD a] := hmod.of_dvd ⟨b, rfl⟩
      have e2 : n ≡ r [MOD b] := hmod.of_dvd ⟨a, mul_comm a b⟩
      refine ⟨?_, ?_⟩
      · have : n ≡ 0 [MOD a] := e1.trans ((Nat.modEq_zero_iff_dvd).mpr hra)
        exact (Nat.modEq_zero_iff_dvd).mp this
      · have h1 : n + 2 ≡ r + 2 [MOD b] := e2.add_right 2
        have : n + 2 ≡ 0 [MOD b] := h1.trans ((Nat.modEq_zero_iff_dvd).mpr hrb)
        exact (Nat.modEq_zero_iff_dvd).mp this
  rw [hset]
  have := abs_card_filter_mod_sub_le N (a * b) r hrlt
  simpa using this

/-- The fibre decomposition of the set counted by `dvdCount`. -/

/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Same Parity Betrothed Exists
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.SameParityBetrothedExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset

/-- A pair of *betrothed* (quasi-amicable) numbers: two distinct positive integers each of
whose sum of divisors equals the sum of the two numbers plus one. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The smallest betrothed pair, `(48, 75)`; it has *opposite* parity. -/
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-- The (open) statement that a betrothed pair of the same parity exists. -/
def SameParityBetrothedPairExists : Prop :=
  ∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2

/-- For an odd prime `p`, if `σ (p ^ e)` is odd then `e` is even. -/
theorem odd_sigma_prime_pow {p e : ℕ} (hp : p.Prime) (hodd : p % 2 = 1)
    (h : Odd (sigma 1 (p ^ e))) : Even e := by
  rw [sigma_one_apply_prime_pow hp] at h
  have key : ∀ k : ℕ, (∑ j ∈ Finset.range (k + 1), p ^ j) % 2 = (k + 1) % 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hpk : p ^ (k + 1) % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd).pow)
        omega
  rw [Nat.odd_iff, key] at h
  rw [Nat.even_iff]
  omega

/-- If `m` is odd and `σ m` is odd, then `m` is a perfect square. -/
theorem isSquare_of_odd_of_odd_sigma :
    ∀ m : ℕ, 0 < m → m % 2 = 1 → Odd (sigma 1 m) → IsSquare m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hodd hs
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm.ne') with h1 | h1
    · exact ⟨1, by omega⟩
    · set p := m.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      have hpodd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h2 | h2
        · exfalso
          rw [h2] at hpdvd
          omega
        · exact h2
      set e := m.factorization p
      set m' := ordCompl[p] m
      have hsplit : p ^ e * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
      have hcop : Nat.Coprime (p ^ e) m' :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp (by omega))
      have hmul : sigma 1 m = sigma 1 (p ^ e) * sigma 1 m' := by
        rw [← hsplit]
        exact isMultiplicative_sigma.map_mul_of_coprime hcop
      rw [hmul] at hs
      obtain ⟨hs1, hs2⟩ := Nat.odd_mul.mp hs
      have heven : Even e := odd_sigma_prime_pow hp hpodd hs1
      have hm'pos : 0 < m' := Nat.ordCompl_pos p (by omega)
      have hm'odd : m' % 2 = 1 := by
        have hdvd : m' ∣ m := Nat.ordCompl_dvd m p
        rcases Nat.even_or_odd m' with h | h
        · exfalso
          have : (2 : ℕ) ∣ m := dvd_trans (even_iff_two_dvd.mp h) hdvd
          omega
        · exact Nat.odd_iff.mp h
      have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpdvd
      have hplt : 1 < p ^ e := by
        calc 1 < p := hp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
      have hlt : m' < m := by
        calc m' = 1 * m' := (one_mul m').symm
        _ < p ^ e * m' := Nat.mul_lt_mul_of_lt_of_le hplt (le_refl m') hm'pos
        _ = m := hsplit
      obtain ⟨c, hc⟩ := ih m' hlt hm'pos hm'odd hs2
      obtain ⟨k, hk⟩ := heven
      refine ⟨p ^ k * c, ?_⟩
      rw [← hsplit, hc, hk]
      ring

/-- If `σ n` is odd (`n > 0`), then `n = 2 ^ a * b ^ 2` for some `a`, `b`. -/
theorem eq_two_pow_mul_sq_of_odd_sigma {n : ℕ} (hn : 0 < n) (h : Odd (sigma 1 n)) :
    ∃ a b : ℕ, 0 < b ∧ n = 2 ^ a * b ^ 2 := by
  set a := n.factorization 2
  set m := ordCompl[2] n
  have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two (by omega))
  have hmul : sigma 1 n = sigma 1 (2 ^ a) * sigma 1 m := by
    rw [← hsplit]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul] at h
  have hs2 : Odd (sigma 1 m) := (Nat.odd_mul.mp h).2
  have hmpos : 0 < m := Nat.ordCompl_pos 2 (by omega)
  have hmodd : m % 2 = 1 := by
    have := Nat.not_dvd_ordCompl Nat.prime_two (n := n) (by omega)
    omega
  obtain ⟨c, hc⟩ := isSquare_of_odd_of_odd_sigma m hmpos hmodd hs2
  refine ⟨a, c, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · simp at hc; omega
    · exact hcpos
  · rw [← hsplit, hc]; ring

/-- In a same-parity betrothed pair, the common value `σ m = σ n = m + n + 1` is odd. -/
theorem odd_sigma_of_sameParity {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    Odd (sigma 1 m) ∧ Odd (sigma 1 n) := by
  obtain ⟨-, -, -, hm, hn⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.odd_iff]; omega
  · rw [hn, Nat.odd_iff]; omega

/-- **Structure of a hypothetical same-parity betrothed pair.**
Both members of a betrothed pair of equal parity are of the form `2 ^ a * b ^ 2`. -/
theorem sameParity_betrothed_structure {m n : ℕ} (h : Betrothed m n) (hpar : m % 2 = n % 2) :
    (∃ a b : ℕ, 0 < b ∧ m = 2 ^ a * b ^ 2) ∧ (∃ a b : ℕ, 0 < b ∧ n = 2 ^ a * b ^ 2) := by
  obtain ⟨hm, hn⟩ := odd_sigma_of_sameParity h hpar
  exact ⟨eq_two_pow_mul_sq_of_odd_sigma h.1 hm, eq_two_pow_mul_sq_of_odd_sigma h.2.1 hn⟩

/-- A betrothed pair of two odd numbers would consist of two perfect squares. -/
theorem isSquare_of_odd_betrothed {m n : ℕ} (h : Betrothed m n) (hm : m % 2 = 1)
    (hn : n % 2 = 1) : IsSquare m ∧ IsSquare n := by
  have hpar : m % 2 = n % 2 := by omega
  obtain ⟨hm2, hn2⟩ := odd_sigma_of_sameParity h hpar
  have key : ∀ k : ℕ, k % 2 = 1 → (∃ a b : ℕ, 0 < b ∧ k = 2 ^ a * b ^ 2) → IsSquare k := by
    rintro k hk ⟨a, b, -, rfl⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨b, by ring⟩
    · exfalso
      have : (2 : ℕ) ∣ 2 ^ a * b ^ 2 := Dvd.dvd.mul_right (dvd_pow_self 2 ha.ne') _
      omega
  exact ⟨key m hm (eq_two_pow_mul_sq_of_odd_sigma h.1 hm2),
    key n hn (eq_two_pow_mul_sq_of_odd_sigma h.2.1 hn2)⟩

/-- **Same Parity Betrothed Exists (conditional reduction).**

Whether a betrothed (quasi-amicable) pair of the same parity exists is an open problem: all
known betrothed pairs consist of one even and one odd number.  What is proved here is the
equivalence of that open existence statement with the a priori much more restrictive
statement that a same-parity betrothed pair exists both of whose members have the shape
`2 ^ a * b ^ 2`.  In particular, if both members are odd they must both be perfect squares. -/
theorem SameParityBetrothedExists :
    SameParityBetrothedPairExists ↔
      ∃ m n : ℕ, Betrothed m n ∧ m % 2 = n % 2 ∧
        (∃ a b : ℕ, 0 < b ∧ m = 2 ^ a * b ^ 2) ∧ (∃ a b : ℕ, 0 < b ∧ n = 2 ^ a * b ^ 2) := by
  constructor
  · rintro ⟨m, n, h, hpar⟩
    obtain ⟨h1, h2⟩ := sameParity_betrothed_structure h hpar
    exact ⟨m, n, h, hpar, h1, h2⟩
  · rintro ⟨m, n, h, hpar, -, -⟩
    exact ⟨m, n, h, hpar⟩

end Brockian.BetrothedNumbers


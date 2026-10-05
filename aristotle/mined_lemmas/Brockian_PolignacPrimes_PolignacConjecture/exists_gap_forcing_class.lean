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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean requires `import` commands to come before any module docstring, so the header
-- above appears both at the very top of the file (as a plain comment) and here, after the
-- import, as the module docstring.

namespace Brockian.PolignacPrimes

/-- `GapOccursInfinitelyOften n` says that there are infinitely many pairs of *consecutive*
primes whose difference is exactly `n`: for every bound `N` there is a prime `p > N` such that
`p + n` is prime and no integer strictly between `p` and `p + n` is prime. -/

lemma exists_gap_forcing_class (n : ℕ) (hn : Even n) :
    ∀ k : ℕ, k < n → ∃ M a : ℕ, 0 < M ∧ 2 ∣ M ∧ Nat.Coprime a M ∧ Nat.Coprime (a + n) M ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k → ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ q ∣ a + j := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨2, 1, by norm_num, dvd_rfl, by norm_num, ?_, ?_⟩
    · have h : ¬ (2 ∣ (1 + n)) := by obtain ⟨m, rfl⟩ := hn; omega
      exact ((Nat.prime_two.coprime_iff_not_dvd).mpr h).symm
    · intro j h1 h2; omega
  | succ k ih =>
    intro hk
    obtain ⟨M, a, hM0, hM2, hcop, hcop', hforce⟩ := ih (by omega)
    obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max M n + 1)
    have hqM : M < q := by have := le_max_left M n; omega
    have hqn : n < q := by have := le_max_right M n; omega
    have hqdvd : ¬ q ∣ M := fun h => absurd (Nat.le_of_dvd hM0 h) (by omega)
    have hcoMq : Nat.Coprime M q := ((hq.coprime_iff_not_dvd).mpr hqdvd).symm
    obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcoMq a (q - (k + 1))
    have hbM : Nat.Coprime b M := by
      have := hb1.gcd_eq
      unfold Nat.Coprime at *
      omega
    have hbq : Nat.Coprime b q := by
      refine ((hq.coprime_iff_not_dvd).mpr ?_).symm
      intro hdvd
      have h0 : b ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have hd : q ∣ (q - (k + 1)) := (Nat.modEq_zero_iff_dvd).mp (hb2.symm.trans h0)
      have := Nat.le_of_dvd (by omega) hd
      omega
    have hbnM : Nat.Coprime (b + n) M := by
      have := (hb1.add_right n).gcd_eq
      unfold Nat.Coprime at *
      omega
    have hbnq : Nat.Coprime (b + n) q := by
      refine ((hq.coprime_iff_not_dvd).mpr ?_).symm
      intro hdvd
      have h0 : (b + n) ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr hdvd
      have hd : q ∣ (q - (k + 1) + n) :=
        (Nat.modEq_zero_iff_dvd).mp ((hb2.add_right n).symm.trans h0)
      have hq2 : q ∣ (n - (k + 1)) := by
        have hrw : q - (k + 1) + n = q + (n - (k + 1)) := by omega
        rw [hrw] at hd
        exact (Nat.dvd_add_right dvd_rfl).mp hd
      have := Nat.le_of_dvd (by omega) hq2
      omega
    refine ⟨M * q, b, Nat.mul_pos hM0 hq.pos, Dvd.dvd.mul_right hM2 q, hbM.mul_right hbq,
      hbnM.mul_right hbnq, ?_⟩
    intro j hj1 hj2
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · obtain ⟨r, hr, hrM, hra⟩ := hforce j hj1 (by omega)
      refine ⟨r, hr, hrM.mul_right q, ?_⟩
      have hbr : (b + j) ≡ (a + j) [MOD r] := (hb1.of_dvd hrM).add_right j
      have h0 : (a + j) ≡ 0 [MOD r] := (Nat.modEq_zero_iff_dvd).mpr hra
      exact (Nat.modEq_zero_iff_dvd).mp (hbr.trans h0)
    · have hjeq : j = k + 1 := by omega
      subst hjeq
      refine ⟨q, hq, dvd_mul_left q M, ?_⟩
      have hb3 : (b + (k + 1)) ≡ (q - (k + 1) + (k + 1)) [MOD q] := hb2.add_right _
      have heq : q - (k + 1) + (k + 1) = q := by omega
      rw [heq] at hb3
      have h0 : q ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr dvd_rfl
      exact (Nat.modEq_zero_iff_dvd).mp (hb3.trans h0)

/-- **Conditional proof of the de Polignac conjecture.**

The de Polignac conjecture is open.  What is proved here is a reduction: the full conjecture
(every positive even number is infinitely often the gap between *consecutive* primes) follows
from `DicksonPairHypothesis`, the qualitative Dickson/Hardy–Littlewood hypothesis on prime
pairs in arithmetic progressions.  The point of the reduction is that the hypothesis says
nothing about consecutiveness; consecutiveness is obtained by forcing all the intermediate
integers to be composite through a congruence condition. -/

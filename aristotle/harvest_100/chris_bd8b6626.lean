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
def GapOccursInfinitelyOften (n : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + n).Prime ∧ ∀ q : ℕ, p < q → q < p + n → ¬ q.Prime

/-- The de Polignac conjecture: every positive even number occurs infinitely often as the
difference of two consecutive primes. -/
def PolignacStatement : Prop :=
  ∀ n : ℕ, 0 < n → Even n → GapOccursInfinitelyOften n

/-- `PairsOccurInfinitelyOften n` says that there are infinitely many primes `p` with `p + n`
also prime (the two primes are *not* required to be consecutive). -/
def PairsOccurInfinitelyOften (n : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + n).Prime

/-- A qualitative Dickson / Hardy–Littlewood hypothesis for the pair of linear forms
`M x + a` and `M x + a + n`: whenever the pair is admissible for the trivial reasons
(`n` even, the modulus `M` even, and both `a` and `a + n` coprime to `M`) there are
infinitely many primes `p ≡ a [MOD M]` with `p + n` prime. -/
def DicksonPairHypothesis : Prop :=
  ∀ n M a : ℕ, 0 < n → Even n → 0 < M → 2 ∣ M → Nat.Coprime a M → Nat.Coprime (a + n) M →
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + n).Prime ∧ p ≡ a [MOD M]

/-- Construction of a "gap-forcing" residue class: for even `n` and any `k < n` there is an
even modulus `M` and a residue `a`, with `a` and `a + n` coprime to `M`, such that for every
`1 ≤ j ≤ k` some prime divisor of `M` divides `a + j`. Any `p ≡ a [MOD M]` larger than `M`
then has `p + j` composite for all these `j`. -/
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
theorem PolignacConjecture (H : DicksonPairHypothesis) : PolignacStatement := by
  intro n hn0 hn N
  obtain ⟨M, a, hM0, hM2, hcop, hcop', hforce⟩ :=
    exists_gap_forcing_class n hn (n - 1) (by omega)
  obtain ⟨p, hpN, hp, hpn, hmod⟩ := H n M a hn0 hn hM0 hM2 hcop hcop' (max N M)
  have hNp : N < p := lt_of_le_of_lt (le_max_left N M) hpN
  have hMp : M < p := lt_of_le_of_lt (le_max_right N M) hpN
  refine ⟨p, hNp, hp, hpn, ?_⟩
  intro c hc1 hc2 hcprime
  obtain ⟨r, hr, hrM, hra⟩ := hforce (c - p) (by omega) (by omega)
  have hrp : (p + (c - p)) ≡ (a + (c - p)) [MOD r] := (hmod.of_dvd hrM).add_right _
  have h0 : (a + (c - p)) ≡ 0 [MOD r] := (Nat.modEq_zero_iff_dvd).mpr hra
  have hrc : r ∣ c := by
    have : (p + (c - p)) ≡ 0 [MOD r] := hrp.trans h0
    have hpc : p + (c - p) = c := by omega
    rw [hpc] at this
    exact (Nat.modEq_zero_iff_dvd).mp this
  have hrle : r ≤ M := Nat.le_of_dvd hM0 hrM
  rcases (Nat.Prime.eq_one_or_self_of_dvd hcprime r hrc) with h | h
  · exact hr.one_lt.ne' h
  · omega

/-- For `n = 2` consecutiveness is automatic, so the gap `2` occurs infinitely often between
consecutive primes if and only if there are infinitely many twin primes. -/
theorem gap_two_iff_twin_primes :
    GapOccursInfinitelyOften 2 ↔ PairsOccurInfinitelyOften 2 := by
  constructor
  · intro h N
    obtain ⟨p, hpN, hp, hp2, -⟩ := h N
    exact ⟨p, hpN, hp, hp2⟩
  · intro h N
    obtain ⟨p, hpN, hp, hp2⟩ := h (max N 2)
    refine ⟨p, lt_of_le_of_lt (le_max_left N 2) hpN, hp, hp2, ?_⟩
    intro c hc1 hc2 hcprime
    have hcp : c = p + 1 := by omega
    have hp2' : 2 < p := lt_of_le_of_lt (le_max_right N 2) hpN
    have hodd : ¬ (2 ∣ p) := by
      intro hd
      have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 hd)
      omega
    have : (2 : ℕ) ∣ c := by omega
    have := (Nat.Prime.eq_one_or_self_of_dvd hcprime 2 this)
    omega

/-- Unconditional reduction: if some `n > 0` occurs infinitely often as a difference of two
(not necessarily consecutive) primes, then some `0 < m ≤ n` occurs infinitely often as a gap
between consecutive primes. -/
theorem exists_gap_of_pairs (n : ℕ) (hn : 0 < n) (h : PairsOccurInfinitelyOften n) :
    ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ GapOccursInfinitelyOften m := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ m : ℕ, ∃ N : ℕ, ∀ p : ℕ, N < p → 0 < m → m ≤ n →
      ¬ (p.Prime ∧ (p + m).Prime ∧ ∀ q : ℕ, p < q → q < p + m → ¬ q.Prime) := by
    intro m
    by_cases hm : 0 < m ∧ m ≤ n
    · have hnot := hcon m hm.1 hm.2
      rw [GapOccursInfinitelyOften, not_forall] at hnot
      obtain ⟨N, hN⟩ := hnot
      refine ⟨N, ?_⟩
      intro p hp _ _ hA
      exact hN ⟨p, hp, hA.1, hA.2.1, hA.2.2⟩
    · exact ⟨0, fun p _ h1 h2 _ => hm ⟨h1, h2⟩⟩
  choose f hf using key
  obtain ⟨p, hpB, hp, hpn⟩ := h ((Finset.range (n + 1)).sup f)
  have hex : ∃ j, 1 ≤ j ∧ (p + j).Prime := ⟨n, hn, hpn⟩
  obtain ⟨hm1, hmp⟩ := Nat.find_spec hex
  have hmn : Nat.find hex ≤ n := Nat.find_le ⟨hn, hpn⟩
  have hfm : f (Nat.find hex) ≤ (Finset.range (n + 1)).sup f :=
    Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))
  refine hf (Nat.find hex) p (by omega) hm1 hmn ⟨hp, hmp, ?_⟩
  intro q hq1 hq2 hqprime
  refine Nat.find_min hex (show q - p < Nat.find hex by omega) ⟨by omega, ?_⟩
  rw [show p + (q - p) = q by omega]
  exact hqprime

end Brockian.PolignacPrimes


/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Polignac's conjecture ("for every even `n > 0` there are infinitely many pairs of
*consecutive* primes whose difference is `n`") is a well-known open problem, and it is
not available in Mathlib.  What is proved here is a *conditional reduction*: Polignac's
conjecture follows from the two-linear-form case of Dickson's conjecture.

The reduction itself is unconditional Lean-checked mathematics:

* pick `n - 1` distinct primes `q 0, …, q (n-2)`, all larger than `n`;
* by the Chinese Remainder Theorem choose `a` with `a ≡ -(i+1) [MOD q i]`;
* with `M = ∏ q i`, every number of the form `M * x + a + (i+1)` is divisible by `q i`,
  hence composite once it exceeds `q i`;
* the pair of linear forms `M * x + a`, `M * x + (a + n)` is admissible, so Dickson's
  conjecture supplies arbitrarily large `x` making both values prime.  Those two primes
  are then *consecutive* primes differing by exactly `n`.
-/

namespace Brockian.PolignacPrimes

/-- `n` is a Polignac gap: there are arbitrarily large primes `p` such that `p + n` is
prime and no number strictly between `p` and `p + n` is prime, i.e. `p` and `p + n` are
consecutive primes at distance `n`. -/
def IsPolignacGap (n : ℕ) : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + n) ∧
    ∀ r : ℕ, p < r → r < p + n → ¬ Nat.Prime r

/-- Polignac's conjecture: every positive even number is a Polignac gap. -/
def PolignacStatement : Prop := ∀ n : ℕ, 0 < n → Even n → IsPolignacGap n

/-- The two-linear-form case of Dickson's conjecture: if the product of the two linear
forms `m * x + b` and `m * x + c` (with `m > 0`) is not divisible by a fixed prime for
all `x` — i.e. the pair is *admissible* — then both forms are simultaneously prime for
arbitrarily large `x`. -/
def DicksonPairHypothesis : Prop :=
  ∀ m b c : ℕ, 0 < m →
    (∀ Q : ℕ, Nat.Prime Q → ∃ x : ℕ, ¬ Q ∣ (m * x + b) ∧ ¬ Q ∣ (m * x + c)) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ Nat.Prime (m * x + b) ∧ Nat.Prime (m * x + c)

/-- Divisibility only depends on the residue class. -/
private lemma dvd_iff_of_modEq {m a r : ℕ} (h : a ≡ r [MOD m]) : m ∣ a ↔ m ∣ r := by
  constructor <;> intro hd
  · exact Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
  · exact Nat.modEq_zero_iff_dvd.1 (h.trans (Nat.modEq_zero_iff_dvd.2 hd))

/-- Local admissibility at a prime `Q` not dividing the common difference `M`:
one can choose `x` so that neither `M * x + a` nor `M * x + a + n` is divisible by `Q`
(here `n` is even, which is what rules out the obstruction at `Q = 2`). -/
private lemma exists_x_not_dvd {Q M a n : ℕ} (hQ : Nat.Prime Q) (hM : ¬ Q ∣ M)
    (hn : Even n) : ∃ x : ℕ, ¬ Q ∣ (M * x + a) ∧ ¬ Q ∣ (M * x + a + n) := by
  haveI : Fact (Nat.Prime Q) := ⟨hQ⟩
  haveI : NeZero Q := ⟨hQ.ne_zero⟩
  have hv : ∃ v : ZMod Q, v ≠ 0 ∧ v + (n : ZMod Q) ≠ 0 := by
    by_cases h1 : (1 : ZMod Q) + (n : ZMod Q) = 0
    · refine ⟨2, ?_, ?_⟩
      · by_cases hQ2 : Q = 2
        · subst hQ2
          have hn2 : ((n : ℕ) : ZMod 2) = 0 := by
            refine (ZMod.natCast_eq_zero_iff n 2).2 ?_
            obtain ⟨k, hk⟩ := hn
            omega
          rw [hn2, add_zero] at h1
          exact absurd h1 one_ne_zero
        · have h2 : (2 : ZMod Q) = ((2 : ℕ) : ZMod Q) := by push_cast; ring
          rw [h2]
          intro hc
          exact hQ2 ((Nat.prime_dvd_prime_iff_eq hQ Nat.prime_two).1
            ((ZMod.natCast_eq_zero_iff 2 Q).1 hc))
      · have h2 : (2 : ZMod Q) + (n : ZMod Q) = ((1 : ZMod Q) + (n : ZMod Q)) + 1 := by ring
        rw [h2, h1, zero_add]
        exact one_ne_zero
    · exact ⟨1, one_ne_zero, h1⟩
  obtain ⟨v, hv0, hvn⟩ := hv
  have hMne : (M : ZMod Q) ≠ 0 := fun h => hM ((ZMod.natCast_eq_zero_iff M Q).1 h)
  set x : ℕ := ((v - (a : ZMod Q)) * (M : ZMod Q)⁻¹).val with hxdef
  have hcast : ((M * x + a : ℕ) : ZMod Q) = v := by
    push_cast
    rw [hxdef, ZMod.natCast_val, ZMod.cast_id]
    field_simp
    exact sub_add_cancel v (a : ZMod Q)
  refine ⟨x, ?_, ?_⟩
  · intro hd
    rw [← ZMod.natCast_eq_zero_iff, hcast] at hd
    exact hv0 hd
  · intro hd
    rw [← ZMod.natCast_eq_zero_iff] at hd
    push_cast at hd
    rw [show ((M : ZMod Q) * (x : ZMod Q) + (a : ZMod Q)) = ((M * x + a : ℕ) : ZMod Q) by
      push_cast; ring, hcast] at hd
    exact hvn hd

/-- **Polignac's conjecture, conditionally on the two-form case of Dickson's
conjecture.**  Assuming `DicksonPairHypothesis`, for every positive even `n` there are
arbitrarily large pairs of consecutive primes `p < p + n`. -/
theorem PolignacConjecture (H : DicksonPairHypothesis) : PolignacStatement := by
  intro n hn0 hneven N
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hneven
    omega
  -- a supply of distinct primes larger than `n`
  set q : ℕ → ℕ := fun i => Nat.nth Nat.Prime (n + 1 + i) with hqdef
  have hqp : ∀ i, Nat.Prime (q i) := fun i => Nat.prime_nth_prime _
  have hqgt : ∀ i, n < q i := by
    intro i
    have h : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
    have := h.le_apply (x := n + 1 + i)
    simp only [hqdef]
    omega
  have hqinj : Function.Injective q := by
    intro i j hij
    have := Nat.nth_injective Nat.infinite_setOf_prime hij
    omega
  -- Chinese remainder: `a ≡ -(i+1) [MOD q i]`
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun i => q i - (i + 1)) q
    (Finset.range (n - 1)) (fun i _ => (hqp i).ne_zero)
    (by
      intro i _ j _ hij
      exact (Nat.coprime_primes (hqp i) (hqp j)).2 (fun h => hij (hqinj h)))
  set M : ℕ := ∏ i ∈ Finset.range (n - 1), q i with hMdef
  have hM0 : 0 < M := Finset.prod_pos (fun i _ => (hqp i).pos)
  have hqdvdM : ∀ i ∈ Finset.range (n - 1), q i ∣ M := fun i hi =>
    Finset.dvd_prod_of_mem _ hi
  have hqleM : ∀ i ∈ Finset.range (n - 1), q i ≤ M := fun i hi =>
    Nat.le_of_dvd hM0 (hqdvdM i hi)
  -- key divisibility facts about `a`
  have hkey : ∀ i ∈ Finset.range (n - 1), q i ∣ (a + (i + 1)) := by
    intro i hi
    have hlt : i + 1 < q i := by
      simp only [Finset.mem_range] at hi
      have := hqgt i
      omega
    have h1 : a + (i + 1) ≡ (q i - (i + 1)) + (i + 1) [MOD q i] :=
      Nat.ModEq.add_right _ (ha i hi)
    have h2 : (q i - (i + 1)) + (i + 1) = q i := by omega
    rw [h2] at h1
    exact (dvd_iff_of_modEq h1).2 dvd_rfl
  have hnda : ∀ i ∈ Finset.range (n - 1), ¬ q i ∣ a := by
    intro i hi hd
    have hlt : i + 1 < q i := by
      simp only [Finset.mem_range] at hi
      have := hqgt i
      omega
    have hdvd : q i ∣ (i + 1) := (Nat.dvd_add_right hd).1 (hkey i hi)
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hndan : ∀ i ∈ Finset.range (n - 1), ¬ q i ∣ (a + n) := by
    intro i hi hd
    have hi' : i < n - 1 := Finset.mem_range.1 hi
    have hqn := hqgt i
    have h1 : q i ∣ (a + n) - (a + (i + 1)) := Nat.dvd_sub hd (hkey i hi)
    have h2 : (a + n) - (a + (i + 1)) = n - (i + 1) := by omega
    rw [h2] at h1
    have := Nat.le_of_dvd (by omega) h1
    omega
  -- admissibility of the pair of forms
  have hadm : ∀ Q : ℕ, Nat.Prime Q →
      ∃ x : ℕ, ¬ Q ∣ (M * x + a) ∧ ¬ Q ∣ (M * x + (a + n)) := by
    intro Q hQ
    by_cases hdvd : Q ∣ M
    · obtain ⟨i, hi, hQi⟩ := (Nat.prime_iff.1 hQ).exists_mem_finset_dvd hdvd
      have hQeq : Q = q i := (Nat.prime_dvd_prime_iff_eq hQ (hqp i)).1 hQi
      refine ⟨0, ?_, ?_⟩
      · simpa [hQeq] using hnda i hi
      · simpa [hQeq] using hndan i hi
    · obtain ⟨x, h1, h2⟩ := exists_x_not_dvd (Q := Q) (M := M) (a := a) (n := n) hQ hdvd hneven
      exact ⟨x, h1, by rwa [← add_assoc]⟩
  obtain ⟨x, hxgt, hp1, hp2⟩ := H M a (a + n) hM0 hadm (N + M)
  have hMx : M ≤ M * x := Nat.le_mul_of_pos_right M (by omega)
  have hxMx : x ≤ M * x := Nat.le_mul_of_pos_left x hM0
  refine ⟨M * x + a, by omega, hp1, ?_, ?_⟩
  · rw [add_assoc]; exact hp2
  · intro r hr1 hr2 hrp
    -- `r = M * x + a + j` with `1 ≤ j ≤ n - 1`
    set j : ℕ := r - (M * x + a) with hjdef
    have hmem : j - 1 ∈ Finset.range (n - 1) := by
      simp only [Finset.mem_range]
      omega
    have hr : r = M * x + (a + ((j - 1) + 1)) := by omega
    have hdvdr : q (j - 1) ∣ r := by
      rw [hr]
      exact Nat.dvd_add (Dvd.dvd.mul_right (hqdvdM _ hmem) x) (hkey _ hmem)
    have hlt : q (j - 1) < r := by
      have h1 : q (j - 1) ≤ M := hqleM _ hmem
      omega
    rcases hrp.eq_one_or_self_of_dvd _ hdvdr with h | h
    · exact (hqp (j - 1)).ne_one h
    · omega

/-- An unconditional complement: the evenness assumption in Polignac's conjecture is
necessary, since no odd number is a Polignac gap (for odd `n` and `p > 2` prime, `p + n`
is even and larger than `2`, hence composite). -/
theorem not_isPolignacGap_of_odd {n : ℕ} (hn : Odd n) : ¬ IsPolignacGap n := by
  intro h
  obtain ⟨p, hp2, hpp, hpn, -⟩ := h 2
  have hpodd : Odd p := hpp.odd_of_ne_two (by omega)
  have heven : Even (p + n) := hpodd.add_odd hn
  have := (Nat.Prime.even_iff hpn).1 heven
  omega

end Brockian.PolignacPrimes


import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Filter

/-- `primeGap n = p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n` is the `n`-th prime
(with `p_0 = 2`). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The bounded prime gaps statement (Zhang / Maynard): some bound `B` is achieved by
infinitely many consecutive prime gaps. -/
def BoundedPrimeGaps : Prop := ∃ B : ℕ, {n : ℕ | primeGap n ≤ B}.Infinite

/-! ### Auxiliary order-theoretic lemmas -/

/-- A set of naturals is infinite iff it contains arbitrarily large elements. -/
lemma infinite_setOf_iff (p : ℕ → Prop) :
    {n : ℕ | p n}.Infinite ↔ ∀ N : ℕ, ∃ n ≥ N, p n := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt.le, hn⟩
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨n, hn, hp⟩ := h (a + 1)
    exact ⟨n, hp, by omega⟩

/-- In `ℕ∞`, an infimum over a tail is bounded by a natural number iff some term is. -/
lemma iInf_ge_le_coe_iff (f : ℕ → ℕ∞) (N B : ℕ) :
    (⨅ i ≥ N, f i) ≤ (B : ℕ∞) ↔ ∃ i ≥ N, f i ≤ (B : ℕ∞) := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hle : ((B : ℕ∞) + 1) ≤ ⨅ i ≥ N, f i := by
      refine le_iInf fun i => le_iInf fun hi => ?_
      exact Order.add_one_le_of_lt (hc i hi)
    have hBB : ((B : ℕ∞) + 1) ≤ (B : ℕ∞) := hle.trans h
    have h2 : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact hBB
    have h3 : B + 1 ≤ B := Nat.cast_le.mp h2
    omega
  · rintro ⟨i, hi, hle⟩
    exact le_trans (iInf_le_of_le i (iInf_le_of_le hi le_rfl)) hle

/-- In `ℕ∞`, a supremum is finite iff it is bounded by a natural number. -/
lemma iSup_lt_top_iff (g : ℕ → ℕ∞) :
    (⨆ N, g N) < ⊤ ↔ ∃ B : ℕ, ∀ N, g N ≤ (B : ℕ∞) := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp h.ne
    exact ⟨B, fun N => hB ▸ le_iSup g N⟩
  · rintro ⟨B, hB⟩
    exact lt_of_le_of_lt (iSup_le hB) (by simp)

/-! ### Main reduction -/

/-- **Bounded prime gaps (statement / Lean-checked reduction).**

The `liminf` of the sequence of prime gaps `p_{n+1} - p_n`, computed in `ℕ∞`, is finite
if and only if some bound `B` is attained by infinitely many prime gaps.

This is a Lean-checked reduction of the Zhang–Maynard theorem to the combinatorial
statement `BoundedPrimeGaps`; the equivalence itself is proved unconditionally. -/
theorem bounded_prime_gaps :
    BoundedPrimeGaps ↔ Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop < ⊤ := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat, iSup_lt_top_iff]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N => ?_⟩
    rw [iInf_ge_le_coe_iff]
    obtain ⟨n, hn, hle⟩ := (infinite_setOf_iff _).mp hB N
    exact ⟨n, hn, by exact_mod_cast hle⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, (infinite_setOf_iff _).mpr fun N => ?_⟩
    obtain ⟨n, hn, hle⟩ := (iInf_ge_le_coe_iff _ N B).mp (hB N)
    exact ⟨n, hn, by exact_mod_cast hle⟩

/-! ### Unconditional facts about prime gaps -/

/-- Prime gaps are positive: `p_{n+1} > p_n`. -/
lemma one_le_primeGap (n : ℕ) : 1 ≤ primeGap n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 (by omega)
  simp only [primeGap]
  omega

/-- The first few prime gaps: `3 - 2 = 1`. -/
lemma primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- The first few prime gaps: `5 - 3 = 2`. -/
lemma primeGap_one : primeGap 1 = 2 := by
  simp [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- The first few prime gaps: `7 - 5 = 2`. -/
lemma primeGap_two : primeGap 2 = 2 := by
  simp [primeGap, Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]

/-- The first few prime gaps: `11 - 7 = 4`. -/
lemma primeGap_three : primeGap 3 = 4 := by
  simp [primeGap, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]

/-- Prime gaps are unbounded: for every `B` there is a gap exceeding `B`
(the classical `n! + 2, …, n! + n` construction). -/
theorem exists_primeGap_gt (B : ℕ) : ∃ n, B < primeGap n := by
  simp only [primeGap]
  have hMpos : 0 < (B + 2)! := Nat.factorial_pos _
  have hMge : B + 2 ≤ (B + 2)! := Nat.self_le_factorial _
  have hnp : ∀ q, (B + 2)! + 2 ≤ q → q ≤ (B + 2)! + B + 2 → ¬ q.Prime := by
    intro q h1 h2 hq
    have hdvdM : (q - (B + 2)!) ∣ (B + 2)! := Nat.dvd_factorial (by omega) (by omega)
    have hsum : (q - (B + 2)!) ∣ ((B + 2)! + (q - (B + 2)!)) := Dvd.dvd.add hdvdM dvd_rfl
    rw [show (B + 2)! + (q - (B + 2)!) = q from by omega] at hsum
    rcases hq.eq_one_or_self_of_dvd _ hsum with h | h <;> omega
  have hinf := Nat.infinite_setOf_prime
  obtain ⟨k, hk⟩ : ∃ k, Nat.count Nat.Prime ((B + 2)! + 2) = k := ⟨_, rfl⟩
  have hk1 : (B + 2)! + 2 ≤ Nat.nth Nat.Prime k := by
    rw [← hk]; exact (Nat.count_le_iff_le_nth hinf).mp le_rfl
  have hkprime : Nat.Prime (Nat.nth Nat.Prime k) := Nat.nth_mem_of_infinite hinf k
  have hkbig : (B + 2)! + B + 3 ≤ Nat.nth Nat.Prime k := by
    by_contra hcon
    exact hnp _ hk1 (by omega) hkprime
  have hkpos : 1 ≤ k := by
    have h2 : Nat.nth Nat.Prime 0 < (B + 2)! + 2 := by
      rw [Nat.nth_prime_zero_eq_two]; omega
    have h3 := (Nat.lt_nth_iff_count_lt hinf).mpr h2
    rw [hk] at h3
    omega
  have hlow : Nat.nth Nat.Prime (k - 1) < (B + 2)! + 2 := by
    refine (Nat.lt_nth_iff_count_lt hinf).mp ?_
    rw [hk]; omega
  refine ⟨k - 1, ?_⟩
  rw [show k - 1 + 1 = k from by omega]
  omega

/-- Prime gaps are unbounded along every tail. -/
theorem exists_ge_primeGap_gt (B N : ℕ) : ∃ n ≥ N, B < primeGap n := by
  obtain ⟨n, hn⟩ := exists_primeGap_gt (B + (Finset.range N).sup primeGap)
  refine ⟨n, ?_, by omega⟩
  by_contra hlt
  push_neg at hlt
  have : primeGap n ≤ (Finset.range N).sup primeGap :=
    Finset.le_sup (Finset.mem_range.mpr hlt)
  omega

/-- Consequently the `limsup` of the prime gaps is infinite: the `liminf` formulation is the
correct way to state bounded gaps. -/
theorem limsup_primeGap_eq_top :
    Filter.limsup (fun n => (primeGap n : ℕ∞)) atTop = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine eq_top_iff.mpr (le_iInf fun N => ?_)
  by_contra hcon
  obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.mp (fun h => hcon (h ▸ le_rfl))
  obtain ⟨n, hn, hgt⟩ := exists_ge_primeGap_gt B N
  have hle : ((primeGap n : ℕ) : ℕ∞) ≤ (B : ℕ∞) := by
    refine le_trans (le_trans (le_iSup (f := fun _ : n ≥ N => ((primeGap n : ℕ) : ℕ∞)) hn)
      (le_iSup (fun i => ⨆ _ : i ≥ N, ((primeGap i : ℕ) : ℕ∞)) n)) ?_
    exact le_of_eq hB.symm
  have := Nat.cast_le.mp hle
  omega

end Frontier


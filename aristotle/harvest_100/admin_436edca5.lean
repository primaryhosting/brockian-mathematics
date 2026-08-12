import Mathlib

/-!
# Bounded Prime Gaps
Category: Frontier — Prime Numbers
Target: Frontier.bounded_prime_gaps
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter

/-- The `n`-th prime gap `p_{n+1} - p_n`, where `p_n = Nat.nth Nat.Prime n`. -/
noncomputable def primeGap (n : ℕ) : ℕ := Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n

/-- The statement "the `liminf` of the prime gaps is finite", the conclusion of the
Zhang–Maynard theorem, expressed in `ℕ∞`. -/
def BoundedPrimeGaps : Prop :=
  Filter.liminf (fun n => (primeGap n : ℕ∞)) Filter.atTop < ⊤

/-- A finite set `H ⊆ ℕ` is *admissible* if for every prime `p` the reductions of the
elements of `H` modulo `p` do not cover all of `ZMod p`. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The Dickson–Hardy–Littlewood type hypothesis `DHL[k, 2]`: for every admissible set `H`
of size `k` there are infinitely many `n` such that at least two of the numbers `n + h`,
`h ∈ H`, are prime.  This is what the Goldston–Pintz–Yıldırım / Zhang / Maynard sieve
machinery provides for suitable `k`. -/
def DicksonHardyLittlewood (k : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → IsAdmissible H →
    {n : ℕ | 2 ≤ (H.filter fun h => Nat.Prime (n + h)).card}.Infinite

section Basic

lemma primeGap_zero : primeGap 0 = 1 := by
  simp [primeGap, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

lemma primeGap_one : primeGap 1 = 2 := by
  simp [primeGap, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

lemma nth_prime_lt_nth_prime {m n : ℕ} (h : m < n) :
    Nat.nth Nat.Prime m < Nat.nth Nat.Prime n :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 h

lemma nth_prime_le_nth_prime {m n : ℕ} (h : m ≤ n) :
    Nat.nth Nat.Prime m ≤ Nat.nth Nat.Prime n :=
  (Nat.nth_le_nth Nat.infinite_setOf_prime).2 h

lemma primeGap_pos (n : ℕ) : 0 < primeGap n := by
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    nth_prime_lt_nth_prime (Nat.lt_succ_self n)
  simp only [primeGap]
  omega

/-- If `q` is a prime exceeding the `j`-th prime, then the `(j+1)`-st prime is at most `q`. -/
lemma nth_prime_succ_le_of_prime {j q : ℕ} (hq : q.Prime) (h : Nat.nth Nat.Prime j < q) :
    Nat.nth Nat.Prime (j + 1) ≤ q := by
  classical
  have hjp : Nat.Prime (Nat.nth Nat.Prime j) := Nat.prime_nth_prime j
  have hcount : Nat.count Nat.Prime (Nat.nth Nat.Prime j) = j :=
    Nat.count_nth_of_infinite Nat.infinite_setOf_prime j
  have h1 : Nat.count Nat.Prime (Nat.nth Nat.Prime j + 1) = j + 1 := by
    rw [Nat.count_succ_eq_succ_count_iff.2 hjp, hcount]
  have h2 : j + 1 ≤ Nat.count Nat.Prime q := by
    rw [← h1]
    exact Nat.count_monotone _ h
  calc Nat.nth Nat.Prime (j + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
        nth_prime_le_nth_prime h2
    _ = q := Nat.nth_count hq

/-- Bertrand's postulate gives the (trivial, unconditional) bound `p_{n+1} - p_n ≤ p_n`. -/
lemma primeGap_le_nth (n : ℕ) : primeGap n ≤ Nat.nth Nat.Prime n := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime n)
    (Nat.prime_nth_prime n).ne_zero
  have h3 : Nat.nth Nat.Prime (n + 1) ≤ q := nth_prime_succ_le_of_prime hq h1
  simp only [primeGap]
  omega

end Basic

section Reduction

/-- Infinitely many pairs of primes at distance at most `B` yield infinitely many indices `n`
with `p_{n+1} - p_n ≤ B`. -/
lemma infinite_gap_le_of_prime_pairs (B : ℕ)
    (h : ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B) :
    {n : ℕ | primeGap n ≤ B}.Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, q, hNp, hp, hq, hpq, hqle⟩ := h (Nat.nth Nat.Prime (N + 1))
  set j := Nat.count Nat.Prime p
  have hnthp : Nat.nth Nat.Prime j = p := Nat.nth_count hp
  have hNj : N + 1 < j := by
    apply (Nat.nth_lt_nth Nat.infinite_setOf_prime).1
    rw [hnthp]
    exact hNp
  refine ⟨j, ?_, by omega⟩
  have hle : Nat.nth Nat.Prime (j + 1) ≤ q :=
    nth_prime_succ_le_of_prime hq (by rw [hnthp]; exact hpq)
  simp only [Set.mem_setOf_eq, primeGap, hnthp]
  omega

/-- Having infinitely many gaps bounded by `B` is the same as frequently having a gap at
most `B`. -/
lemma infinite_gap_le_iff_frequently (B : ℕ) :
    {n : ℕ | primeGap n ≤ B}.Infinite ↔ ∃ᶠ n in atTop, primeGap n ≤ B := by
  constructor
  · intro hinf
    rw [frequently_atTop]
    intro a
    obtain ⟨n, hn, hna⟩ := hinf.exists_gt a
    exact ⟨n, hna.le, hn⟩
  · intro hfreq
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨b, hb, hbp⟩ := frequently_atTop.1 hfreq (a + 1)
    exact ⟨b, hbp, by omega⟩

/-- Reformulation of finiteness of the `liminf` of the prime gaps. -/
theorem boundedPrimeGaps_iff :
    BoundedPrimeGaps ↔ ∃ B : ℕ, {n : ℕ | primeGap n ≤ B}.Infinite := by
  constructor
  · intro hlt
    obtain ⟨B, hB⟩ := ENat.ne_top_iff_exists.1 hlt.ne
    refine ⟨B, (infinite_gap_le_iff_frequently B).2 ?_⟩
    by_contra hcon
    rw [not_frequently] at hcon
    have hev : ∀ᶠ n in atTop, ((B : ℕ∞) + 1) ≤ (primeGap n : ℕ∞) := by
      filter_upwards [hcon] with n hn
      have : B + 1 ≤ primeGap n := by omega
      exact_mod_cast this
    have hge : ((B : ℕ∞) + 1) ≤ Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop :=
      le_liminf_of_le (by isBoundedDefault) hev
    rw [← hB] at hge
    have : ((B + 1 : ℕ) : ℕ∞) ≤ ((B : ℕ) : ℕ∞) := by push_cast; exact hge
    have := (Nat.cast_le (α := ℕ∞)).1 this
    omega
  · rintro ⟨B, hB⟩
    have hfreq := (infinite_gap_le_iff_frequently B).1 hB
    have hle : Filter.liminf (fun n => (primeGap n : ℕ∞)) atTop ≤ (B : ℕ∞) :=
      liminf_le_of_frequently_le (hfreq.mono fun n hn => by exact_mod_cast hn)
    exact lt_of_le_of_lt hle (ENat.coe_lt_top B)

/-- For every `k` there is an admissible set of size `k`: the `k` primes
`p_k, p_{k+1}, …, p_{2k-1}`, all of which exceed `k`. -/
lemma exists_admissible (k : ℕ) : ∃ H : Finset ℕ, H.card = k ∧ IsAdmissible H := by
  classical
  have hsm : StrictMono (fun i => Nat.nth Nat.Prime (k + i)) := by
    intro a b hab
    exact nth_prime_lt_nth_prime (by omega)
  set H : Finset ℕ := (Finset.range k).image (fun i => Nat.nth Nat.Prime (k + i)) with hHdef
  have hcardH : H.card = k := by
    rw [hHdef, Finset.card_image_of_injective _ hsm.injective, Finset.card_range]
  have hmem : ∀ x ∈ H, k < x ∧ Nat.Prime x := by
    intro x hx
    rw [hHdef, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨?_, Nat.prime_nth_prime _⟩
    have := Nat.add_two_le_nth_prime (k + i)
    omega
  refine ⟨H, hcardH, ?_⟩
  intro p hp
  by_cases hpk : p ≤ k
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨hxk, hxp⟩ := hmem x hx
    have hnd : ¬ p ∣ x := by
      intro hdvd
      have := (Nat.prime_dvd_prime_iff_eq hp hxp).1 hdvd
      omega
    simpa [ZMod.natCast_eq_zero_iff] using hnd
  · push_neg at hpk
    by_contra hcon
    push_neg at hcon
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ Finset.image (fun x : ℕ => (x : ZMod p)) H := by
      intro r _
      obtain ⟨x, hx, hxr⟩ := hcon r
      exact Finset.mem_image.2 ⟨x, hx, hxr⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card p] at hcard
    have hle : (Finset.image (fun x : ℕ => (x : ZMod p)) H).card ≤ k :=
      Finset.card_image_le.trans (le_of_eq hcardH)
    omega

/-- From `DHL[k,2]` one extracts infinitely many pairs of primes at bounded distance. -/
lemma exists_prime_pairs_of_DHL {k : ℕ} (h : DicksonHardyLittlewood k) :
    ∃ B : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ p + B := by
  classical
  obtain ⟨H, hcard, hadm⟩ := exists_admissible k
  refine ⟨H.sup id, fun N => ?_⟩
  obtain ⟨n, hn, hNn⟩ := (h H hcard hadm).exists_gt N
  simp only [Set.mem_setOf_eq] at hn
  have hn' : 1 < (H.filter fun h => Nat.Prime (n + h)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hn'
  rw [Finset.mem_filter] at ha hb
  obtain ⟨haH, hpa⟩ := ha
  obtain ⟨hbH, hpb⟩ := hb
  have hasup : a ≤ H.sup id := Finset.le_sup (f := id) haH
  have hbsup : b ≤ H.sup id := Finset.le_sup (f := id) hbH
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨n + a, n + b, by omega, hpa, hpb, by omega, by omega⟩
  · exact ⟨n + b, n + a, by omega, hpb, hpa, by omega, by omega⟩

end Reduction

/-- **Bounded prime gaps** (Zhang, Maynard), as a Lean-checked reduction: the
Dickson–Hardy–Littlewood hypothesis `DHL[k,2]` for some `k ≥ 2` implies that the `liminf`
of the prime gaps `p_{n+1} - p_n` is finite. -/
theorem bounded_prime_gaps {k : ℕ} (h : DicksonHardyLittlewood k) :
    BoundedPrimeGaps := by
  obtain ⟨B, hB⟩ := exists_prime_pairs_of_DHL h
  exact boundedPrimeGaps_iff.2 ⟨B, infinite_gap_le_of_prime_pairs B hB⟩

end Frontier

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


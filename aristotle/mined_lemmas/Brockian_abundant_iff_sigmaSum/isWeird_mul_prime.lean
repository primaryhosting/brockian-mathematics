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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Status of the target

`Brockian.WeirdNumbers.OddWeirdExists` states that some odd weird number exists
(weird = abundant but not pseudoperfect, in Mathlib's `Nat.Weird`). Whether an odd
weird number exists is an open problem, so it is stated here as a `Prop`-valued
definition and *not* asserted. What is proved unconditionally in this file is:

* `isWeird_mul_prime` : if `n` is weird and `p` is a prime exceeding the sum of the
  divisors of `n`, then `n * p` is weird;
* `oddWeirdExists_iff_infinite` : `OddWeirdExists` holds iff there are infinitely many
  odd weird numbers (a conditional reduction obtained from `isWeird_mul_prime`);
* `weird_seventy` : `70` is weird, so weird numbers do exist;
* `not_weird_of_odd_lt_946` : no odd number below `946` is weird, hence
  `oddWeird_ge_946` : any witness for `OddWeirdExists` is at least `946`.

Mathlib supplies the basic vocabulary (`Nat.Abundant`, `Nat.Pseudoperfect`, `Nat.Weird`
and `Nat.abundant_iff_sum_divisors` in `Mathlib/NumberTheory/FactorisationProperties.lean`,
all of which are used below), but no lemma there closes or nearly closes the target:
`exact?`/`apply?` find nothing, and Mathlib proves no existence results about weird
numbers at all, so everything below is developed from scratch.
-/

open Finset

namespace Brockian
namespace WeirdNumbers

/-- The sum of all (positive) divisors of `n`. -/

theorem isWeird_mul_prime {n p : ℕ} (hp : p.Prime) (hlt : sigmaSum n < p) (hw : n.Weird) :
    (n * p).Weird := by
  have hn : n ≠ 0 := weird_ne_zero hw
  have hnle : n ≤ sigmaSum n := self_le_sigmaSum hn
  have hpn : ¬ p ∣ n := by
    intro hdvd
    have hpn' : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    omega
  obtain ⟨habund, hpseudo⟩ := hw
  rw [abundant_iff_sigmaSum] at habund
  constructor
  · rw [abundant_iff_sigmaSum, sigmaSum_mul_prime hn hp hpn]
    have hp1 : 1 ≤ p := hp.one_lt.le
    nlinarith [habund, hp1]
  · rintro ⟨-, S, hS, hsum⟩
    have hSsub : S ⊆ (n * p).divisors := hS.trans Nat.properDivisors_subset_divisors
    classical
    set A : Finset ℕ := S.filter (fun d => ¬ p ∣ d) with hA
    set B : Finset ℕ := S.filter (fun d => p ∣ d) with hB
    have hAB : A ∪ B = S := by
      ext x
      simp only [hA, hB, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        by_cases h : p ∣ x
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [hA, hB, Finset.mem_filter] at ha hb
      exact ha.2 hb.2
    have hsumsplit : ∑ d ∈ A, d + ∑ d ∈ B, d = n * p := by
      rw [← Finset.sum_union hdisj, hAB, hsum]
    have hAdvd : A ⊆ n.divisors := by
      intro a ha
      simp only [hA, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [divisors_mul_prime hn hp] at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact h
      · exfalso
        simp only [Finset.mem_image] at h
        obtain ⟨e, -, rfl⟩ := h
        exact ha.2 (Dvd.intro e rfl)
    have hBsub : B ⊆ n.divisors.image (fun d => p * d) := by
      intro a ha
      simp only [hB, Finset.mem_filter] at ha
      have hmem := hSsub ha.1
      rw [divisors_mul_prime hn hp] at hmem
      rcases Finset.mem_union.mp hmem with h | h
      · exact absurd (dvd_trans ha.2 (Nat.mem_divisors.mp h).1) hpn
      · exact h
    obtain ⟨C, hC, hCimage⟩ := Finset.subset_image_iff.mp hBsub
    have hinj : Set.InjOn (fun d => p * d) (C : Set ℕ) := by
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    have hBsum : ∑ d ∈ B, d = p * ∑ d ∈ C, d := by
      rw [← hCimage, Finset.sum_image hinj, Finset.mul_sum]
    have hAle : ∑ d ∈ A, d ≤ sigmaSum n := by
      unfold sigmaSum
      exact Finset.sum_le_sum_of_subset hAdvd
    have hAdvdp : p ∣ ∑ d ∈ A, d := by
      have hcomm : n * p = p * n := mul_comm n p
      refine ⟨n - ∑ d ∈ C, d, ?_⟩
      rw [Nat.mul_sub]
      omega
    have hA0 : ∑ d ∈ A, d = 0 := by
      rcases Nat.eq_zero_or_pos (∑ d ∈ A, d) with h | h
      · exact h
      · have := Nat.le_of_dvd h hAdvdp
        omega
    have hCsum : ∑ d ∈ C, d = n := by
      have hmul : p * ∑ d ∈ C, d = p * n := by
        rw [mul_comm p n]; omega
      exact Nat.eq_of_mul_eq_mul_left hp.pos hmul
    have hCproper : C ⊆ n.properDivisors := by
      intro c hc
      have hcn : c ∣ n := (Nat.mem_divisors.mp (hC hc)).1
      rw [Nat.mem_properDivisors]
      refine ⟨hcn, ?_⟩
      rcases lt_or_ge c n with h | h
      · exact h
      · exfalso
        have hcn' : c = n := le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hcn) h
        subst hcn'
        have hmem : p * c ∈ B := by
          rw [← hCimage]
          exact Finset.mem_image_of_mem _ hc
        have hmemS : p * c ∈ S := (Finset.mem_filter.mp hmem).1
        have hprop := hS hmemS
        rw [Nat.mem_properDivisors] at hprop
        have hcomm : p * c = c * p := mul_comm p c
        omega
    exact hpseudo ⟨Nat.pos_of_ne_zero hn, C, hCproper, hCsum⟩

/-! ### Consequence: one odd weird number yields arbitrarily large ones -/

/-- If an odd weird number exists, then there are arbitrarily large odd weird numbers. -/

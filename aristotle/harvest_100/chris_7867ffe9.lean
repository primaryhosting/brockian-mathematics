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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is a *Zumkeller number* if the set of its divisors can be
split into two parts having the same sum. -/
def Zumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ A ⊆ n.divisors, ∑ d ∈ A, d = ∑ d ∈ n.divisors \ A, d

/-- Equivalent "signed" description of the Zumkeller condition: there is a `±1`-valued function
`f` with `∑_{d ∣ n} f d * d = 0`. -/
def SignedZumkeller (n : ℕ) : Prop :=
  ∃ f : ℕ → ℤ, (∀ d, f d = 1 ∨ f d = -1) ∧ ∑ d ∈ n.divisors, f d * (d : ℤ) = 0

/-- The subset formulation and the `±1`-signed formulation of the Zumkeller property agree. -/
theorem zumkeller_iff_signedZumkeller {n : ℕ} :
    Zumkeller n ↔ 0 < n ∧ SignedZumkeller n := by
  constructor
  · rintro ⟨hn, A, hA, hsum⟩
    refine ⟨hn, fun d => if d ∈ A then 1 else -1, fun d => by by_cases h : d ∈ A <;> simp [h], ?_⟩
    rw [← Finset.sum_sdiff hA]
    have h1 : ∑ d ∈ n.divisors \ A, (if d ∈ A then (1 : ℤ) else -1) * (d : ℤ)
        = -∑ d ∈ n.divisors \ A, (d : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [Finset.mem_sdiff] at hd
      simp [hd.2]
    have h2 : ∑ d ∈ A, (if d ∈ A then (1 : ℤ) else -1) * (d : ℤ) = ∑ d ∈ A, (d : ℤ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      simp [hd]
    rw [h1, h2]
    have hcast : ((∑ d ∈ A, d : ℕ) : ℤ) = ((∑ d ∈ n.divisors \ A, d : ℕ) : ℤ) := by
      exact_mod_cast hsum
    push_cast at hcast
    omega
  · rintro ⟨hn, f, hf, hsum⟩
    refine ⟨hn, n.divisors.filter (fun d => f d = 1), Finset.filter_subset _ _, ?_⟩
    have hsplit : n.divisors \ n.divisors.filter (fun d => f d = 1)
        = n.divisors.filter (fun d => ¬ f d = 1) := by
      ext d
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      tauto
    have key : ((∑ d ∈ n.divisors.filter (fun d => f d = 1), d : ℕ) : ℤ)
        = ((∑ d ∈ n.divisors \ n.divisors.filter (fun d => f d = 1), d : ℕ) : ℤ) := by
      rw [hsplit]
      push_cast
      rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => f d = 1)
        (fun d => f d * (d : ℤ))] at hsum
      have e1 : ∑ d ∈ n.divisors.filter (fun d => f d = 1), f d * (d : ℤ)
          = ∑ d ∈ n.divisors.filter (fun d => f d = 1), (d : ℤ) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter] at hd
        rw [hd.2, one_mul]
      have e2 : ∑ d ∈ n.divisors.filter (fun d => ¬ f d = 1), f d * (d : ℤ)
          = -∑ d ∈ n.divisors.filter (fun d => ¬ f d = 1), (d : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter] at hd
        rcases hf d with h | h
        · exact absurd h hd.2
        · rw [h]; ring
      rw [e1, e2] at hsum
      omega
    exact_mod_cast key

/-- Summing an integer-valued function over the divisors of a coprime product `m * n` is the
same as summing over all pairs consisting of a divisor of `m` and a divisor of `n`. -/
theorem sum_divisors_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (g : ℕ → ℤ) :
    ∑ k ∈ (m * n).divisors, g k = ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, g (d * e) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun p : ℕ × ℕ => p.1 * p.2) (j := fun k => (k.gcd m, k.gcd n))
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product, Nat.mem_divisors] at hde
    simp only [Nat.mem_divisors]
    exact ⟨Nat.mul_dvd_mul hde.1.1 hde.2.1, by positivity⟩
  · intro k _
    simp only [Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right k m, hm⟩, ⟨Nat.gcd_dvd_right k n, hn⟩⟩
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product, Nat.mem_divisors] at hde
    have h1 : (d * e).gcd m = d := by
      rw [Nat.Coprime.gcd_mul_right_cancel d (Nat.Coprime.coprime_dvd_left hde.2.1 h.symm)]
      exact Nat.gcd_eq_left hde.1.1
    have h2 : (d * e).gcd n = e := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel e (Nat.Coprime.coprime_dvd_left hde.1.1 h)]
      exact Nat.gcd_eq_left hde.2.1
    simp [h1, h2]
  · intro k hk
    simp only [Nat.mem_divisors] at hk
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hk.1
  · rintro ⟨d, e⟩ _
    rfl

/-- Zumkeller numbers are stable under multiplication by a coprime factor. -/
theorem Zumkeller.mul_coprime {n m : ℕ} (hn : Zumkeller n) (hm : 0 < m)
    (h : Nat.Coprime n m) : Zumkeller (n * m) := by
  obtain ⟨hnpos, f, hf, hsum⟩ := zumkeller_iff_signedZumkeller.1 hn
  refine zumkeller_iff_signedZumkeller.2 ⟨by positivity, fun k => f (k.gcd n), fun d => hf _, ?_⟩
  rw [sum_divisors_mul_of_coprime h hnpos.ne' hm.ne' (fun k => f (k.gcd n) * (k : ℤ))]
  have key : ∀ d ∈ n.divisors, ∀ e ∈ m.divisors,
      f ((d * e).gcd n) * ((d * e : ℕ) : ℤ) = (f d * (d : ℤ)) * (e : ℤ) := by
    intro d hd e he
    simp only [Nat.mem_divisors] at hd he
    have h1 : (d * e).gcd n = d := by
      rw [Nat.Coprime.gcd_mul_right_cancel d (Nat.Coprime.coprime_dvd_left he.1 h.symm)]
      exact Nat.gcd_eq_left hd.1
    rw [h1]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => key d hd e he)),
    ← Finset.sum_mul_sum, hsum, zero_mul]

/-- `945 = 3 ^ 3 * 5 * 7` is a Zumkeller number: its divisors sum to `1920`, and the two
divisors `15` and `945` already add up to the half sum `960`. -/
theorem zumkeller_945 : Zumkeller 945 :=
  ⟨by norm_num, {15, 945}, by decide, by decide⟩

/-- **Odd Zumkeller numbers from the `3`-structure `945 = 3 ^ 3 · 5 · 7`.**
For every odd `m` coprime to `945`, the number `945 * m` is an odd Zumkeller number,
and it is divisible by `27`. -/
theorem OddZumkellerFrom3Structure {m : ℕ} (hm : Odd m) (hcop : Nat.Coprime 945 m) :
    Odd (945 * m) ∧ 27 ∣ 945 * m ∧ Zumkeller (945 * m) := by
  refine ⟨Odd.mul (by decide) hm, Dvd.dvd.mul_right (by norm_num) m, ?_⟩
  exact zumkeller_945.mul_coprime hm.pos hcop

/-- There are infinitely many odd Zumkeller numbers, for instance `945 * 11 ^ k`. -/
theorem infinite_odd_zumkeller : {n : ℕ | Odd n ∧ Zumkeller n}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 945 * 11 ^ k) ?_ ?_
  · intro a b hab
    have h11 : (11 : ℕ) ^ a = 11 ^ b := by
      have := hab
      simp only at this
      omega
    exact Nat.pow_right_injective (by norm_num) h11
  · intro k
    have hodd : Odd ((11 : ℕ) ^ k) := Odd.pow (by decide)
    have hcop : Nat.Coprime 945 (11 ^ k) := Nat.Coprime.pow_right k (by decide)
    obtain ⟨h1, _, h3⟩ := OddZumkellerFrom3Structure hodd hcop
    exact ⟨h1, h3⟩

end ZumkellerNumbers
end Brockian


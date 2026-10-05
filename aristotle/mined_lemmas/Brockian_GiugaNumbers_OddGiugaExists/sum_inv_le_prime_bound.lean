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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to precede every other command, so the header above is a plain
-- comment; it is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Summary

A *Giuga number* is a composite `n` with `p ∣ n / p - 1` for every prime `p ∣ n`
(`IsGiuga`).  The smallest one is `30`.  Whether an **odd** Giuga number exists is an open
problem, so the target `OddGiugaExists` is stated and proved here as a Lean-checked
equivalent reformulation (a reduction), not as an unconditional existence claim:

* `OddGiugaExists` : an odd Giuga number exists **iff** there is a finite set `S` of at least
  two odd primes with `p ∣ (∏ q ∈ S \ {p}, q) - 1` for every `p ∈ S`.

Supporting results and unconditional partial results proved here:

* `IsGiuga.squarefree` : Giuga numbers are squarefree;
* `isGiugaSet_primeFactors` / `isGiuga_prod` : the two directions of the reduction;
* `isGiuga_30` : `30` is a Giuga number;
* `IsGiuga.dvd_sum_div_sub_one` : Giuga's congruence `n ∣ (∑ p ∈ n.primeFactors, n / p) - 1`;
* `IsGiuga.one_lt_sum_inv` : the reciprocals of the prime factors sum to more than `1`;
* `odd_giuga_nine_le_card` : an odd Giuga number has at least nine distinct prime factors.
-/

open scoped BigOperators

namespace Brockian.GiugaNumbers

/-- `n` is a *Giuga number* if it is composite (`1 < n` and not prime) and for every prime
divisor `p` of `n` we have `p ∣ n / p - 1`. -/

theorem sum_inv_le_prime_bound :
    ∀ (k : ℕ), k ≤ 8 → ∀ S : Finset ℕ, S.card = k → (∀ x ∈ S, x.Prime) → (∀ x ∈ S, Odd x) →
      ∑ x ∈ S, (1 : ℚ) / x ≤ ∑ i ∈ Finset.range k, (1 : ℚ) / (oddPrimeLB i) := by
  intro k
  induction k with
  | zero =>
    intro _ S hS _ _
    rw [Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro hk8 S hS hprime hodd
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hM : S.max' hne ∈ S := S.max'_mem hne
    set M := S.max' hne with hMdef
    have hMprime := hprime M hM
    have hModd : M % 2 = 1 := by have := hodd M hM; rwa [Nat.odd_iff] at this
    have hM3 : 3 ≤ M := by have := hMprime.two_le; omega
    have hPS : ∀ x ∈ S, 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0) := by
      intro x hx
      have h2 := (hprime x hx).two_le
      have hox : x % 2 = 1 := by have := hodd x hx; rwa [Nat.odd_iff] at this
      refine ⟨by omega, hox, ?_⟩
      by_cases h : x % 3 = 0
      · left
        have hdvd : (3 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero h
        exact (((hprime x hx).eq_one_or_self_of_dvd 3 hdvd).resolve_left (by norm_num)).symm
      · right; exact h
    -- counting the admissible values below a bound
    have hcards : ∀ j < 8, ((Finset.range (oddPrimeLB j)).filter
        (fun x => 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0))).card = j := by decide
    have hbound : oddPrimeLB k ≤ M := by
      by_contra hlt
      push_neg at hlt
      have hsub : S ⊆ (Finset.range (oddPrimeLB k)).filter
          (fun x => 3 ≤ x ∧ x % 2 = 1 ∧ (x = 3 ∨ x % 3 ≠ 0)) := by
        intro x hx
        have hxM : x ≤ M := S.le_max' x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hPS x hx⟩
      have hcle := Finset.card_le_card hsub
      have hk : k < 8 := by omega
      rw [hcards k hk] at hcle
      omega
    have hcard' : (S.erase M).card = k := by
      rw [Finset.card_erase_of_mem hM, hS]
      omega
    have h1 := ih (by omega) (S.erase M) hcard'
      (fun x hx => hprime x (Finset.mem_of_mem_erase hx))
      (fun x hx => hodd x (Finset.mem_of_mem_erase hx))
    have hsum : ∑ x ∈ S, (1 : ℚ) / x
        = 1 / (M : ℚ) + ∑ x ∈ S.erase M, (1 : ℚ) / x :=
      (Finset.add_sum_erase _ (fun x : ℕ => (1 : ℚ) / (x : ℚ)) hM).symm
    have hLBpos : (0 : ℚ) < (oddPrimeLB k : ℚ) := by
      have h3 : (3 : ℚ) ≤ (oddPrimeLB k : ℚ) := by exact_mod_cast three_le_oddPrimeLB k
      linarith
    have hMcast : ((oddPrimeLB k : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hbound
    have hterm : (1 : ℚ) / M ≤ 1 / (oddPrimeLB k : ℚ) :=
      one_div_le_one_div_of_le hLBpos hMcast
    rw [Finset.sum_range_succ, hsum]
    linarith

/-- The reciprocals of the eight smallest odd primes sum to less than `1`. -/

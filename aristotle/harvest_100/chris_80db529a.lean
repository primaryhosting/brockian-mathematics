/-
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-- `noDiv n k` is `true` when no `d` with `2 ≤ d ≤ k` divides `n`. -/
def noDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | (d + 2) => (n % (d + 2) != 0) && noDiv n (d + 1)

/-- A trial–division primality test, sound for `n ≤ 2703` (`51 = ⌊√2703⌋`). -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && noDiv n (min 51 (n - 1))

/-- The primes used as the small side of a Goldbach split (all primes `≤ 103`). -/
def wheelPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103]

/-- `goldbachSplit m` searches the small primes for a `p` with `p < m` and `m - p` prime. -/
def goldbachSplit (m : ℕ) : Bool :=
  wheelPrimes.any (fun p => isPrimeB p && decide (p < m) && isPrimeB (m - p))

theorem noDiv_spec (n : ℕ) :
    ∀ k : ℕ, noDiv n k = true → ∀ d : ℕ, 2 ≤ d → d ≤ k → ¬ d ∣ n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro _ d hd hdk; omega
    | 1 => intro _ d hd hdk; omega
    | (j + 2) =>
      intro h d hd hdk
      simp only [noDiv, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge d (j + 2) with hlt | hge
      · exact ih (j + 1) (by omega) h.2 d hd (by omega)
      · have hdj : d = j + 2 := by omega
        subst hdj
        rw [Nat.dvd_iff_mod_eq_zero]
        exact h.1

/-- Soundness of the trial–division test in the range we use it in. -/
theorem isPrimeB_sound {n : ℕ} (hn : n ≤ 2703) (h : isPrimeB n = true) : Nat.Prime n := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms => ?_⟩
  have hs51 : n.sqrt ≤ 51 := by
    have : n.sqrt < 52 := Nat.sqrt_lt'.mpr (by omega)
    omega
  have hsn : n.sqrt < n := Nat.sqrt_lt_self (by omega)
  exact noDiv_spec n (min 51 (n - 1)) hnd m hm (by omega)

/-- If the Boolean search succeeds, `m` really is a sum of two primes. -/
theorem goldbachSplit_sound {m : ℕ} (hm : m ≤ 2703) (h : goldbachSplit m = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  rw [goldbachSplit, List.any_eq_true] at h
  obtain ⟨p, _, hp⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨hpp, hplt⟩, hqp⟩ := hp
  refine ⟨p, m - p, isPrimeB_sound (by omega) hpp, isPrimeB_sound (by omega) hqp, by omega⟩

/-- The exhaustive wheel check: every even number `2n` with `2 ≤ n ≤ 1327` splits. -/
theorem wheel_check : (List.range' 2 1326).all (fun n => goldbachSplit (2 * n)) = true := by
  decide +kernel

/-- **Goldbach wheel, K = 2, modulus 1327.**
Every even number `n` with `4 ≤ n ≤ 2 * 1327 = 2654` is a sum of two primes.
The verification is a kernel-checked trial-division search that, for each even `n` in range,
exhibits a prime `p ≤ 103` with `n - p` prime. -/
theorem GoldbachWheelK2_1327 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 2654) (heven : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨k, hk⟩ := heven
  have hmem : k ∈ List.range' 2 1326 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
  have := (List.all_eq_true.mp wheel_check) k hmem
  have h2k : 2 * k = n := by omega
  rw [h2k] at this
  exact goldbachSplit_sound (by omega) this

end Brockian

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


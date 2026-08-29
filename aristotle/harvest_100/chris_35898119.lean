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

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace GoldbachSchema

/-- Goldbach's property at `n`: `n` is a sum of two primes. -/
def Goldbach (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- The "model" hypothesis at threshold `B`: every even number **beyond** `B`
is a sum of two primes.  This is the genuinely open part of Goldbach's conjecture. -/
def GoldbachModel (B : ℕ) : Prop := ∀ n : ℕ, B < n → Even n → Goldbach n

/-- All primes below `1000`. -/
def smallPrimes : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,
   127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,
   251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,
   389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,
   541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,
   677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,
   839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997]

/-- Every entry of `smallPrimes` really is prime. -/
theorem smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

/-- The finite verification: every even number `2 * k + 4` with `k < 499`
(i.e. every even number between `4` and `1000`) splits as a sum of two entries
of `smallPrimes`. -/
theorem smallPrimes_split :
    ∀ k < 499, ∃ p ∈ smallPrimes, p ≤ 2 * k + 4 ∧ (2 * k + 4 - p) ∈ smallPrimes := by
  decide

/-- **Discharged sub-lemma.**  Goldbach's conjecture holds unconditionally for every even
number `n` with `4 ≤ n ≤ 1000`. -/
theorem goldbach_of_le_1000 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1000) (he : Even n) : Goldbach n := by
  obtain ⟨m, hm⟩ := he
  have hk : (n - 4) / 2 < 499 := by omega
  obtain ⟨p, hp, hple, hq⟩ := smallPrimes_split ((n - 4) / 2) hk
  have hn' : 2 * ((n - 4) / 2) + 4 = n := by omega
  rw [hn'] at hple hq
  exact ⟨p, n - p, smallPrimes_prime p hp, smallPrimes_prime _ hq, by omega⟩

/-- **Main target.**  If the (open) model hypothesis holds beyond some threshold `B ≤ 1000`,
then Goldbach's conjecture holds for *every* even `n ≥ 4`.

The finite hypothesis of the original schema — that Goldbach's conjecture has been checked on
the range `4 ≤ n ≤ 1000` — is discharged here (see `goldbach_of_le_1000`), so no verification
assumption remains; the only remaining hypothesis is the genuinely open statement
`GoldbachModel B` about the numbers beyond the checked range. -/
theorem goldbach_beyond_of_model {B : ℕ} (hB : B ≤ 1000) (model : GoldbachModel B) :
    ∀ n : ℕ, 4 ≤ n → Even n → Goldbach n := by
  intro n h4 he
  by_cases h : B < n
  · exact model n h he
  · exact goldbach_of_le_1000 n h4 (by omega) he

/-- Consequence: Goldbach's conjecture is *equivalent* to its restriction beyond `1000`. -/
theorem goldbach_iff_goldbachModel_1000 :
    GoldbachModel 1000 ↔ ∀ n : ℕ, 4 ≤ n → Even n → Goldbach n := by
  constructor
  · intro h
    exact goldbach_beyond_of_model (B := 1000) le_rfl h
  · intro h n hn he
    exact h n (by omega) he

end GoldbachSchema
end Brockian


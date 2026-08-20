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

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian.GoldbachSchema

/-- The bound up to which the binary Goldbach property is verified here by kernel
computation (`decide`). -/
def verifiedBound : ℕ := 200

/-- Kernel-checked finite verification: every even `n` with `4 ≤ n ≤ verifiedBound`
admits a prime `p ≤ n` such that `n - p` is prime as well. -/
private lemma goldbach_check :
    ∀ n ∈ Finset.range (verifiedBound + 1), 4 ≤ n → Even n →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- Every even number `n` with `4 ≤ n ≤ verifiedBound` is a sum of two primes. -/
theorem goldbach_le_verifiedBound (n : ℕ) (hn : n ≤ verifiedBound) (h4 : 4 ≤ n)
    (hev : Even n) : ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, hp_mem, hp, hq⟩ :=
    goldbach_check n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) h4 hev
  refine ⟨p, n - p, hp, hq, ?_⟩
  have hple : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_mem)
  omega

/-- A *Goldbach model*: a witness function producing, for every even number beyond
`verifiedBound`, a prime `witness n ≤ n` whose complement `n - witness n` is prime too. -/
structure GoldbachModel where
  /-- The witness function, choosing one of the two prime summands. -/
  witness : ℕ → ℕ
  /-- The witness never exceeds its argument. -/
  witness_le : ∀ n, Even n → verifiedBound < n → witness n ≤ n
  /-- The witness is prime. -/
  witness_prime : ∀ n, Even n → verifiedBound < n → Nat.Prime (witness n)
  /-- The complement of the witness is prime. -/
  cowitness_prime : ∀ n, Even n → verifiedBound < n → Nat.Prime (n - witness n)

/-- **Goldbach from a model.** Given a Goldbach model, which supplies prime
decompositions for the even numbers *beyond* `verifiedBound`, every even number
`n ≥ 4` is a sum of two primes.

The small cases, previously carried as a separate hypothesis, are discharged
unconditionally by the kernel computation in `goldbach_le_verifiedBound`. -/
theorem goldbach_beyond_of_model (M : GoldbachModel) (n : ℕ) (h4 : 4 ≤ n) (hev : Even n) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rcases le_or_gt n verifiedBound with h | h
  · exact goldbach_le_verifiedBound n h h4 hev
  · refine ⟨M.witness n, n - M.witness n, M.witness_prime n hev h,
      M.cowitness_prime n hev h, ?_⟩
    have := M.witness_le n hev h
    omega

end Brockian.GoldbachSchema


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
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxRecDepth 10000

namespace Brockian.GoldbachSchema

/-- `IsGoldbach n` says that `n` is a sum of two primes. -/
def IsGoldbach (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- A *Goldbach model beyond `B`*: every even number that is at least `B` is a sum of two
primes.  This is the "model" input of the schema: it captures the asymptotic half of
Goldbach's conjecture, leaving the initial segment to be verified. -/
def ModelBeyond (B : ℕ) : Prop := ∀ n : ℕ, B ≤ n → Even n → IsGoldbach n

/-- Goldbach's conjecture: every even number `n ≥ 4` is a sum of two primes. -/
def Goldbach : Prop := ∀ n : ℕ, 4 ≤ n → Even n → IsGoldbach n

/-- The finite base check: every even `n` with `4 ≤ n < 200` is a sum of two primes.
This is the hypothesis that is discharged (by kernel computation) in
`goldbach_beyond_of_model`. -/
theorem isGoldbach_of_lt_two_hundred (n : ℕ) (hn : n < 200) (h4 : 4 ≤ n) (hev : Even n) :
    IsGoldbach n := by
  have key : ∀ m ∈ Finset.range 200, 4 ≤ m → Even m →
      ∃ p ∈ Finset.range (m + 1), Nat.Prime p ∧ Nat.Prime (m - p) := by decide
  obtain ⟨p, hp, hp1, hp2⟩ := key n (Finset.mem_range.mpr hn) h4 hev
  have hple : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  exact ⟨p, n - p, hp1, hp2, Nat.add_sub_cancel' hple⟩

/-- **Goldbach beyond a model.**  If some `B ≤ 200` admits a Goldbach model beyond `B`
(i.e. every even `n ≥ B` is a sum of two primes), then Goldbach's conjecture holds in full:
every even `n ≥ 4` is a sum of two primes.

The initial-segment hypothesis of the schema has been discharged, so the only remaining
hypothesis is the model itself. -/
theorem goldbach_beyond_of_model (B : ℕ) (hB : B ≤ 200) (hmodel : ModelBeyond B) : Goldbach := by
  intro n h4 hev
  rcases le_or_gt B n with h | h
  · exact hmodel n h hev
  · exact isGoldbach_of_lt_two_hundred n (lt_of_lt_of_le h hB) h4 hev

end Brockian.GoldbachSchema


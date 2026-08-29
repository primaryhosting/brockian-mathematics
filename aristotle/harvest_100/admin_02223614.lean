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

## Contents

* `GoldbachModel S`: a model of the binary Goldbach schema over a set `S` of naturals.
* `goldbach_beyond_of_model`: the target theorem — from a model covering `n - 3` one gets the
  ternary Goldbach statement at any odd `n ≥ 9`.  It is proved outright (no hypothesis is
  assumed as an axiom) and it is non-vacuous: `goldbachModel_Iic_300` exhibits an explicit,
  computationally verified model.
* `goldbach_le_300` / `goldbachModel_Iic_300`: unconditional discharge of the model hypothesis
  on the range `[4, 300]`, by kernel computation.
* `ternary_le_303`: the resulting unconditional ternary Goldbach statement for odd `9 ≤ n ≤ 303`.

A model over `Set.univ` (`goldbachModel_univ_iff`) is precisely Goldbach's conjecture, which is
open; so the model hypothesis is discharged here exactly on the finite ranges that can be
verified, and left as a hypothesis in general.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian.GoldbachSchema

/-- `IsGoldbachSum n` says that `n` is a sum of two primes. -/
def IsGoldbachSum (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- `IsTernaryGoldbachSum n` says that `n` is a sum of three primes. -/
def IsTernaryGoldbachSum (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- A *model* of the binary Goldbach schema over a set `S` of natural numbers: every even
number `n ∈ S` with `4 ≤ n` is a sum of two primes.  Taking `S = Set.univ` gives exactly
Goldbach's conjecture; taking `S` finite gives statements checkable by computation. -/
structure GoldbachModel (S : Set ℕ) : Prop where
  sum_two_primes : ∀ n ∈ S, 4 ≤ n → Even n → IsGoldbachSum n

/-- A model over `Set.univ` is exactly Goldbach's conjecture. -/
theorem goldbachModel_univ_iff :
    GoldbachModel Set.univ ↔ ∀ n : ℕ, 4 ≤ n → Even n → IsGoldbachSum n := by
  constructor
  · intro M n hn he
    exact M.sum_two_primes n (Set.mem_univ n) hn he
  · intro h
    exact ⟨fun n _ hn he => h n hn he⟩

/-- Models restrict along inclusions of the index set. -/
theorem GoldbachModel.mono {S T : Set ℕ} (h : S ⊆ T) (M : GoldbachModel T) :
    GoldbachModel S :=
  ⟨fun n hn h4 he => M.sum_two_primes n (h hn) h4 he⟩

/-- **Goldbach beyond, from a model.**  From a model of the binary Goldbach schema covering
`n - 3`, one obtains the *ternary* Goldbach statement at the odd number `n ≥ 9`: `n` is a sum
of three primes. -/
theorem goldbach_beyond_of_model {S : Set ℕ} (M : GoldbachModel S) {n : ℕ}
    (hodd : Odd n) (h9 : 9 ≤ n) (hmem : n - 3 ∈ S) : IsTernaryGoldbachSum n := by
  obtain ⟨k, hk⟩ := hodd
  have h4 : 4 ≤ n - 3 := by omega
  have heven : Even (n - 3) := ⟨k - 1, by omega⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := M.sum_two_primes (n - 3) hmem h4 heven
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- Full binary Goldbach implies full ternary Goldbach for odd numbers `≥ 9`. -/
theorem ternary_of_goldbach (h : ∀ n : ℕ, 4 ≤ n → Even n → IsGoldbachSum n) {n : ℕ}
    (hodd : Odd n) (h9 : 9 ≤ n) : IsTernaryGoldbachSum n :=
  goldbach_beyond_of_model (goldbachModel_univ_iff.2 h) hodd h9 (Set.mem_univ _)

/-- The binary Goldbach schema, verified by computation for all even numbers up to `300`. -/
theorem goldbach_le_300 : ∀ n ≤ 300, 4 ≤ n → Even n → IsGoldbachSum n := by
  have H : ∀ n ≤ 300, 4 ≤ n → Even n →
      ∃ p ≤ n, ∃ q ≤ n, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by decide
  intro n hn h4 he
  obtain ⟨p, -, q, -, hp, hq, hpq⟩ := H n hn h4 he
  exact ⟨p, q, hp, hq, hpq⟩

/-- An explicit (unconditional) model of the binary Goldbach schema on `Set.Iic 300`. -/
theorem goldbachModel_Iic_300 : GoldbachModel (Set.Iic 300) :=
  ⟨fun n hn h4 he => goldbach_le_300 n hn h4 he⟩

/-- Unconditional ternary Goldbach in the verified range: every odd `n` with `9 ≤ n ≤ 303`
is a sum of three primes. -/
theorem ternary_le_303 {n : ℕ} (hodd : Odd n) (h9 : 9 ≤ n) (hn : n ≤ 303) :
    IsTernaryGoldbachSum n :=
  goldbach_beyond_of_model goldbachModel_Iic_300 hodd h9 (by simp only [Set.mem_Iic]; omega)

end Brockian.GoldbachSchema


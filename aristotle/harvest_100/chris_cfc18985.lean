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
namespace Brockian
namespace GoldbachSchema

/-- The binary Goldbach property: `n` is a sum of two primes. -/
def Goldbach2 (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The ternary Goldbach property: `n` is a sum of three primes. -/
def Goldbach3 (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

example : Goldbach2 10 := ⟨3, 7, by norm_num, by norm_num, by norm_num⟩

example : Goldbach3 9 := ⟨3, 3, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- A *model* of binary Goldbach beyond a bound: a witness function assigning to every even
`n ≥ bound` a prime `witness n ≤ n` whose complement `n - witness n` is again prime. -/
structure Model where
  /-- The bound beyond which the model certifies the binary Goldbach property. -/
  bound : ℕ
  /-- The witness function: the smaller summand attached to an even number. -/
  witness : ℕ → ℕ
  /-- The witness never exceeds the number it decomposes. -/
  witness_le : ∀ n : ℕ, bound ≤ n → Even n → witness n ≤ n
  /-- The witness is prime. -/
  witness_prime : ∀ n : ℕ, bound ≤ n → Even n → Nat.Prime (witness n)
  /-- The complement of the witness is prime. -/
  cowitness_prime : ∀ n : ℕ, bound ≤ n → Even n → Nat.Prime (n - witness n)

/-- Every model certifies the binary Goldbach property beyond its bound. -/
theorem binary_of_model (M : Model) {n : ℕ} (hn : M.bound ≤ n) (hev : Even n) :
    Goldbach2 n := by
  refine ⟨M.witness n, n - M.witness n, M.witness_prime n hn hev,
    M.cowitness_prime n hn hev, ?_⟩
  have := M.witness_le n hn hev
  omega

/-- Conversely, binary Goldbach beyond a bound `B` yields a model with that bound: the notion of
`Model` is exactly a packaging of the binary Goldbach property beyond a bound. -/
noncomputable def Model.ofGoldbachBeyond (B : ℕ)
    (h : ∀ n : ℕ, B ≤ n → Even n → Goldbach2 n) : Model where
  bound := B
  witness := fun n => if hb : B ≤ n then (if he : Even n then (h n hb he).choose else 0) else 0
  witness_le := by
    intro n hb he
    obtain ⟨q, _, _, hsum⟩ := (h n hb he).choose_spec
    simp only [dif_pos hb, dif_pos he]
    omega
  witness_prime := by
    intro n hb he
    obtain ⟨q, hp, _, _⟩ := (h n hb he).choose_spec
    simpa only [dif_pos hb, dif_pos he] using hp
  cowitness_prime := by
    intro n hb he
    obtain ⟨q, _, hq, hsum⟩ := (h n hb he).choose_spec
    simp only [dif_pos hb, dif_pos he]
    have : n - (h n hb he).choose = q := by omega
    rw [this]
    exact hq

/-- The named hypothesis of the schema: the *ternary descent* principle, stating that every odd
number `n ≥ 3` whose predecessor-by-three satisfies binary Goldbach is a sum of three primes. -/
def TernaryDescent : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n → Goldbach2 (n - 3) → Goldbach3 n

/-- Discharge of the named hypothesis `TernaryDescent`: it holds unconditionally. -/
theorem ternaryDescent : TernaryDescent := by
  rintro n hodd h3 ⟨p, q, hp, hq, hpq⟩
  exact ⟨3, p, q, Nat.prime_three, hp, hq, by omega⟩

/-- **Goldbach beyond, of a model** (unconditional in the named hypothesis).

Given any model `M` of binary Goldbach beyond `M.bound`, every number `n ≥ M.bound + 3` satisfies
the Goldbach property appropriate to its parity: an even such `n` is a sum of two primes, and an
odd such `n` is a sum of three primes.

The auxiliary hypothesis `TernaryDescent`, relative to which the schema is stated, has been
discharged (see `ternaryDescent`), so the result depends only on the model. -/
theorem goldbach_beyond_of_model (M : Model) (n : ℕ) (hn : M.bound + 3 ≤ n) :
    (Even n → Goldbach2 n) ∧ (Odd n → Goldbach3 n) := by
  constructor
  · intro hev
    exact binary_of_model M (by omega) hev
  · intro hodd
    have hn3 : Even (n - 3) := by
      rw [Nat.even_iff]
      rw [Nat.odd_iff] at hodd
      omega
    exact ternaryDescent n hodd (by omega) (binary_of_model M (by omega) hn3)

end GoldbachSchema
end Brockian


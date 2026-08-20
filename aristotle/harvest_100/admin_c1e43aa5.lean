/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Brockian

/-- The `K = 2` Goldbach property: `n` is a sum of two prime numbers. -/
def GoldbachK2 (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Decidable, finitely checkable form of the wheel statement for the modulus `631`:
for every even `n` in the window `[4, 631]` there is a prime `p ≤ 631` such that
`n - p` is again prime. -/
private lemma goldbachK2_631_check :
    ∀ n ∈ Finset.range 632, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range 632, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `631`.**
Every even number `n` with `4 ≤ n ≤ 631` is a sum of two primes. -/
theorem GoldbachWheelK2_631 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 631 → Even n → GoldbachK2 n := by
  intro n h4 h631 hev
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  have hmem : n ∈ Finset.range 632 := Finset.mem_range.mpr (by omega)
  obtain ⟨p, -, hp, hq⟩ := goldbachK2_631_check n hmem h4 hmod
  have h2 : 2 ≤ n - p := hq.two_le
  exact ⟨p, n - p, hp, hq, by omega⟩

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


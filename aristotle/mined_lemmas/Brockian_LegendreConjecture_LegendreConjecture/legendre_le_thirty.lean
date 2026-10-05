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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/

theorem legendre_le_thirty (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 30) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have key : ∀ m ∈ Finset.Icc 1 30, ∃ p ∈ Finset.Ioo (m ^ 2) ((m + 1) ^ 2), Nat.Prime p := by
    decide
  obtain ⟨p, hp, hp'⟩ := key n (Finset.mem_Icc.mpr ⟨hn, hn'⟩)
  rw [Finset.mem_Ioo] at hp
  exact ⟨p, hp', hp.1, hp.2⟩

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — a prime strictly between `n ^ 2` and `(n + 1) ^ 2` for every `n ≥ 1` —
follows from the (also open) hypothesis that every sufficiently large `x` is followed by a
prime in the short interval `(x, x + √x]`.  The remaining small cases `n ≤ 30` are verified
unconditionally, so no assumption is needed for them. -/

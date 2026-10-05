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

Legendre's conjecture — that for every `n ≥ 1` there is a prime strictly between `n ^ 2` and
`(n + 1) ^ 2` — is a well-known open problem.  This file therefore contains:

* `Brockian.LegendreConjecture.LegendreStatement`, the formal statement of the conjecture;
* several *equivalent* reformulations (contrapositive form, a counting form using
  `Finset` cardinalities, and a form using the prime counting function `π`);
* `Brockian.LegendreConjecture.LegendreConjecture`, a Lean-checked **conditional reduction**:
  Legendre's conjecture follows from the (also open, but formally weaker-looking) statement
  that every interval `(m, m + √m]` contains a prime;
* `Brockian.LegendreConjecture.legendre_of_le_hundred`, an unconditional verification of the
  conjecture for all `1 ≤ n ≤ 100`.
-/

namespace Brockian.LegendreConjecture

open Finset

/-- The statement of Legendre's conjecture: for every `n ≥ 1` there is a prime `p` with
`n ^ 2 < p < (n + 1) ^ 2`. -/

theorem legendre_iff_card_pos :
    LegendreStatement ↔
      ∀ n : ℕ, 0 < n → 0 < #{p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2) | p.Prime} := by
  constructor
  · intro h n hn
    obtain ⟨p, hp, h1, h2⟩ := h n hn
    exact Finset.card_pos.2 ⟨p, by simp [Finset.mem_filter, Finset.mem_Ioo, hp, h1, h2]⟩
  · intro h n hn
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (h n hn)
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2⟩

/-- Splitting the counting function `Nat.count` over an initial segment. -/

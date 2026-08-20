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
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Three Prime Carmichael Infinitude
Category: Brockian Conjecture
Target: Brockian.CarmichaelKorselt.ThreePrimeCarmichaelInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace CarmichaelKorselt

/-- Korselt's criterion, used here as the definition of a Carmichael number:
`n` is composite (`1 < n` and not prime), squarefree, and `p - 1 ∣ n - 1` for every
prime `p` dividing `n`. -/

theorem ThreePrimeCarmichaelInfinitude
    (hDickson : ∀ N : ℕ, ∃ k, N < k ∧
      Nat.Prime (6 * k + 1) ∧ Nat.Prime (12 * k + 1) ∧ Nat.Prime (18 * k + 1)) :
    ∀ N : ℕ, ∃ n, N < n ∧ IsCarmichael n ∧ n.primeFactors.card = 3 := by
  intro N
  obtain ⟨k, hkN, h1, h2, h3⟩ := hDickson N
  refine ⟨(6 * k + 1) * (12 * k + 1) * (18 * k + 1), ?_, ?_, ?_⟩
  · calc N < 6 * k + 1 := by omega
      _ ≤ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := by
          have h : (6 * k + 1) ≤ (6 * k + 1) * (12 * k + 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          exact h.trans (Nat.le_mul_of_pos_right _ (by omega))
  · exact (chernick_isCarmichael (by omega) h1 h2 h3).1
  · exact (chernick_isCarmichael (by omega) h1 h2 h3).2

/-- Set-theoretic form of the conditional infinitude statement. -/

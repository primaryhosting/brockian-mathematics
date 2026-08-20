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

theorem squarefree_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : Squarefree (p * q * r) := by
  have hcpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have hcqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  rw [Nat.squarefree_mul (Nat.Coprime.mul_left hcpr hcqr), Nat.squarefree_mul hcpq]
  exact ⟨⟨hp.squarefree, hq.squarefree⟩, hr.squarefree⟩

/-- General criterion for a product of three distinct primes to be Carmichael:
it suffices that `p - 1`, `q - 1` and `r - 1` each divide `pqr - 1`. -/

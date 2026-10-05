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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed immediately after `import Mathlib` because Lean 4
requires `import` commands to precede every other command, including module
docstrings; the header text itself is verbatim.)
-/

set_option maxHeartbeats 1000000

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

lemma prime_of_no_small_prime_factor {m : ℕ} (hm : 1 < m)
    (h : ∀ p : ℕ, p.Prime → p * p ≤ m → ¬ p ∣ m) : m.Prime := by
  by_contra hcomp
  have hpos : 0 < m := lt_trans Nat.zero_lt_one hm
  have hmf : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hle : m.minFac * m.minFac ≤ m := by
    have h' := Nat.minFac_sq_le_self hpos hcomp
    nlinarith [h']
  exact h m.minFac hmf hle (Nat.minFac_dvd m)

/-!
## A partial unconditional result: infinitely many Cullen numbers are composite

For every odd prime `p` one has `p ∣ C (p - 2)`, by Fermat's little theorem:
`C (p-2) = (p-2) * 2 ^ (p-2) + 1 ≡ -2 * 2 ^ (p-2) + 1 = 1 - 2 ^ (p-1) ≡ 0 (mod p)`.
-/

/-- Fermat-type divisibility: every odd prime `p` divides the Cullen number `C (p - 2)`. -/

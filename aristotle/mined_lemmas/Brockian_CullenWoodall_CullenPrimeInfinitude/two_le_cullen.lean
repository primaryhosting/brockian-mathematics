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
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the requested header comment appears verbatim immediately after the
-- single `import Mathlib` line.

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

lemma two_le_cullen {n : ℕ} (hn : 1 ≤ n) : 2 ≤ cullen n := by
  have h : 1 * 2 ^ 1 ≤ n * 2 ^ n :=
    Nat.mul_le_mul hn (Nat.pow_le_pow_right (by norm_num) hn)
  simp only [cullen]
  omega

/-! ## An unconditional divisibility law and infinitely many composite Cullen numbers -/

/-- For every odd prime `p` we have `p ∣ C (p - 2)`: indeed
`(p-2) * 2 ^ (p-2) + 1 ≡ -2 ^ (p-1) + 1 ≡ 0 [MOD p]` by Fermat's little theorem. -/

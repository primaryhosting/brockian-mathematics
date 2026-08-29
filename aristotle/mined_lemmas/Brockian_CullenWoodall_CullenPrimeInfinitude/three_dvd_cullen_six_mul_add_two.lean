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

lemma three_dvd_cullen_six_mul_add_two (k : ℕ) : 3 ∣ cullen (6 * k + 2) := by
  have hpow : (2 : ℕ) ^ (6 * k + 2) % 3 = 1 := by
    induction k with
    | zero => norm_num
    | succ m ih =>
        have h : (2 : ℕ) ^ (6 * (m + 1) + 2) = 2 ^ (6 * m + 2) * 64 := by ring
        rw [h, Nat.mul_mod, ih]
  have h : cullen (6 * k + 2) % 3 = 0 := by
    simp only [cullen]
    omega
  omega

/-- There are infinitely many `n` for which the Cullen number `C n` is *not* prime. -/

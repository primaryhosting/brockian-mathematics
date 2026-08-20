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

/-
Note on file layout: Lean 4 requires all `import` commands to appear before any
other command, including module docstrings, so the mandated header comment above
is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th **Cullen number** `C n = n * 2 ^ n + 1`. -/

theorem lt_cullen_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p < cullen (p - 1) := by
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · omega
    · exact h
  have hpow : 2 ^ 2 ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : (p - 1) * 4 ≤ (p - 1) * 2 ^ (p - 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [cullen]
  omega

/-- For an odd prime `p`, the Cullen number `C (p - 1)` is composite. -/

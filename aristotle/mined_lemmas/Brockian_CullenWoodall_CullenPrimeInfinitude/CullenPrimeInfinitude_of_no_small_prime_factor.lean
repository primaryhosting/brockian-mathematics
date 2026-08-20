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

theorem CullenPrimeInfinitude_of_no_small_prime_factor
    (h : ∀ N : ℕ, ∃ n, N < n ∧ ∀ q : ℕ, q.Prime → q ^ 2 ≤ cullen n → ¬ q ∣ cullen n) :
    cullenPrimeIndices.Infinite := by
  refine CullenPrimeInfinitude fun N => ?_
  obtain ⟨n, hn, hq⟩ := h N
  exact ⟨n, hn, prime_cullen_of_no_small_prime_factor (by omega) hq⟩

/-!
## Unconditional partial results: infinitely many composite Cullen numbers
-/

/-- For an odd prime `p`, Fermat's little theorem gives `p ∣ C (p - 1)`,
since `C (p - 1) ≡ (-1) * 1 + 1 = 0 [MOD p]`. -/

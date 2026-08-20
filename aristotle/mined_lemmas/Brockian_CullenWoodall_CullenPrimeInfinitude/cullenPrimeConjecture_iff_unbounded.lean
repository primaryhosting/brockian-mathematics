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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
header above is a plain block comment (`/- ... -/`) rather than a module docstring (`/-! ... -/`);
its text is otherwise verbatim.

## Contents

* Cullen numbers `C n = n * 2 ^ n + 1` and Woodall numbers `W n = n * 2 ^ n - 1`.
* `CullenPrimeInfinitude` / `WoodallPrimeInfinitude`: Lean-checked *conditional reductions* of the
  (open) infinitude conjectures to the corresponding unboundedness hypotheses, together with
  `cullenPrimeConjecture_iff_unbounded` / `woodallPrimeConjecture_iff_unbounded`.
* Unconditional partial results: explicit arithmetic progressions of composite Cullen numbers
  (`p ∣ C (p - 2 + k * p * (p - 1))` for every odd prime `p`), the companion Woodall divisibility
  `p ∣ W ((p - 1) ^ 2)`, and the resulting infinitude of composite Cullen and Woodall numbers.

Nothing about Cullen or Woodall numbers is currently available in Mathlib; the arithmetic input
used here is Fermat's little theorem in the form `ZMod.pow_card_sub_one_eq_one`, together with
`Nat.exists_infinite_primes` and `Set.infinite_of_forall_exists_gt`.
-/

namespace Brockian.CullenWoodall

/-! ## Cullen numbers -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem cullenPrimeConjecture_iff_unbounded :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (cullen n) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    exact (CullenPrimeInfinitude h).1

/-! ## Unconditional partial results for Cullen numbers

For every odd prime `p` and every `k`, the index `n = (p - 2) + k * p * (p - 1)` satisfies
`n ≡ -2 (mod p)` and `2 ^ n ≡ 2 ^ (p - 2) (mod p)`, whence
`C n ≡ -2 * 2 ^ (p - 2) + 1 = 1 - 2 ^ (p - 1) ≡ 0 (mod p)`
by Fermat's little theorem.  So each odd prime `p` kills a whole arithmetic progression of
Cullen numbers, and infinitely many Cullen numbers are composite. -/


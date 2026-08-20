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

theorem infinite_woodall_not_prime : {n : ℕ | ¬ IsWoodallPrime n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max 3 (a + 2))
  have h3 : 3 ≤ p := le_trans (le_max_left _ _) hple
  have ha : a + 2 ≤ p := le_trans (le_max_right _ _) hple
  refine ⟨(p - 1) ^ 2, woodall_sq_not_prime hp (by omega), ?_⟩
  have hsq : (p - 1) ^ 2 = (p - 1) * (p - 1) := by ring
  have : (p - 1) * 2 ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

end Brockian.CullenWoodall


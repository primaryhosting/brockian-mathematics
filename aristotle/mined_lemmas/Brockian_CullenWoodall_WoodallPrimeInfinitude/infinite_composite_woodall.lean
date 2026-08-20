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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; harmless
since `n * 2 ^ n ≥ 1` for `n ≥ 1`). -/

theorem infinite_composite_woodall : {n : ℕ | 1 ≤ n ∧ ¬ (woodall n).Prime}.Infinite := by
  apply Set.Infinite.mono (s := Set.range (fun k : ℕ => 6 * k + 4))
  · rintro _ ⟨k, rfl⟩
    show 1 ≤ 6 * k + 4 ∧ ¬ (woodall (6 * k + 4)).Prime
    exact ⟨by omega, woodall_not_prime_of_mod_six (Or.inl (by omega))⟩
  · exact Set.infinite_range_of_injective (fun a b h => by
      have h' : 6 * a + 4 = 6 * b + 4 := h
      omega)

/-! ## Reduction of the conjecture to the set of indices -/

/-- **Woodall prime infinitude (Lean-checked reduction).**  The infinitude of the set of
Woodall primes is *equivalent* to the infinitude of the set of indices `n ≥ 1` for which
`n * 2 ^ n - 1` is prime.  (The unconditional infinitude of Woodall primes is an open
problem; what is proved here is this reduction.) -/

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

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem woodall_prime_infinite_iff :
    {q : ℕ | q.Prime ∧ ∃ n, 1 ≤ n ∧ q = woodall n}.Infinite ↔
      ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (woodall n) := by
  refine ⟨fun hinf N => ?_, WoodallPrimeInfinitude⟩
  obtain ⟨q, ⟨hq, n, h1, rfl⟩, hlt⟩ := hinf.exists_gt (woodall N)
  refine ⟨n, ?_, hq⟩
  by_contra hc
  have hnN : n ≤ N := by omega
  rcases eq_or_lt_of_le hnN with h | h
  · subst h; omega
  · exact absurd (woodall_lt_woodall h1 h) (by omega)

/-! ## Cullen companion: every odd prime divides a Cullen number -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

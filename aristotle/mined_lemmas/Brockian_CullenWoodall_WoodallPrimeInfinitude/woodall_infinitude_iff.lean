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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction). -/

theorem woodall_infinitude_iff :
    {p : ℕ | IsWoodallPrime p}.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ (woodall n).Prime := by
  constructor
  · intro hinf N
    obtain ⟨p, hp, hlt⟩ := hinf.exists_gt (woodall N)
    obtain ⟨hprime, m, -, rfl⟩ := hp
    refine ⟨m, ?_, hprime⟩
    by_contra hle
    have := woodall_mono (show m ≤ N by omega)
    omega
  · intro h
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro N
    obtain ⟨n, hn, hprime⟩ := h (N + 2)
    refine ⟨woodall n, ⟨hprime, n, by omega, rfl⟩, ?_⟩
    have := le_woodall (n := n) (by omega)
    omega

/-- **Conditional infinitude of Woodall primes.**  If for every bound `N` there is an index
`n > N` for which the Woodall number `n * 2 ^ n - 1` is prime, then there are infinitely many
Woodall primes.  (The hypothesis is exactly the — still open — Woodall prime conjecture, so this
is a Lean-checked reduction of the conjecture to its index formulation, not an unconditional
proof.) -/

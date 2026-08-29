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

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RieselCovering

/-- `IsComposite N` means that `N` factors as a product of two factors, each `> 1`. -/

theorem pow24_mul (p t : Nat) (ht : 2 ^ 24 = 1 + p * t) :
    ∀ q : Nat, ∃ s : Nat, 2 ^ (24 * q) = 1 + p * s := by
  intro q
  induction q with
  | zero => exact ⟨0, by simp⟩
  | succ q ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨s + t + p * s * t, ?_⟩
      have h1 : 24 * (q + 1) = 24 * q + 24 := by omega
      rw [h1, Nat.pow_add, hs, ht]
      grind

/-- The heart of the covering argument: for every `n`, the number `509203 * 2 ^ n - 1`
is divisible by `cov (n % 24)`, with an explicit cofactor. -/

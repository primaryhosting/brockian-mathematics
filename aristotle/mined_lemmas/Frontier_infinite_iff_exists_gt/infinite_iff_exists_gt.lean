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
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/

theorem infinite_iff_exists_gt (S : Set ℕ) : S.Infinite ↔ ∀ N : ℕ, ∃ n ∈ S, N < n := by
  constructor
  · intro h N
    obtain ⟨n, hn, hN⟩ := h.exists_gt N
    exact ⟨n, hn, hN⟩
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    obtain ⟨n, hn, hlt⟩ := h N
    exact absurd (hN hn) (by omega)

/-- Reformulation of Artin's conjecture: for each admissible `a` there are arbitrarily large
primes having `a` as a primitive root. -/

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

import RequestProject.AKS.Defs

/-!
# Introspective exponents

Fix a prime `p` and let `F = AlgebraicClosure (ZMod p)`.  A natural number `m` is
*introspective* for a polynomial `f ∈ 𝔽ₚ[X]` (relative to `r`) if `f(z)^m = f(z^m)` for every
`r`-th root of unity `z ∈ F`.  This is the key notion in the AKS correctness proof.
-/

open Polynomial

namespace CS
namespace AKS

/-- The algebraic closure of `𝔽ₚ`, the field in which the AKS argument takes place. -/
abbrev AC (p : ℕ) [Fact p.Prime] := AlgebraicClosure (ZMod p)

variable {p : ℕ} [Fact p.Prime]

/-- `m` is introspective for `f`: `f(z)^m = f(z^m)` for all `r`-th roots of unity `z`. -/

lemma pow_eq_pow_of_modEq {M : Type*} [CommMonoid M] {r : ℕ} {z : M} (h1 : z ^ r = 1) {i j : ℕ}
    (hij : i ≡ j [MOD r]) : z ^ i = z ^ j := by
  have h2 : z ^ (i % r) = z ^ (j % r) := by rw [hij]
  calc z ^ i = z ^ (r * (i / r) + i % r) := by rw [Nat.div_add_mod]
    _ = (z ^ r) ^ (i / r) * z ^ (i % r) := by rw [pow_add, pow_mul]
    _ = z ^ (i % r) := by rw [h1, one_pow, one_mul]
    _ = z ^ (j % r) := h2
    _ = (z ^ r) ^ (j / r) * z ^ (j % r) := by rw [h1, one_pow, one_mul]
    _ = z ^ (r * (j / r) + j % r) := by rw [pow_add, pow_mul]
    _ = z ^ j := by rw [Nat.div_add_mod]

/-- In a finite group every integer power is a natural power. -/

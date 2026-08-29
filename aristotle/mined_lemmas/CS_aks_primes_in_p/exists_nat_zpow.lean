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

lemma exists_nat_zpow {G : Type*} [Group G] [Finite G] (g : G) (z : ℤ) :
    ∃ k : ℕ, g ^ z = g ^ k := by
  have hd : 0 < orderOf g := orderOf_pos g
  set d := orderOf g with hdd
  set N : ℕ := z.natAbs with hN
  have hN1 : (N : ℤ) ≤ (d : ℤ) * N := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hd)
  have hN2 : -z ≤ (N : ℤ) := by omega
  have hnn : 0 ≤ z + d * N := by linarith
  refine ⟨(z + d * N).toNat, ?_⟩
  have hz : ((z + d * N).toNat : ℤ) = z + d * N := Int.toNat_of_nonneg hnn
  rw [← zpow_natCast g ((z + d * N).toNat), hz, zpow_add g z ((d : ℤ) * N), zpow_mul,
    zpow_natCast g d, hdd, pow_orderOf_eq_one, one_zpow, mul_one]

/-- A finite set of field elements all satisfying `v ^ m₁ = v ^ m₂` with `m₂ < m₁` has at most
`m₁` elements: they are all roots of the nonzero polynomial `X ^ m₁ - X ^ m₂`. -/

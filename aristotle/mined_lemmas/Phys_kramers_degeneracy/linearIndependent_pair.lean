/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-- A *time-reversal operator* on a complex inner product space `V` for a system of
half-integer spin: an antiunitary map (additive, conjugate-linear, and antipreserving the
inner product) whose square is `-1`. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- the underlying map -/
  toFun : V → V
  /-- additivity -/
  map_add : ∀ x y : V, toFun (x + y) = toFun x + toFun y
  /-- conjugate-linearity -/
  map_smul : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  /-- antiunitarity: `⟪T x, T y⟫ = ⟪y, x⟫` -/
  inner_map : ∀ x y : V, ⟪toFun x, toFun y⟫_ℂ = ⟪y, x⟫_ℂ
  /-- half-integer spin: `T² = -1` -/
  sq_eq_neg : ∀ x : V, toFun (toFun x) = -x

namespace TimeReversal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩


theorem linearIndependent_pair (T : TimeReversal V) {x : V} (hx : x ≠ 0) :
    LinearIndependent ℂ ![x, T x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : ⟪x, s • x + t • T x⟫_ℂ = 0 := by rw [hst, inner_zero_right]
  have h2 : ⟪T x, s • x + t • T x⟫_ℂ = 0 := by rw [hst, inner_zero_right]
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    T.inner_self_apply_eq_zero x] at h1
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    T.inner_apply_self_eq_zero x] at h2
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hx
  have hTT : ⟪T x, T x⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using T.apply_ne_zero hx
  constructor
  · have : s * ⟪x, x⟫_ℂ = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hxx
  · have : t * ⟪T x, T x⟫_ℂ = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_right hTT

end TimeReversal

/-- **Kramers degeneracy.**

Let `H` be the Hamiltonian of a quantum system on a complex inner product space `V`,
and let `T` be a time-reversal operator for half-integer spin, i.e. an antiunitary map with
`T² = -1`.  Assume the system is time-reversal invariant, `H ∘ T = T ∘ H`.

Then for every (real) energy level `E` with a nonzero eigenvector `ψ`, the time-reversed
state `T ψ` is again an eigenvector with the same energy, it is orthogonal to `ψ`, and
consequently the eigenspace of `H` at `E` has dimension at least `2`: every level is
(at least) doubly degenerate. -/

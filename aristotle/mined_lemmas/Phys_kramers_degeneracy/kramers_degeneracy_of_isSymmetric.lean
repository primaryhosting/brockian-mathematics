import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Statement: A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped InnerProductSpace
open ComplexConjugate

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator of half-integer-spin type*: an antiunitary map `T` (additive,
conjugate-linear, inner-product-conjugating) whose square is `-1`. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (c : ℂ) (x : V), toFun (c • x) = conj c • toFun x
  inner_map : ∀ x y, ⟪toFun x, toFun y⟫_ℂ = conj ⟪x, y⟫_ℂ
  /-- Half-integer spin: the square of time reversal is `-1`. -/
  sq_eq_neg : ∀ x, toFun (toFun x) = -x

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

/-- The Kramers partner of a nonzero vector is nonzero. -/

theorem kramers_degeneracy_of_isSymmetric (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric)
    (T : TimeReversal V) (hcomm : ∀ x, T (H x) = H (T x))
    (lam : ℂ) (v : V) (hv : v ≠ 0) (hHv : H v = lam • v) :
    2 ≤ Module.rank ℂ (Module.End.eigenspace H lam) := by
  have hmem : v ∈ Module.End.eigenspace H lam := by
    simpa [Module.End.mem_eigenspace_iff] using hHv
  have hlam : conj lam = lam :=
    hH.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hv⟩)
  exact kramers_degeneracy H T hcomm lam hlam v hv hHv

end Phys

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


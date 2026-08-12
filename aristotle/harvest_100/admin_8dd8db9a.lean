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
theorem TimeReversal.apply_ne_zero (T : TimeReversal V) {v : V} (hv : v ≠ 0) : T v ≠ 0 := by
  intro h
  apply hv
  have := T.sq_eq_neg v
  rw [h] at this
  have hT0 : T (0 : V) = 0 := by
    have := T.map_add 0 0
    simpa using this.symm
  rw [hT0] at this
  simpa using this.symm

/-- **Kramers orthogonality**: a vector is orthogonal to its time-reversed partner. -/
theorem TimeReversal.inner_self_apply_eq_zero (T : TimeReversal V) (v : V) :
    ⟪v, T v⟫_ℂ = 0 := by
  have h1 : ⟪T v, T (T v)⟫_ℂ = conj ⟪v, T v⟫_ℂ := T.inner_map v (T v)
  rw [T.sq_eq_neg v, inner_neg_right, inner_conj_symm] at h1
  have h2 : ⟪v, T v⟫_ℂ + ⟪v, T v⟫_ℂ = 0 := by
    have := congrArg (fun z : ℂ => conj z) h1
    simp only [RingHom.map_neg] at this
    rw [inner_conj_symm] at this
    -- `this : ⟪v, T v⟫ = - ⟪v, T v⟫`
    linear_combination -this
  linear_combination h2 / 2

/-- The Kramers pair `(v, T v)` is linearly independent when `v ≠ 0`. -/
theorem TimeReversal.linearIndependent_pair (T : TimeReversal V) {v : V} (hv : v ≠ 0) :
    LinearIndependent ℂ ![v, T v] := by
  have hTv : T v ≠ 0 := T.apply_ne_zero hv
  have horth : ⟪v, T v⟫_ℂ = 0 := T.inner_self_apply_eq_zero v
  have horth' : ⟪T v, v⟫_ℂ = 0 := by
    have := congrArg (fun z : ℂ => conj z) horth
    simpa [inner_conj_symm] using this
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrArg (fun w => ⟪v, w⟫_ℂ) hst
    simp only [inner_add_right, inner_smul_right, horth, inner_zero_right] at h
    have hvv : (⟪v, v⟫_ℂ) ≠ 0 := by
      simpa [inner_self_eq_zero] using hv
    have : s * ⟪v, v⟫_ℂ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hvv
  · have h := congrArg (fun w => ⟪T v, w⟫_ℂ) hst
    simp only [inner_add_right, inner_smul_right, horth', inner_zero_right] at h
    have hvv : (⟪T v, T v⟫_ℂ) ≠ 0 := by
      simpa [inner_self_eq_zero] using hTv
    have : t * ⟪T v, T v⟫_ℂ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_right hvv

/-- **Kramers degeneracy.**  Let `H` be the Hamiltonian of a system with a time-reversal
symmetry `T` of half-integer-spin type (`T` antiunitary, `T² = -1`) which commutes with `H`.
Then every eigenvalue `lam` of `H` (real, as it is for a self-adjoint `H`) has an eigenspace
of dimension at least `2`: the levels are (at least) doubly degenerate. -/
theorem kramers_degeneracy (H : V →ₗ[ℂ] V) (T : TimeReversal V)
    (hcomm : ∀ x, T (H x) = H (T x))
    (lam : ℂ) (hlam : conj lam = lam) (v : V) (hv : v ≠ 0) (hHv : H v = lam • v) :
    2 ≤ Module.rank ℂ (Module.End.eigenspace H lam) := by
  have hmemv : v ∈ Module.End.eigenspace H lam := by
    simpa [Module.End.mem_eigenspace_iff] using hHv
  have hHTv : H (T v) = lam • T v := by
    have := hcomm v
    rw [hHv, T.map_smul, hlam] at this
    exact this.symm
  have hmemTv : T v ∈ Module.End.eigenspace H lam := by
    simpa [Module.End.mem_eigenspace_iff] using hHTv
  set W := Module.End.eigenspace H lam
  set w : Fin 2 → W := ![⟨v, hmemv⟩, ⟨T v, hmemTv⟩] with hw
  have hli : LinearIndependent ℂ w := by
    have hcomp : (W.subtype ∘ w) = ![v, T v] := by
      funext i
      fin_cases i <;> simp [hw]
    have : LinearIndependent ℂ (W.subtype ∘ w) := by
      rw [hcomp]; exact T.linearIndependent_pair hv
    exact this.of_comp W.subtype
  have := hli.cardinal_lift_le_rank
  simpa using this

/-- **Kramers degeneracy for a self-adjoint Hamiltonian.**  If `H` is symmetric (self-adjoint)
and commutes with a half-integer-spin time reversal `T`, then every eigenvalue of `H` has
eigenspace of dimension at least `2`. -/
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


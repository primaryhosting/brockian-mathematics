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

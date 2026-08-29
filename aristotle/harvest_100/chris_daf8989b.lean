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

@[simp] theorem map_zero (T : TimeReversal V) : T 0 = 0 := by
  have h := T.map_add 0 0
  simp only [add_zero] at h
  linear_combination (norm := module) -h

/-- A time-reversal operator never kills a nonzero vector. -/
theorem apply_ne_zero (T : TimeReversal V) {x : V} (hx : x ≠ 0) : T x ≠ 0 := by
  intro h
  have hsq := T.sq_eq_neg x
  rw [h, T.map_zero] at hsq
  exact hx (by simpa using hsq.symm)

/-- **Kramers orthogonality**: every vector is orthogonal to its time reverse. -/
theorem inner_apply_self_eq_zero (T : TimeReversal V) (x : V) : ⟪T x, x⟫_ℂ = 0 := by
  have h := T.inner_map x (T x)
  rw [T.sq_eq_neg x, inner_neg_right] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem inner_self_apply_eq_zero (T : TimeReversal V) (x : V) : ⟪x, T x⟫_ℂ = 0 := by
  have h := inner_conj_symm (𝕜 := ℂ) x (T x)
  rw [T.inner_apply_self_eq_zero x] at h
  simpa using h.symm

/-- A nonzero vector and its time reverse are linearly independent (they are orthogonal
and both nonzero). -/
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
theorem kramers_degeneracy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : TimeReversal V) (H : Module.End ℂ V) (hcomm : ∀ x : V, H (T x) = T (H x))
    (E : ℝ) (ψ : V) (hψ : ψ ≠ 0) (heig : H ψ = (E : ℂ) • ψ) :
    T ψ ≠ 0 ∧ H (T ψ) = (E : ℂ) • T ψ ∧ ⟪ψ, T ψ⟫_ℂ = 0 ∧
      2 ≤ Module.rank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  have hTψ : T ψ ≠ 0 := T.apply_ne_zero hψ
  have hEig2 : H (T ψ) = (E : ℂ) • T ψ := by
    rw [hcomm ψ, heig, T.map_smul]
    simp
  have hOrth : ⟪ψ, T ψ⟫_ℂ = 0 := T.inner_self_apply_eq_zero ψ
  refine ⟨hTψ, hEig2, hOrth, ?_⟩
  -- both `ψ` and `T ψ` live in the eigenspace
  have hm1 : ψ ∈ Module.End.eigenspace H (E : ℂ) := Module.End.mem_eigenspace_iff.mpr heig
  have hm2 : T ψ ∈ Module.End.eigenspace H (E : ℂ) := Module.End.mem_eigenspace_iff.mpr hEig2
  set W := Module.End.eigenspace H (E : ℂ)
  have hli : LinearIndependent ℂ ![ψ, T ψ] := T.linearIndependent_pair hψ
  have hli' : LinearIndependent ℂ (![(⟨ψ, hm1⟩ : W), ⟨T ψ, hm2⟩]) := by
    refine LinearIndependent.of_comp (W.subtype) ?_
    convert hli using 1
    funext i
    fin_cases i <;> rfl
  have := hli'.cardinal_lift_le_rank
  simpa using this


/-! ### Non-vacuity: the spin-`1/2` time-reversal operator on `ℂ²`

`T = -i σ_y K`, i.e. `T (a, b) = (-conj b, conj a)`, is a genuine example of the structure
`Phys.TimeReversal`, so the hypotheses of `Phys.kramers_degeneracy` are satisfiable. -/

/-- Time reversal for a single spin-`1/2`, acting on `ℂ²`. -/
noncomputable def spinHalfTimeReversal : TimeReversal (EuclideanSpace ℂ (Fin 2)) where
  toFun x := WithLp.toLp 2 ![-(starRingEnd ℂ) (x 1), (starRingEnd ℂ) (x 0)]
  map_add x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul c x := by ext i; fin_cases i <;> simp
  inner_map x y := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_neg,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  sq_eq_neg x := by ext i; fin_cases i <;> simp

end Phys


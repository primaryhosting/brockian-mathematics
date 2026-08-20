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

set_option grind.warning false

namespace Phys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A *time-reversal operator* on a complex inner product space: an antiunitary map `T`
(additive, conjugate-homogeneous, and inner-product reversing) which squares to `-1`.
The condition `T (T a) = -a` is exactly what holds for half-integer spin
(for integer spin one has `T² = +1`). -/
structure IsTimeReversal (T : V → V) : Prop where
  /-- `T` is additive. -/
  map_add : ∀ a b, T (a + b) = T a + T b
  /-- `T` is conjugate-homogeneous. -/
  map_smul : ∀ (c : ℂ) (a : V), T (c • a) = (starRingEnd ℂ) c • T a
  /-- `T` is antiunitary: it conjugates inner products. -/
  inner_map : ∀ a b, ⟪T a, T b⟫_ℂ = ⟪b, a⟫_ℂ
  /-- Half-integer spin: `T² = -1`. -/
  sq_eq_neg : ∀ a, T (T a) = -a

/-- For a half-integer-spin time reversal, `T x` is orthogonal to `x`. -/
lemma IsTimeReversal.inner_apply_self {T : V → V} (hT : IsTimeReversal T) (x : V) :
    ⟪T x, x⟫_ℂ = 0 := by
  have h := hT.inner_map x (T x)
  rw [hT.sq_eq_neg, inner_neg_right] at h
  linear_combination -h / 2

lemma IsTimeReversal.map_zero {T : V → V} (hT : IsTimeReversal T) : T 0 = 0 := by
  simpa using hT.map_smul 0 0

lemma IsTimeReversal.apply_ne_zero {T : V → V} (hT : IsTimeReversal T) {x : V} (hx : x ≠ 0) :
    T x ≠ 0 := by
  intro h
  have h2 := hT.sq_eq_neg x
  rw [h, hT.map_zero] at h2
  exact hx (by simpa using h2.symm)

/-- The *Kramers pair* `x, T x` of a nonzero vector is linearly independent
(indeed orthogonal), when `T² = -1`. -/
lemma IsTimeReversal.linearIndependent {T : V → V} (hT : IsTimeReversal T) {x : V} (hx : x ≠ 0) :
    LinearIndependent ℂ ![x, T x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hxT : ⟪x, T x⟫_ℂ = 0 := by
    simpa using congrArg (starRingEnd ℂ) (hT.inner_apply_self x)
  constructor
  · have := congrArg (fun v => ⟪x, v⟫_ℂ) hst
    simp [hxT] at this
    rcases this with h | h
    · exact h
    · exact absurd h hx
  · have := congrArg (fun v => ⟪T x, v⟫_ℂ) hst
    simp [hT.inner_apply_self x] at this
    rcases this with h | h
    · exact h
    · exact absurd h (hT.apply_ne_zero hx)

/-- **Kramers degeneracy.** Let `H` be the Hamiltonian (a symmetric, i.e. self-adjoint,
operator) of a finite-dimensional quantum system with half-integer spin, meaning that it
admits a time-reversal symmetry `T` with `T² = -1` commuting with `H`. Then every energy
level of `H` is (at least) doubly degenerate: its eigenspace has dimension at least `2`.

The proof: an eigenvector `x` with eigenvalue `μ` has `μ` real
(`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`), so `T x` lies in the same eigenspace,
and antiunitarity together with `T² = -1` forces `⟪T x, x⟫ = 0`, so `x` and `T x` are
linearly independent. -/
theorem kramers_degeneracy [FiniteDimensional ℂ V] {T : V → V} (hT : IsTimeReversal T)
    {H : V →ₗ[ℂ] V} (hH : H.IsSymmetric) (hTH : ∀ a, T (H a) = H (T a)) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue H μ) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H μ) := by
  obtain ⟨x, hx_mem, hx⟩ := hμ.exists_hasEigenvector
  have hμreal : (starRingEnd ℂ) μ = μ := hH.conj_eigenvalue_eq_self hμ
  have hxe : H x = μ • x := Module.End.mem_eigenspace_iff.mp hx_mem
  have hTx : H (T x) = μ • T x := by
    rw [← hTH x, hxe, hT.map_smul, hμreal]
  have hindep : LinearIndependent ℂ ![x, T x] := hT.linearIndependent hx
  set W := Module.End.eigenspace H μ with hW
  have hmem1 : x ∈ W := hx_mem
  have hmem2 : T x ∈ W := Module.End.mem_eigenspace_iff.mpr hTx
  have hsub : LinearIndependent ℂ ![(⟨x, hmem1⟩ : W), ⟨T x, hmem2⟩] := by
    apply LinearIndependent.of_comp W.subtype
    convert hindep using 1
    ext i
    fin_cases i <;> simp
  simpa using hsub.fintype_card_le_finrank

/-! ### A concrete spin-1/2 system, showing the hypotheses are satisfiable -/

/-- Time reversal for a single spin-1/2 particle, `T = -i σ_y K` on `ℂ²`. -/
noncomputable def spinHalfT : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
  fun x => WithLp.toLp 2 ![-(starRingEnd ℂ) (x 1), (starRingEnd ℂ) (x 0)]

lemma inner_euclidean_two (a b : EuclideanSpace ℂ (Fin 2)) :
    ⟪a, b⟫_ℂ = (starRingEnd ℂ) (a 0) * b 0 + (starRingEnd ℂ) (a 1) * b 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, mul_comm]

lemma isTimeReversal_spinHalfT : IsTimeReversal spinHalfT where
  map_add a b := by
    ext i; fin_cases i <;> simp [spinHalfT, add_comm]
  map_smul c a := by
    ext i; fin_cases i <;> simp [spinHalfT]
  inner_map a b := by
    simp [inner_euclidean_two, spinHalfT]; ring
  sq_eq_neg a := by
    ext i; fin_cases i <;> simp [spinHalfT]

/-- The Kramers theorem applied to a spin-1/2 particle with Hamiltonian `H = 1`:
the energy level `1` is doubly degenerate. -/
example : 2 ≤ Module.finrank ℂ
    (Module.End.eigenspace (LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] _) 1) := by
  have hx : (EuclideanSpace.single 0 (1 : ℂ) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
    intro h
    have := congrFun (congrArg WithLp.ofLp h) 0
    simp at this
  exact kramers_degeneracy isTimeReversal_spinHalfT (fun _ _ => rfl) (fun _ => rfl)
    (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by simp), hx⟩)

end Phys


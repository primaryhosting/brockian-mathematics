import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Statement: A time-reversal-invariant half-integer-spin system has doubly degenerate levels (Kramers).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Phys

/-- A vector and its image under an antiunitary time-reversal operator squaring to `-1`
are linearly independent (the algebraic heart of Kramers' theorem). -/
theorem kramers_pair_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ⋆[ℂ] V) (hT : ∀ v, T (T v) = -v) (v : V) (hv : v ≠ 0) :
    LinearIndependent ℂ ![v, T v] := by
  have hsmul : ∀ (a b : ℂ), a • v = b • v → a = b := by
    intro a b hab
    by_contra hne
    have h0 : (a - b) • v = 0 := by
      rw [sub_smul, hab, sub_self]
    have : v = 0 := by
      have := congrArg (fun w => (a - b)⁻¹ • w) h0
      simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne)] using this
    exact hv this
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hv
  · -- `T v = c • v` with `c = -s/t`, then `T (T v) = |c|^2 • v = -v` forces `|c|^2 = -1`
    have hTv : T v = (-(s / t)) • v := by
      have : t • T v = (-s) • v := by
        rw [neg_smul, eq_comm, neg_eq_iff_add_eq_zero]
        exact hst
      have := congrArg (fun w => t⁻¹ • w) this
      simpa [smul_smul, inv_mul_cancel₀ ht, div_eq_inv_mul, mul_comm] using this
    have h2 : T (T v) = (starRingEnd ℂ (-(s / t)) * (-(s / t))) • v := by
      rw [hTv, map_smulₛₗ, hTv, smul_smul]
    rw [hT v] at h2
    have h3 : (-1 : ℂ) = starRingEnd ℂ (-(s / t)) * (-(s / t)) := by
      apply hsmul
      rw [← h2]
      simp
    set c : ℂ := -(s / t) with hc
    have h4 : (Complex.normSq c : ℂ) = -1 := by
      rw [h3, Complex.normSq_eq_conj_mul_self]
    have h5 : Complex.normSq c = -1 := by exact_mod_cast h4
    have := Complex.normSq_nonneg c
    linarith [h5 ▸ this]

/-- **Kramers degeneracy.**  Let `V` be a complex vector space carrying an antilinear
time-reversal operator `T` with `T² = -1` (a half-integer-spin system), and let `H` be a
Hamiltonian commuting with `T`.  Then for every eigenvector `v` of `H` with real eigenvalue `e`,
the vector `T v` is an eigenvector with the *same* eigenvalue, linearly independent from `v`;
consequently every energy level has degeneracy at least two. -/
theorem kramers_degeneracy {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ⋆[ℂ] V) (hT : ∀ v, T (T v) = -v)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ v, T (H v) = H (T v))
    (e : ℝ) (v : V) (hv : v ≠ 0) (hHv : H v = (e : ℂ) • v) :
    H (T v) = (e : ℂ) • T v ∧ LinearIndependent ℂ ![v, T v] ∧
      2 ≤ Module.rank ℂ (LinearMap.ker (H - (e : ℂ) • LinearMap.id)) := by
  have heig : H (T v) = (e : ℂ) • T v := by
    rw [← hcomm v, hHv, map_smulₛₗ]
    simp
  have hind : LinearIndependent ℂ ![v, T v] := kramers_pair_independent T hT v hv
  refine ⟨heig, hind, ?_⟩
  -- both `v` and `T v` lie in the eigenspace
  have hmemv : v ∈ LinearMap.ker (H - (e : ℂ) • LinearMap.id) := by
    simp [LinearMap.mem_ker, hHv]
  have hmemTv : T v ∈ LinearMap.ker (H - (e : ℂ) • LinearMap.id) := by
    simp [LinearMap.mem_ker, heig]
  set W := LinearMap.ker (H - (e : ℂ) • LinearMap.id)
  set f : Fin 2 → W := ![⟨v, hmemv⟩, ⟨T v, hmemTv⟩] with hf
  have hcomp : (W.subtype) ∘ f = ![v, T v] := by
    funext i
    fin_cases i <;> simp [hf]
  have hfi : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp W.subtype
    rw [hcomp]
    exact hind
  have := hfi.cardinal_lift_le_rank
  simpa using this

/-- The spin-1/2 time-reversal operator `T = i σ_y K` on `ℂ × ℂ`, as a conjugate-linear map. -/
def spinHalfTimeReversal : (ℂ × ℂ) →ₗ⋆[ℂ] (ℂ × ℂ) where
  toFun p := (-(starRingEnd ℂ p.2), starRingEnd ℂ p.1)
  map_add' p q := by simp [Prod.ext_iff]; ring
  map_smul' c p := by simp

/-- The spin-1/2 time-reversal operator squares to `-1`, so the hypotheses of
`Phys.kramers_degeneracy` are satisfiable: the theorem is not vacuous. -/
theorem spinHalfTimeReversal_sq (p : ℂ × ℂ) :
    spinHalfTimeReversal (spinHalfTimeReversal p) = -p := by
  simp [spinHalfTimeReversal, Prod.ext_iff]

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


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

/-- An **antiunitary time-reversal operator** on a complex inner product space `V`:
an additive, conjugate-linear map preserving the inner product up to conjugation. -/
structure TimeReversal (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying map. -/
  toFun : V → V
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : ℂ) (x : V), toFun (c • x) = (starRingEnd ℂ) c • toFun x
  inner_map' : ∀ x y, inner ℂ (toFun x) (toFun y) = inner ℂ y x

namespace TimeReversal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance : CoeFun (TimeReversal V) (fun _ => V → V) := ⟨TimeReversal.toFun⟩

/-- For a half-integer-spin time reversal (`Θ² = -1`), every vector is orthogonal to its
time-reverse. -/

theorem kramers_degeneracy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Θ : TimeReversal V) (hsq : ∀ x, Θ (Θ x) = -x)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ x, Θ (H x) = H (Θ x))
    (E : ℝ) (ψ : V) (hψ : ψ ≠ 0) (heig : H ψ = (E : ℂ) • ψ) :
    Θ ψ ≠ 0 ∧ inner ℂ ψ (Θ ψ) = 0 ∧ H (Θ ψ) = (E : ℂ) • Θ ψ ∧
      2 ≤ Module.rank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  -- `Θ ψ ≠ 0`
  have hΘψ : Θ ψ ≠ 0 := by
    intro h
    apply hψ
    have := hsq ψ
    rw [h] at this
    have hz : Θ (0 : V) = 0 := by
      have := Θ.map_smul' 0 0
      simpa using this
    rw [hz] at this
    simpa using this.symm
  -- orthogonality
  have horth : inner ℂ (Θ ψ) ψ = 0 := Θ.inner_self_eq_zero hsq ψ
  have horth' : inner ℂ ψ (Θ ψ) = 0 := by
    have := congrArg (starRingEnd ℂ) horth
    rwa [inner_conj_symm, map_zero] at this
  -- `Θ ψ` is an eigenvector with the same (real) eigenvalue
  have heig2 : H (Θ ψ) = (E : ℂ) • Θ ψ := by
    have := hcomm ψ
    rw [heig, Θ.map_smul'] at this
    simpa using this.symm
  refine ⟨hΘψ, horth', heig2, ?_⟩
  -- linear independence of `ψ` and `Θ ψ` inside the eigenspace
  have hmem1 : ψ ∈ Module.End.eigenspace H (E : ℂ) := by
    simp [heig]
  have hmem2 : Θ ψ ∈ Module.End.eigenspace H (E : ℂ) := by
    simp [heig2]
  set W := Module.End.eigenspace H (E : ℂ)
  have hli : LinearIndependent ℂ ![(⟨ψ, hmem1⟩ : W), ⟨Θ ψ, hmem2⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : s • ψ + t • Θ ψ = 0 := by
      have := congrArg (Submodule.subtype W) hst
      simpa using this
    constructor
    · have h1 : inner ℂ ψ (s • ψ + t • Θ ψ) = 0 := by rw [hst']; simp
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth'] at h1
      have hne : (inner ℂ ψ ψ : ℂ) ≠ 0 := by
        simpa [inner_self_eq_zero] using hψ
      have : s * inner ℂ ψ ψ = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right hne
    · have h1 : inner ℂ (Θ ψ) (s • ψ + t • Θ ψ) = 0 := by rw [hst']; simp
      rw [inner_add_right, inner_smul_right, inner_smul_right, horth] at h1
      have hne : (inner ℂ (Θ ψ) (Θ ψ) : ℂ) ≠ 0 := by
        simpa [inner_self_eq_zero] using hΘψ
      have : t * inner ℂ (Θ ψ) (Θ ψ) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_right hne
  simpa using hli.cardinal_lift_le_rank

end Phys


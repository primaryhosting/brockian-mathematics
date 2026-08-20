import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma cone_equidecomp {A B : Set E} (hA : A ⊆ sph) (hB : B ⊆ sph)
    (h : IsEquidecomposable SO3 A B) : IsEquidecomposable SO3 (cone A) (cone B) := by
  obtain ⟨f, hfs, hft⟩ := h
  obtain ⟨S, hS⟩ := f.isDecompOn'
  have hmapA : ∀ x ∈ A, f.toPartialEquiv x ∈ B := by
    intro x hx
    have := f.toPartialEquiv.map_source (show x ∈ f.source by rw [hfs]; exact hx)
    rwa [hft] at this
  have hmapB : ∀ y ∈ B, f.toPartialEquiv.symm y ∈ A := by
    intro y hy
    have := f.toPartialEquiv.map_target (show y ∈ f.target by rw [hft]; exact hy)
    rwa [hfs] at this
  have hleft : ∀ x ∈ A, f.toPartialEquiv.symm (f.toPartialEquiv x) = x := by
    intro x hx
    exact f.toPartialEquiv.left_inv (show x ∈ f.source by rw [hfs]; exact hx)
  have hright : ∀ y ∈ B, f.toPartialEquiv (f.toPartialEquiv.symm y) = y := by
    intro y hy
    exact f.toPartialEquiv.right_inv (show y ∈ f.target by rw [hft]; exact hy)
  refine ⟨⟨⟨rad (f.toPartialEquiv), rad (f.toPartialEquiv.symm), cone A, cone B,
    ?_, ?_, ?_, ?_⟩, ⟨S, ?_⟩⟩, rfl, rfl⟩
  · intro v hv
    exact rad_mem_cone hv hB (hmapA _ hv.2.2)
  · intro v hv
    exact rad_mem_cone hv hA (hmapB _ hv.2.2)
  · intro v hv
    exact rad_rad_apply hv.1 hB (hmapA _ hv.2.2) (hleft _ hv.2.2)
  · intro v hv
    exact rad_rad_apply hv.1 hA (hmapB _ hv.2.2) (hright _ hv.2.2)
  · intro v hv
    obtain ⟨g, hgS, hg⟩ := hS (‖v‖⁻¹ • v) (by rw [hfs]; exact hv.2.2)
    refine ⟨g, hgS, ?_⟩
    have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv.1
    show ‖v‖ • f.toPartialEquiv (‖v‖⁻¹ • v) = g • v
    rw [hg, so3_smul_real, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]


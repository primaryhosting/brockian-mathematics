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


theorem hausdorff_paradox :
    ∃ D : Set E, D.Countable ∧ D ⊆ sph ∧ IsParadoxical SO3 (sph \ D) := by
  classical
  set psi : FreeGroup Bool →* SO3 := rho with hpsi
  letI : MulAction (FreeGroup Bool) E := MulAction.compHom E psi
  have hsmul : ∀ (w : FreeGroup Bool) (v : E), w • v = toPerm (rho w) v := fun w v => rfl
  refine ⟨badSet, badSet_countable, fun v hv => hv.1, ?_⟩
  have hpar : IsParadoxical (FreeGroup Bool) (sph \ badSet) := by
    refine isParadoxical_of_freeAction (H := FreeGroup Bool) (sph \ badSet) ?_ ?_
      FreeGroupParadox.freeGroup_isParadoxical
    · -- invariance
      rintro w v ⟨hv, hbad⟩
      refine ⟨by rw [hsmul]; exact sph_invariant _ hv, ?_⟩
      rintro ⟨-, u, hu, hufix⟩
      refine hbad ⟨hv, w⁻¹ * u * w, ?_, ?_⟩
      · intro hcon
        apply hu
        have huw : u = w * (w⁻¹ * u * w) * w⁻¹ := by group
        rw [huw, hcon]
        group
      · have h1 : toPerm (rho (w⁻¹ * u * w)) v
            = toPerm (rho w⁻¹) (toPerm (rho u) (toPerm (rho w) v)) := by
          rw [map_mul, map_mul, toPerm_mul, toPerm_mul]
        rw [hsmul] at hufix
        rw [h1, hufix, ← toPerm_mul, ← map_mul, inv_mul_cancel, map_one, toPerm_one]
    · -- freeness
      rintro w v ⟨hv, hbad⟩ hfix
      by_contra hw
      exact hbad ⟨hv, w, hw, by rw [← hsmul]; exact hfix⟩
  exact hpar.of_hom psi (fun h x => rfl)

/-! ## Absorbing the countable set: the whole sphere is paradoxical -/

/-- The north pole of the unit sphere. -/

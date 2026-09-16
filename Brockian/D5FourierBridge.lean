import Mathlib
import Brockian.D5Isotypic
import Brockian.CyclicFourierStructure

/-!
# Connect the existing five-vertex representation to the uniform Fourier lemma

The bridge upgrades the old mode-by-mode projector statements to every vertex
function. It concerns the existing finite D₅ representation only.
-/

namespace Brockian.D5FourierBridge

open Brockian.D5Representation Brockian.D5Isotypic
open Brockian.CyclicFourierStructure

theorem omegaPow_eq_character (a : Fin 5) :
    omegaPow a = ZMod.stdAddChar (a : ZMod 5) := by
  have hgen : ZMod.stdAddChar (1 : ZMod 5) = omega := by
    simpa [omega] using (ZMod.stdAddChar_coe (N := 5) (1 : ℤ))
  have ha : (a : ZMod 5) = a.val • (1 : ZMod 5) := by simp
  rw [ha, AddChar.map_nsmul_eq_pow, hgen]
  rfl

theorem eigenmode_eq_mode (k : Fin 5) : eigenmode k = mode (N := 5) k := by
  ext j
  exact omegaPow_eq_character (k * j)

theorem isotypicProjector_eq_projector (k : Fin 5) (f : VertexSpace) :
    isotypicProjector k f = projector (N := 5) k f := by
  classical
  ext x
  rw [isotypicProjector_apply]
  simp only [omegaPow_eq_character, projector, Pi.smul_apply, coefficient, mode,
    ZMod.dft_apply, smul_eq_mul]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun j => ?_
  simp only [Equiv.subLeft_apply]
  have heq : -( (x - j) * k) + k * x = k * j := by ring
  rw [mul_right_comm, ← AddChar.map_add_eq_mul, heq]

theorem full_projector_resolution (f : VertexSpace) :
    ∑ k : Fin 5, isotypicProjector k f = f := by
  simp_rw [isotypicProjector_eq_projector]
  exact projector_resolution f

theorem full_projector_composition (k l : Fin 5) (f : VertexSpace) :
    isotypicProjector k (isotypicProjector l f) =
      if k = l then isotypicProjector k f else 0 := by
  simp_rw [isotypicProjector_eq_projector]
  exact projector_composition k l f

end Brockian.D5FourierBridge

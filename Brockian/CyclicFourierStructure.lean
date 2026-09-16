import Mathlib

/-!
# A shared Fourier explanation for cycle symmetry and Hückel operators

The character sum is uniform in the cycle length. Fourier inversion gives
projectors on every vertex function, not only on a listed set of modes.
The five- and thirteen-cycle statements are specializations of this interface.
These are finite cycle representations; no action on a modular surface is asserted.
-/

namespace Brockian.CyclicFourierStructure

open Finset

variable {N : ℕ} [NeZero N]

noncomputable def mode (k : ZMod N) : ZMod N → ℂ :=
  fun j => ZMod.stdAddChar (k * j)

def shift (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => f (j + 1)
def shiftInv (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => f (j - 1)
def reflect (f : ZMod N → ℂ) : ZMod N → ℂ := fun j => f (-j)

def huckel (α β : ℂ) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  α • f + β • (shift f + shiftInv f)

noncomputable def coefficient (k : ZMod N) (f : ZMod N → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ZMod.dft f k

noncomputable def projector (k : ZMod N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  coefficient k f • mode k

/-- The single character-orthogonality lemma used at all cycle lengths. -/
theorem character_sum (t : ZMod N) :
    ∑ j : ZMod N, ZMod.stdAddChar (t * j) = if t = 0 then (N : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, sum_const,
      card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

theorem dft_mode (k l : ZMod N) :
    ZMod.dft (mode k) l = if k = l then (N : ℂ) else 0 := by
  classical
  simp only [ZMod.dft_apply, mode, smul_eq_mul, ← AddChar.map_add_eq_mul]
  have hi (j : ZMod N) : -(j * l) + k * j = (k - l) * j := by ring
  simp_rw [hi]
  rw [character_sum]
  simp only [sub_eq_zero]

theorem coefficient_mode (k l : ZMod N) :
    coefficient l (mode k) = if k = l then 1 else 0 := by
  classical
  rw [coefficient, dft_mode]
  split_ifs <;> simp [NeZero.ne (N : ℂ)]

theorem coefficient_smul (k : ZMod N) (c : ℂ) (f : ZMod N → ℂ) :
    coefficient k (c • f) = c * coefficient k f := by
  simp only [coefficient, ZMod.dft_const_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem projector_mode (k l : ZMod N) :
    projector k (mode l) = if k = l then mode l else 0 := by
  classical
  simp only [projector, coefficient_mode]
  by_cases h : k = l
  · subst l; simp
  · simp [h, Ne.symm h]

theorem projector_composition (k l : ZMod N) (f : ZMod N → ℂ) :
    projector k (projector l f) = if k = l then projector k f else 0 := by
  classical
  simp only [projector, coefficient_smul, coefficient_mode]
  by_cases h : k = l
  · subst l; simp
  · simp [h, Ne.symm h]

theorem projector_idempotent (k : ZMod N) (f : ZMod N → ℂ) :
    projector k (projector k f) = projector k f := by
  simpa using projector_composition k k f

/-- Completeness on arbitrary vertex functions follows from Fourier inversion. -/
theorem projector_resolution (f : ZMod N → ℂ) : ∑ k, projector k f = f := by
  classical
  ext j
  have hinv := congrFun (ZMod.dft.symm_apply_apply f) j
  rw [ZMod.invDFT_apply] at hinv
  simp only [sum_apply, projector, Pi.smul_apply, coefficient, mode, smul_eq_mul]
  calc
    ∑ k : ZMod N, ((N : ℂ)⁻¹ * ZMod.dft f k) * ZMod.stdAddChar (k * j)
        = (N : ℂ)⁻¹ * ∑ k : ZMod N, ZMod.stdAddChar (k * j) * ZMod.dft f k := by
            rw [mul_sum]
            apply sum_congr rfl
            intro k _
            ring
    _ = f j := hinv

theorem shift_mode (k : ZMod N) :
    shift (mode k) = ZMod.stdAddChar k • mode k := by
  ext j
  simp only [shift, mode, Pi.smul_apply, smul_eq_mul, mul_add, mul_one,
    AddChar.map_add_eq_mul]
  ring

theorem shiftInv_mode (k : ZMod N) :
    shiftInv (mode k) = ZMod.stdAddChar (-k) • mode k := by
  ext j
  simp only [shiftInv, mode, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg,
    mul_add, mul_neg, mul_one, AddChar.map_add_eq_mul]
  ring

theorem reflect_mode (k : ZMod N) : reflect (mode k) = mode (-k) := by
  ext j
  simp only [reflect, mode, mul_neg, neg_mul]

/-- The dihedral relation holds for every cycle length. -/
theorem reflect_shift_reflect (f : ZMod N → ℂ) :
    reflect (shift (reflect f)) = shiftInv f := by
  ext j
  simp [reflect, shift, shiftInv, sub_eq_add_neg]

theorem huckel_mode (α β : ℂ) (k : ZMod N) :
    huckel α β (mode k) =
      (α + β * (ZMod.stdAddChar k + ZMod.stdAddChar (-k))) • mode k := by
  rw [huckel, shift_mode, shiftInv_mode]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem five_cycle_resolution (f : ZMod 5 → ℂ) : ∑ k, projector k f = f :=
  projector_resolution f

theorem five_cycle_dihedral (f : ZMod 5 → ℂ) :
    reflect (shift (reflect f)) = shiftInv f := reflect_shift_reflect f

theorem thirteen_cycle_huckel (α β : ℂ) (k : ZMod 13) :
    huckel α β (mode k) =
      (α + β * (ZMod.stdAddChar k + ZMod.stdAddChar (-k))) • mode k :=
  huckel_mode α β k

end Brockian.CyclicFourierStructure

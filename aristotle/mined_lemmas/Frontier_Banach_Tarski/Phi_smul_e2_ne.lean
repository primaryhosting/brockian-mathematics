import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem Phi_smul_e2_ne (w : FreeGroup (Fin 2)) (hw : w ≠ 1) : Phi w • e2 ≠ e2 := by
  intro hcon
  set L := w.toWord with hLdef
  have hL : FreeGroup.mk L = w := FreeGroup.mk_toWord
  have hred : FreeGroup.IsReduced L := FreeGroup.isReduced_toWord
  have hne : L ≠ [] := fun h => hw (FreeGroup.toWord_eq_nil_iff.mp h)
  have hmat : ((Phi w : O3) : Matrix (Fin 3) (Fin 3) ℝ) = matWord L := by
    rw [← hL]; exact coe_Phi_mk L
  -- the matrix fixes `(0,1,0)`
  have hfix : matWord L *ᵥ ![0, 1, 0] = ![0, 1, 0] := by
    funext i
    have := congrFun (congrArg (fun (y : E) (i : Fin 3) => y i) hcon) i
    simpa [O3.smul_apply, hmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  -- hence it fixes `(0,√2,0)`
  have hscale : ![0, Real.sqrt 2, 0] = Real.sqrt 2 • ![(0 : ℝ), 1, 0] := by
    funext i; fin_cases i <;> simp
  have hfix2 : matWord L *ᵥ ![0, Real.sqrt 2, 0] = ![0, Real.sqrt 2, 0] := by
    rw [hscale, Matrix.mulVec_smul, hfix]
  rw [matWord_mulVec] at hfix2
  have hcoord := congrFun hfix2 1
  simp only [Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at hcoord
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hq : ((ival L).2.1 : ℝ) = (3 : ℝ) ^ L.length := by
    have h3 : ((3 : ℝ) ^ L.length) ≠ 0 := by positivity
    field_simp at hcoord
    rcases mul_eq_mul_right_iff.mp hcoord with h | h
    · exact h
    · exact absurd h hs2
  have hqz : (ival L).2.1 = 3 ^ L.length := by
    have : ((ival L).2.1 : ℝ) = (((3 ^ L.length : ℤ)) : ℝ) := by push_cast; exact hq
    exact_mod_cast this
  refine ival_mid_not_dvd L.length L rfl hred hne ?_
  rw [hqz]
  exact dvd_pow_self 3 (List.length_eq_zero_iff.not.mpr hne)

/-- All the rotations in the group have determinant one. -/

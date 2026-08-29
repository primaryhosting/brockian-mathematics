import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  rw [Pmat, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  simp only at hab
  have ha : ZMod.val (a : ZMod 16) < 16 := ZMod.val_lt _
  have hb : ZMod.val (b : ZMod 16) < 16 := ZMod.val_lt _
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  have hz : zeta = Complex.exp (2 * Real.pi * Complex.I / ((16 : ℕ) : ℂ)) := by
    norm_num [zeta]
  rw [hz] at hab
  exact ZMod.val_injective 16 (h.pow_inj ha hb hab)


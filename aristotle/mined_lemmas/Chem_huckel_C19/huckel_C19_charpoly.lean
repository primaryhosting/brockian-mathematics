/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/

theorem huckel_C19_charpoly :
    C19adj.charpoly = ∏ k : ZMod 19, (Polynomial.X - Polynomial.C (mu k)) := by
  set FC : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ) := Fm.map Polynomial.C with hFC
  set GC : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ) := Gm.map Polynomial.C with hGC
  have hFG : FC * GC = 1 := by
    rw [hFC, hGC, ← Matrix.map_mul, Fm_mul_Gm, Matrix.map_one] <;> simp
  have hscalar : (Matrix.scalar (ZMod 19)) (Polynomial.X : (Polynomial ℂ))
      = FC * diagonal (fun _ : ZMod 19 => (Polynomial.X : (Polynomial ℂ))) * GC := by
    have hd : (diagonal (fun _ : ZMod 19 => (Polynomial.X : (Polynomial ℂ))))
        = (Polynomial.X : (Polynomial ℂ)) • (1 : Matrix (ZMod 19) (ZMod 19) (Polynomial ℂ)) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hFG]
    ext a b
    by_cases h : a = b <;> simp [h]
  have hmapA : C19adj.map Polynomial.C
      = FC * diagonal (fun k : ZMod 19 => Polynomial.C (mu k)) * GC := by
    rw [hFC, hGC, C19adj_eq, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (by simp)]
  have hchar : charmatrix C19adj
      = FC * diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k)) * GC := by
    rw [charmatrix, RingHom.mapMatrix_apply, hscalar, hmapA, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_sub]
  have hdet : FC.det * GC.det = 1 := by rw [← Matrix.det_mul, hFG, Matrix.det_one]
  have e1 : C19adj.charpoly
      = FC.det * (diagonal (fun k : ZMod 19 => Polynomial.X - Polynomial.C (mu k))).det * GC.det := by
    rw [Matrix.charpoly, hchar, Matrix.det_mul, Matrix.det_mul]
  rw [e1, det_diagonal_charpoly_factors]
  exact mul_mid_mul_of_mul_eq_one hdet

end Chem

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


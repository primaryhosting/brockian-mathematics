import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma eigenvalue_eq (μ : ℝ) (x : Fin (m + 3) → ℝ) (hx : x ≠ 0)
    (heig : (cycleGraph (m + 3)).lapMatrix ℝ *ᵥ x = μ • x) :
    ∃ k : Fin (m + 3), μ = cycEigen m k := by
  classical
  set M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
    (cycleGraph (m + 3)).lapMatrix ℝ - Matrix.diagonal (fun _ => μ) with hM
  have hMx : M *ᵥ x = 0 := by
    funext i
    have hi := congrFun heig i
    simp [hM, Matrix.sub_mulVec, hi]
  have hdet : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hMx⟩
  set Mc : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ :=
    (cycleGraph (m + 3)).lapMatrix ℂ - Matrix.diagonal (fun _ => (μ : ℂ)) with hMc
  have hmap : Mc = M.map Complex.ofRealHom := by
    have hentry : ∀ i j, (((cycleGraph (m + 3)).lapMatrix ℝ i j : ℝ) : ℂ)
        = (cycleGraph (m + 3)).lapMatrix ℂ i j := by
      intro i j
      have h := congrFun (congrFun (lapMatrix_map_ofReal (m := m)) i) j
      simpa [Matrix.map_apply] using h
    ext i j
    simp [hMc, hM, Matrix.map_apply, Matrix.sub_apply, Matrix.diagonal_apply, ← hentry]
    split_ifs <;> simp
  have hdetC : Mc.det = 0 := by
    have hd := RingHom.map_det Complex.ofRealHom M
    simp [RingHom.mapMatrix_apply] at hd
    rw [hmap, ← hd, hdet]
    simp
  have hprod : Mc * fourierMat m
      = fourierMat m * Matrix.diagonal (fun k => ((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) := by
    rw [hMc, Matrix.sub_mul, lapMatrix_mul_fourierMat]
    ext j k
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply]
    ring
  have hdet2 : Mc.det * (fourierMat m).det
      = (fourierMat m).det * ∏ k : Fin (m + 3), (((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) := by
    rw [← Matrix.det_mul, hprod, Matrix.det_mul, Matrix.det_diagonal]
  rw [hdetC, zero_mul] at hdet2
  have hz : ∏ k : Fin (m + 3), (((cycEigen m k : ℝ) : ℂ) - (μ : ℂ)) = 0 := by
    rcases mul_eq_zero.mp hdet2.symm with h | h
    · exact absurd h det_fourierMat_ne_zero
    · exact h
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
  refine ⟨k, ?_⟩
  have hkc : ((cycEigen m k : ℝ) : ℂ) = (μ : ℂ) := by linear_combination hk
  exact_mod_cast hkc.symm


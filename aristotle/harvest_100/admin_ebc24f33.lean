/-
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
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

set_option grind.warning false

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/
def ksVec : Fin 18 → EuclideanSpace ℝ (Fin 4) :=
  ![ !₂[0, 0, 0, 1],      -- 0
     !₂[0, 0, 1, 0],      -- 1
     !₂[1, 1, 0, 0],      -- 2
     !₂[1, -1, 0, 0],     -- 3
     !₂[0, 1, 0, 0],      -- 4
     !₂[1, 0, 1, 0],      -- 5
     !₂[1, 0, -1, 0],     -- 6
     !₂[1, -1, 1, -1],    -- 7
     !₂[1, -1, -1, 1],    -- 8
     !₂[0, 0, 1, 1],      -- 9
     !₂[1, 1, 1, 1],      -- 10
     !₂[0, 1, 0, -1],     -- 11
     !₂[1, 0, 0, 1],      -- 12
     !₂[1, 0, 0, -1],     -- 13
     !₂[0, 1, -1, 0],     -- 14
     !₂[1, 1, -1, 1],     -- 15
     !₂[1, 1, 1, -1],     -- 16
     !₂[-1, 1, 1, 1] ]    -- 17

/-- The nine orthogonal bases ("contexts"), given as quadruples of indices into `Phys.ksVec`. -/
def ksCtx : Fin 9 → Fin 4 → Fin 18 :=
  ![ ![0, 1, 2, 3],
     ![0, 4, 5, 6],
     ![7, 8, 2, 9],
     ![7, 10, 6, 11],
     ![1, 4, 12, 13],
     ![8, 10, 13, 14],
     ![15, 16, 3, 9],
     ![15, 17, 5, 11],
     ![16, 17, 12, 14] ]

/-- The 18 vectors are pairwise distinct. -/
theorem ksVec_injective : Function.Injective ksVec := by
  intro i j hij
  by_contra hne
  fin_cases i <;> fin_cases j <;>
    simp_all [ksVec, funext_iff, Fin.forall_fin_succ] <;>
    norm_num at hij

/-- None of the 18 vectors is zero. -/
theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  fin_cases i <;>
    simp [ksVec, funext_iff, Fin.forall_fin_succ]

/-- Within each of the nine contexts, the four vectors are pairwise orthogonal;
hence each context is an orthogonal basis of `ℝ⁴`. -/
theorem ksCtx_orthogonal (c : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    inner ℝ (ksVec (ksCtx c i)) (ksVec (ksCtx c j)) = (0 : ℝ) := by
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp_all [ksCtx, ksVec, PiLp.inner_apply, Fin.sum_univ_four]

/-- Each context consists of four linearly independent vectors. -/
theorem ksCtx_linearIndependent (c : Fin 9) :
    LinearIndependent ℝ (fun i : Fin 4 => ksVec (ksCtx c i)) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => ksVec_ne_zero (ksCtx c i))
    (fun i j hij => ksCtx_orthogonal c i j hij)

/-- Each context is in fact an orthogonal basis of `ℝ⁴`: its four vectors span the space. -/
theorem ksCtx_span_eq_top (c : Fin 9) :
    Submodule.span ℝ (Set.range fun i : Fin 4 => ksVec (ksCtx c i)) = ⊤ := by
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) := by simp
  have hb := (basisOfLinearIndependentOfCardEqFinrank (ksCtx_linearIndependent c) hcard).span_eq
  rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at hb

/-- **Kochen–Specker (18-vector version).**  There is no `{0,1}`-coloring of `ℝ⁴`
assigning to each of the nine orthogonal bases listed in `Phys.ksCtx` exactly one
vector of color `1`. -/
theorem kochen_specker_18 :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 4) → ℕ,
      (∀ v, f v = 0 ∨ f v = 1) ∧
      ∀ c : Fin 9, ∑ i : Fin 4, f (ksVec (ksCtx c i)) = 1 := by
  rintro ⟨f, -, hf⟩
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  have h5 := hf 5
  have h6 := hf 6
  have h7 := hf 7
  have h8 := hf 8
  simp only [ksCtx, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

end Phys


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

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/
def ksVec : Fin 18 → Fin 4 → ℝ :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![-1, 1, 1, 1],
    ![0, 1, -1, 0]]

/-- The 9 orthogonal bases of the Kochen–Specker set, given as index quadruples. -/
def ksBasis : Fin 9 → Fin 4 → Fin 18 :=
  ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 2, 9],
    ![7, 10, 6, 11],
    ![1, 4, 12, 13],
    ![8, 10, 13, 17],
    ![14, 15, 3, 9],
    ![14, 16, 5, 11],
    ![15, 16, 12, 17]]

/-- Every vector of the set is nonzero. -/
theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  fin_cases i <;> simp [ksVec] at h0 h1 h2 h3

/-- The same 18 vectors, with integer entries; used to check distinctness by computation. -/
def ksVecInt : Fin 18 → Fin 4 → ℤ :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![1, 1, 0, 0],
    ![1, -1, 0, 0],
    ![0, 1, 0, 0],
    ![1, 0, 1, 0],
    ![1, 0, -1, 0],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![0, 0, 1, 1],
    ![1, 1, 1, 1],
    ![0, 1, 0, -1],
    ![1, 0, 0, 1],
    ![1, 0, 0, -1],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![-1, 1, 1, 1],
    ![0, 1, -1, 0]]

theorem ksVec_eq_int (i : Fin 18) (k : Fin 4) : ksVec i k = (ksVecInt i k : ℝ) := by
  fin_cases i <;> fin_cases k <;> norm_num [ksVec, ksVecInt]

/-- The 18 vectors of the set are pairwise distinct. -/
theorem ksVec_injective : Function.Injective ksVec := by
  have hZ : Function.Injective ksVecInt := by decide
  intro i j h
  refine hZ (funext fun k => ?_)
  have hk := congrFun h k
  rw [ksVec_eq_int, ksVec_eq_int] at hk
  exact_mod_cast hk

/-- The four vectors of each of the nine bases are pairwise orthogonal. -/
theorem ksBasis_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    ∑ k : Fin 4, ksVec (ksBasis b i) k * ksVec (ksBasis b j) k = 0 := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp_all [ksVec, ksBasis, Fin.sum_univ_four]

/-- **Kochen–Specker (18 vectors, 9 bases).**
There is no `{0,1}`-coloring of the 18 explicit vectors in `ℝ⁴` assigning to exactly one
vector of each of the nine orthogonal bases the value `1`. -/
theorem kochen_specker_18 :
    ¬ ∃ c : (Fin 4 → ℝ) → Bool,
        ∀ b : Fin 9, (∑ i : Fin 4, if c (ksVec (ksBasis b i)) then 1 else 0) = 1 := by
  rintro ⟨c, hc⟩
  set g : Fin 18 → ℕ := fun k => if c (ksVec k) then 1 else 0
  have key : ∀ b : Fin 9, ∑ i : Fin 4, g (ksBasis b i) = 1 := hc
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  have h7 := key 7
  have h8 := key 8
  simp only [ksBasis, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

end Phys


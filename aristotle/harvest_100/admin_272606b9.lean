import Mathlib

/-!
# Kochen Specker 18
Category: Frontier Phys
Target: Phys.kochen_specker_18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Phys

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker set in `ℝ⁴`. -/
def ksVec : Fin 18 → (Fin 4 → ℝ) :=
  ![![0, 0, 0, 1],      -- 0
    ![0, 0, 1, 0],      -- 1
    ![1, 1, 0, 0],      -- 2
    ![1, -1, 0, 0],     -- 3
    ![0, 1, 0, 0],      -- 4
    ![1, 0, 1, 0],      -- 5
    ![1, 0, -1, 0],     -- 6
    ![1, -1, 1, -1],    -- 7
    ![1, -1, -1, 1],    -- 8
    ![0, 0, 1, 1],      -- 9
    ![1, 1, 1, 1],      -- 10
    ![0, 1, 0, -1],     -- 11
    ![1, 0, 0, 1],      -- 12
    ![1, 0, 0, -1],     -- 13
    ![0, 1, -1, 0],     -- 14
    ![1, 1, -1, 1],     -- 15
    ![1, 1, 1, -1],     -- 16
    ![-1, 1, 1, 1]]     -- 17

/-- The nine orthogonal bases of the Kochen–Specker set, given as quadruples of indices
into `ksVec`.  Each of the 18 vectors occurs in exactly two of these bases. -/
def ksBasis : Fin 9 → (Fin 4 → Fin 18) :=
  ![![0, 1, 2, 3],
    ![0, 4, 5, 6],
    ![7, 8, 2, 9],
    ![7, 10, 6, 11],
    ![1, 4, 12, 13],
    ![8, 10, 13, 14],
    ![15, 16, 3, 9],
    ![15, 17, 5, 11],
    ![16, 17, 12, 14]]

/-- The standard inner product on `Fin 4 → ℝ`. -/
def ksDot (v w : Fin 4 → ℝ) : ℝ := ∑ k, v k * w k

/-- Every one of the 18 vectors is nonzero. -/
theorem ksVec_ne_zero (i : Fin 18) : ksVec i ≠ 0 := by
  intro h
  have h3 := congrFun h 3
  have h2 := congrFun h 2
  have h1 := congrFun h 1
  have h0 := congrFun h 0
  fin_cases i <;> simp [ksVec] at h0 h1 h2 h3

/-- Within each of the nine listed quadruples, the four vectors are pairwise orthogonal;
hence each quadruple really is an orthogonal basis of `ℝ⁴`. -/
theorem ksBasis_orthogonal (b : Fin 9) (i j : Fin 4) (hij : i ≠ j) :
    ksDot (ksVec (ksBasis b i)) (ksVec (ksBasis b j)) = 0 := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [ksDot, ksVec, ksBasis, Fin.sum_univ_four] at hij ⊢

/-- The four indices in each quadruple are distinct. -/
theorem ksBasis_injective (b : Fin 9) (i j : Fin 4) (h : ksBasis b i = ksBasis b j) : i = j := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;> simp_all [ksBasis]

/-- **Kochen–Specker theorem (18-vector version).**
The explicit 18 vectors `ksVec` in `ℝ⁴` form nine orthogonal bases (the four vectors of each
quadruple `ksBasis b` are pairwise orthogonal and nonzero), yet there is no `{0,1}`-coloring
of the 18 vectors assigning the value `1` to exactly one vector of each basis. -/
theorem kochen_specker_18 :
    (∀ i : Fin 18, ksVec i ≠ 0) ∧
    (∀ b : Fin 9, ∀ i j : Fin 4, ksBasis b i = ksBasis b j → i = j) ∧
    (∀ b : Fin 9, ∀ i j : Fin 4, i ≠ j →
      ksDot (ksVec (ksBasis b i)) (ksVec (ksBasis b j)) = 0) ∧
    ¬ ∃ f : Fin 18 → ℕ,
        (∀ i, f i = 0 ∨ f i = 1) ∧
        (∀ b : Fin 9, f (ksBasis b 0) + f (ksBasis b 1) + f (ksBasis b 2) + f (ksBasis b 3) = 1) := by
  refine ⟨ksVec_ne_zero, ksBasis_injective, ksBasis_orthogonal, ?_⟩
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
  simp only [ksBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

end Phys

#print axioms Phys.kochen_specker_18


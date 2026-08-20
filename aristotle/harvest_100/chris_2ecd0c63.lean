import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede all other commands, including module
docstrings, so the required header comment appears immediately after the import.)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Polynomial

/-- The adjacency matrix of the cycle graph `C₉`, with vertices indexed by `ZMod 9`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `9`. -/
noncomputable def C9adj : Matrix (ZMod 9) (ZMod 9) ℝ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then (1 : ℝ) else 0

/-- The `k`-th Hückel eigenvalue of `C₉` (in units of the resonance integral `β`,
with `α = 0`): `2 cos (2πk/9)`. -/
noncomputable def huckelValue (k : ZMod 9) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 9)

/-- The standard additive character of `ZMod 9` valued in `ℂ`. -/
noncomputable def psi : AddChar (ZMod 9) ℂ := ZMod.stdAddChar

/-- The DFT matrix. -/
noncomputable def Pmat : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun j k => psi (j * k)

/-- The inverse DFT matrix. -/
noncomputable def Qmat : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun k j => psi (-(k * j)) / 9

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dmat : Matrix (ZMod 9) (ZMod 9) ℂ :=
  Matrix.diagonal fun k => (huckelValue k : ℂ)

lemma psi_apply (j : ZMod 9) : psi j = Complex.exp (2 * Real.pi * Complex.I * j.val / 9) := by
  simp [psi, ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- Orthogonality of the character sums. -/
lemma psi_sum (b : ZMod 9) : ∑ x : ZMod 9, psi (x * b) = if b = 0 then 9 else 0 := by
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod 9) ℂ)) b
    (ZMod.isPrimitive_stdAddChar 9)
  rw [show (psi : AddChar (ZMod 9) ℂ) = ZMod.stdAddChar from rfl, h]
  simp

lemma psi_eq_exp (k : ZMod 9) :
    psi k = Complex.exp (((2 * Real.pi * k.val / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [psi_apply]
  congr 1
  push_cast
  ring

lemma exp_add_exp_neg (t : ℝ) :
    Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * (Real.cos t : ℂ) := by
  have h2 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [Complex.exp_mul_I, h2, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- `ψ k + ψ (-k) = 2 cos (2πk/9)`. -/
lemma psi_add_psi_neg (k : ZMod 9) : psi k + psi (-k) = (huckelValue k : ℂ) := by
  have hneg : psi (-k) = (psi k)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [hneg, psi_eq_exp, ← Complex.exp_neg, exp_add_exp_neg, huckelValue]
  push_cast
  ring

lemma Pmat_mul_Qmat : Pmat * Qmat = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Pmat, Qmat, Matrix.of_apply]
  have h : ∀ k : ZMod 9, psi (j * k) * (psi (-(k * l)) / 9) = psi (k * (j - l)) / 9 := by
    intro k
    rw [mul_div_assoc']
    congr 1
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, psi_sum, Matrix.one_apply]
  rcases eq_or_ne j l with hjl | hjl
  · simp [hjl]
  · rw [if_neg (sub_ne_zero.mpr hjl), if_neg hjl]
    simp

lemma Qmat_mul_Pmat : Qmat * Pmat = 1 := by
  ext j l
  simp only [Matrix.mul_apply, Pmat, Qmat, Matrix.of_apply]
  have h : ∀ k : ZMod 9, psi (-(j * k)) / 9 * psi (k * l) = psi (k * (l - j)) / 9 := by
    intro k
    rw [div_mul_eq_mul_div]
    congr 1
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, psi_sum, Matrix.one_apply]
  rcases eq_or_ne j l with hjl | hjl
  · simp [hjl]
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm hjl)), if_neg hjl]
    simp

/-- The complexified adjacency matrix. -/
noncomputable def C9adjC : Matrix (ZMod 9) (ZMod 9) ℂ := C9adj.map (Complex.ofReal)

/-- Each row of the adjacency matrix has exactly two nonzero entries, at the two neighbours. -/
lemma C9adj_entry (i j : ZMod 9) :
    (C9adj i j : ℂ) = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have e1 : (i - j = 1) ↔ (j = i - 1) := by
    constructor <;> intro h <;> linear_combination -h
  have e2 : (j - i = 1) ↔ (j = i + 1) := by
    constructor <;> intro h <;> linear_combination h
  have hne : (i - 1 : ZMod 9) ≠ i + 1 := by
    intro h
    exact absurd (show (2 : ZMod 9) = 0 by linear_combination -h) (by decide)
  simp only [C9adj, Matrix.of_apply, e1, e2]
  by_cases h1 : j = i - 1
  · simp [h1, hne]
  · by_cases h2 : j = i + 1
    · simp [h2, Ne.symm hne]
    · simp [h1, h2]

lemma C9adjC_mul_Pmat : C9adjC * Pmat = Pmat * Dmat := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [Dmat]
  rw [Matrix.mul_diagonal]
  have hentry : ∀ j : ZMod 9, C9adjC i j * Pmat j k
      = (if j = i - 1 then psi (j * k) else 0) + (if j = i + 1 then psi (j * k) else 0) := by
    intro j
    simp only [C9adjC, Matrix.map_apply, Pmat, Matrix.of_apply, C9adj_entry i j]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hentry j, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  simp only [Pmat, Matrix.of_apply]
  have h1 : psi ((i - 1) * k) = psi (i * k) * psi (-k) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have h2 : psi ((i + 1) * k) = psi (i * k) * psi k := by
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [h1, h2, ← mul_add, add_comm (psi (-k)) (psi k), psi_add_psi_neg]

/-- The unit given by the DFT matrix. -/
noncomputable def Punit : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ :=
  ⟨Pmat, Qmat, Pmat_mul_Qmat, Qmat_mul_Pmat⟩

lemma C9adjC_eq :
    C9adjC = (Punit : Matrix (ZMod 9) (ZMod 9) ℂ) * Dmat *
      ((Punit⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) := by
  have hP : ((Punit : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) = Pmat := rfl
  have hQ : ((Punit⁻¹ : (Matrix (ZMod 9) (ZMod 9) ℂ)ˣ) : Matrix (ZMod 9) (ZMod 9) ℂ) = Qmat := rfl
  rw [hP, hQ, ← C9adjC_mul_Pmat, Matrix.mul_assoc, Pmat_mul_Qmat, Matrix.mul_one]

lemma charpoly_C9adjC :
    C9adjC.charpoly = ∏ k : ZMod 9, (X - C ((huckelValue k : ℂ))) := by
  rw [C9adjC_eq, Matrix.charpoly_units_conj, Dmat, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₉`**: the characteristic polynomial of the adjacency matrix of the
cycle graph `C₉` factors as `∏_{k=0}^{8} (X - 2 cos (2πk/9))`, i.e. the adjacency
(Hückel) eigenvalues of `C₉` are exactly `2 cos (2πk/9)` for `k = 0, …, 8`. -/
theorem huckel_C9 :
    C9adj.charpoly = ∏ k : ZMod 9, (X - C (2 * Real.cos (2 * Real.pi * k.val / 9))) := by
  have hmap : (C9adj.map (Complex.ofRealHom : ℝ →+* ℂ)).charpoly
      = Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ) C9adj.charpoly :=
    Matrix.charpoly_map _ _
  have hC : C9adj.map (Complex.ofRealHom : ℝ →+* ℂ) = C9adjC := rfl
  rw [hC, charpoly_C9adjC] at hmap
  have hprod : ∏ k : ZMod 9, (X - C ((huckelValue k : ℂ)))
      = Polynomial.map (Complex.ofRealHom : ℝ →+* ℂ)
          (∏ k : ZMod 9, (X - C (2 * Real.cos (2 * Real.pi * k.val / 9)))) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [huckelValue]
  rw [hprod] at hmap
  exact (Polynomial.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
    hmap.symm)

/-- The multiset of roots of the characteristic polynomial of `C₉` is exactly
`{2 cos (2πk/9) : k = 0, …, 8}`. -/
theorem huckel_C9_roots :
    C9adj.charpoly.roots =
      (Finset.univ : Finset (ZMod 9)).val.map fun k => 2 * Real.cos (2 * Real.pi * k.val / 9) := by
  rw [huckel_C9]
  rw [Finset.prod_eq_multiset_prod]
  rw [show ((Finset.univ : Finset (ZMod 9)).val.map
        fun k => X - C (2 * Real.cos (2 * Real.pi * k.val / 9)))
      = (((Finset.univ : Finset (ZMod 9)).val.map
        fun k => 2 * Real.cos (2 * Real.pi * k.val / 9)).map fun a => X - C a) by
    rw [Multiset.map_map]; rfl]
  exact Polynomial.roots_multiset_prod_X_sub_C _

end Chem


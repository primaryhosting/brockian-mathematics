/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring; the header above is
-- repeated below as the module docstring.)
import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard additive character of `ZMod 11`, `x ↦ exp (2πI x / 11)`. -/
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod 11) ℂ)

/-- The Hückel eigenvalues of the cycle `C₁₁`. -/
noncomputable def lam (k : ZMod 11) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 11)

/-- The adjacency matrix of `C₁₁`, written over `ZMod 11`. -/
noncomputable def Adj11 : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def Fmat : Matrix (ZMod 11) (ZMod 11) ℂ := Matrix.of fun j k => χ (j * k)

/-- The inverse discrete Fourier matrix. -/
noncomputable def Gmat : Matrix (ZMod 11) (ZMod 11) ℂ :=
  Matrix.of fun k j => (11 : ℂ)⁻¹ * χ (-(k * j))

/-- Character orthogonality on `ZMod 11`. -/
lemma sum_char (t : ZMod 11) : ∑ i : ZMod 11, χ (t * i) = if t = 0 then 11 else 0 := by
  split_ifs with h
  · simp
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 h)

lemma Gmat_mul_Fmat : Gmat * Fmat = 1 := by
  ext k k'
  have : ∀ j : ZMod 11, Gmat k j * Fmat j k' = (11 : ℂ)⁻¹ * χ ((k' - k) * j) := by
    intro j
    simp only [Gmat, Fmat, Matrix.of_apply]
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    ring_nf
  rw [Matrix.mul_apply]
  simp only [this, ← Finset.mul_sum, sum_char]
  by_cases h : k = k'
  · subst h; simp
  · rw [if_neg (by simpa [sub_eq_zero] using fun hh => h hh.symm),
      Matrix.one_apply_ne h]
    simp

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := mul_eq_one_comm.mpr Gmat_mul_Fmat

/-- `χ k + χ (-k) = 2 cos (2πk/11)`. -/
lemma char_add_char_neg (k : ZMod 11) : χ k + χ (-k) = lam k := by
  have h1 : χ k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    push_cast
    ring_nf
  have h2 : χ (-k) = Complex.exp (-((2 * Real.pi * k.val / 11 : ℝ) * I)) := by
    have hmul : χ k * χ (-k) = 1 := by
      rw [← AddChar.map_add_eq_mul]; simp
    have hne : χ k ≠ 0 := by
      rw [h1]; exact Complex.exp_ne_zero _
    have : χ (-k) = (χ k)⁻¹ := by
      field_simp at hmul ⊢
      linear_combination hmul
    rw [this, h1, ← Complex.exp_neg]
  rw [h1, h2, lam, Complex.ofReal_cos, Complex.cos]
  ring_nf

lemma Adj11_mul_Fmat : Adj11 * Fmat = Fmat * Matrix.diagonal lam := by
  ext i k
  have hne : (i + 1 : ZMod 11) ≠ i - 1 := by decide +kernel
  have hsplit : ∀ j : ZMod 11, Adj11 i j * Fmat j k
      = (if j = i + 1 then χ (j * k) else 0) + (if j = i - 1 then χ (j * k) else 0) := by
    intro j
    simp only [Adj11, Fmat, Matrix.of_apply]
    by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
      simp_all
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1),
    Finset.sum_ite_eq' Finset.univ (i - 1), Finset.mem_univ, if_true]
  have hd : ∀ j : ZMod 11, Fmat i j * Matrix.diagonal lam j k
      = if j = k then χ (i * k) * lam k else 0 := by
    intro j
    by_cases h : j = k
    · subst h; simp [Fmat, Matrix.diagonal]
    · simp [Matrix.diagonal, h]
  rw [Finset.sum_congr rfl (fun j _ => hd j)]
  rw [Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
  have e1 : ((i + 1 : ZMod 11) * k) = i * k + k := by ring
  have e2 : ((i - 1 : ZMod 11) * k) = i * k + (-k) := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add, char_add_char_neg]

/-- Eigenvalue characterisation for the `ZMod 11` version of the adjacency matrix. -/
theorem huckel_C11_zmod (μ : ℂ) :
    (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ Adj11.mulVec v = μ • v) ↔
      ∃ k : ZMod 11, μ = 2 * Real.cos (2 * Real.pi * k.val / 11) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    set w := Gmat.mulVec v with hw
    have hFw : Fmat.mulVec w = v := by
      rw [hw, ← Matrix.mulVec_mulVec, Fmat_mul_Gmat, Matrix.one_mulVec]
    have hwne : w ≠ 0 := by
      intro h
      apply hv
      rw [← hFw, h, Matrix.mulVec_zero]
    have hDw : (Matrix.diagonal lam).mulVec w = μ • w := by
      have hGA : Gmat * Adj11 = Matrix.diagonal lam * Gmat := by
        calc Gmat * Adj11 = Gmat * Adj11 * (Fmat * Gmat) := by rw [Fmat_mul_Gmat, mul_one]
        _ = Gmat * (Adj11 * Fmat) * Gmat := by simp [mul_assoc]
        _ = Gmat * Fmat * (Matrix.diagonal lam * Gmat) := by
              rw [Adj11_mul_Fmat]; simp [mul_assoc]
        _ = Matrix.diagonal lam * Gmat := by rw [Gmat_mul_Fmat, one_mul]
      calc (Matrix.diagonal lam).mulVec w
          = (Matrix.diagonal lam * Gmat).mulVec v := by rw [hw, Matrix.mulVec_mulVec]
        _ = (Gmat * Adj11).mulVec v := by rw [hGA]
        _ = Gmat.mulVec (Adj11.mulVec v) := by rw [Matrix.mulVec_mulVec]
        _ = Gmat.mulVec (μ • v) := by rw [hAv]
        _ = μ • w := by rw [hw, Matrix.mulVec_smul]
    obtain ⟨k, hk⟩ : ∃ k : ZMod 11, w k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hwne (funext h)
    refine ⟨k, ?_⟩
    have := congrFun hDw k
    rw [Matrix.mulVec_diagonal] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_right_cancel₀ hk this
    rw [← this, lam]
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => Fmat j k, ?_, ?_⟩
    · intro h
      have h0 : Fmat 0 k = 0 := congrFun h 0
      simp [Fmat] at h0
    · funext i
      have := congrFun (congrFun Adj11_mul_Fmat i) k
      rw [Matrix.mul_apply, Matrix.mul_apply] at this
      have hd : ∑ j : ZMod 11, Fmat i j * Matrix.diagonal lam j k = Fmat i k * lam k := by
        rw [Finset.sum_eq_single k]
        · simp [Matrix.diagonal]
        · intro b _ hb; simp [Matrix.diagonal, hb]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [hd] at this
      simpa [Matrix.mulVec, Matrix.dotProduct, lam, mul_comm] using this

/-- **Hückel theory for the cycle `C₁₁`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` (i.e. there is a nonzero vector `v` with `A v = μ v`)
if and only if `μ = 2 cos (2πk/11)` for some `k ∈ {0, 1, …, 10}`. -/
theorem huckel_C11 (μ : ℂ) :
    (∃ v : Fin 11 → ℂ, v ≠ 0 ∧
        ((SimpleGraph.cycleGraph 11).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 11, μ = 2 * Real.cos (2 * Real.pi * k.val / 11) := by
  have hA : ((SimpleGraph.cycleGraph 11).adjMatrix ℂ) = Adj11 := by
    have hadj : ∀ i j : Fin 11,
        ((SimpleGraph.cycleGraph 11).Adj i j ↔ (j = i + 1 ∨ j = i - 1)) := by decide +kernel
    ext i j
    simp only [SimpleGraph.adjMatrix_apply, Adj11, Matrix.of_apply]
    exact if_congr (hadj i j) rfl rfl
  rw [hA]
  exact huckel_C11_zmod μ

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


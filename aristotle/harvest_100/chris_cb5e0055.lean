import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/
def C18adj : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- `C18adj` is the adjacency matrix of Mathlib's cycle graph on `Fin 18`
(note that `ZMod 18` and `Fin 18` are the same type). -/
lemma C18adj_eq_adjMatrix : C18adj = (SimpleGraph.cycleGraph 18).adjMatrix ℂ := by
  have key : ∀ i j : ZMod 18,
      ((j = i + 1 ∨ j = i - 1) ↔ (SimpleGraph.cycleGraph 18).Adj i j) := by decide
  ext i j
  simp only [C18adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  exact if_congr (key i j) rfl rfl

/-- The standard additive character `m ↦ exp (2πI m / 18)` on `ZMod 18`. -/
noncomputable def w (m : ZMod 18) : ℂ := ZMod.stdAddChar m

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def Fmat : Matrix (ZMod 18) (ZMod 18) ℂ := Matrix.of fun j k => w (j * k)

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def Gmat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun k j => (18 : ℂ)⁻¹ * w (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/18)`. -/
noncomputable def Dmat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  diagonal fun k : ZMod 18 => ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)

lemma w_add (a b : ZMod 18) : w (a + b) = w a * w b := by
  simp [w, AddChar.map_add_eq_mul]

lemma w_sum (b : ZMod 18) :
    ∑ x : ZMod 18, w (x * b) = if b = 0 then (18 : ℂ) else 0 := by
  have := AddChar.sum_mulShift (R := ZMod 18) (R' := ℂ) b (ZMod.isPrimitive_stdAddChar 18)
  simpa [w] using this

lemma w_val (k : ZMod 18) : w k = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / 18) := by
  have hk : ((k.val : ℤ) : ZMod 18) = k := by simp
  calc w k = ZMod.stdAddChar (((k.val : ℤ) : ZMod 18)) := by rw [hk]; rfl
    _ = Complex.exp (2 * Real.pi * I * ((k.val : ℤ) : ℂ) / 18) := ZMod.stdAddChar_coe _
    _ = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / 18) := by push_cast; ring_nf

lemma w_neg (k : ZMod 18) : w (-k) = Complex.exp (-(2 * Real.pi * I * (k.val : ℂ) / 18)) := by
  have hk : ((-(k.val : ℤ) : ℤ) : ZMod 18) = -k := by push_cast; simp
  calc w (-k) = ZMod.stdAddChar (((-(k.val : ℤ) : ℤ) : ZMod 18)) := by rw [hk]; rfl
    _ = Complex.exp (2 * Real.pi * I * ((-(k.val : ℤ) : ℤ) : ℂ) / 18) := ZMod.stdAddChar_coe _
    _ = Complex.exp (-(2 * Real.pi * I * (k.val : ℂ) / 18)) := by push_cast; ring_nf

/-- `w k + w (-k) = 2 cos (2πk/18)`. -/
lemma w_add_neg (k : ZMod 18) :
    w k + w (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
  rw [w_val, w_neg]
  push_cast
  rw [Complex.cos]
  have h : (2 : ℂ) * (Real.pi : ℂ) * I * (k.val : ℂ) / 18
      = (2 * (Real.pi : ℂ) * (k.val : ℂ) / 18) * I := by ring
  rw [h]
  ring_nf

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext i l
  simp only [Matrix.mul_apply, Fmat, Gmat, Matrix.of_apply]
  have hterm : ∀ k : ZMod 18,
      w (i * k) * ((18 : ℂ)⁻¹ * w (-(k * l))) = (18 : ℂ)⁻¹ * w (k * (i - l)) := by
    intro k
    rw [show k * (i - l) = i * k + -(k * l) by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, w_sum]
  rw [Matrix.one_apply]
  by_cases h : i = l
  · simp [h]
  · have : i - l ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

lemma Gmat_mul_Fmat : Gmat * Fmat = 1 := by
  ext i l
  simp only [Matrix.mul_apply, Fmat, Gmat, Matrix.of_apply]
  have hterm : ∀ k : ZMod 18,
      (18 : ℂ)⁻¹ * w (-(i * k)) * w (k * l) = (18 : ℂ)⁻¹ * w (k * (l - i)) := by
    intro k
    rw [show k * (l - i) = -(i * k) + k * l by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum, w_sum]
  rw [Matrix.one_apply]
  by_cases h : i = l
  · simp [h]
  · have : l - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm h)
    simp [this, h]

lemma C18adj_mul_Fmat : C18adj * Fmat = Fmat * Dmat := by
  ext j k
  have hne : (j + 1 : ZMod 18) ≠ j - 1 := by
    intro h
    have : (2 : ZMod 18) = 0 := by linear_combination h
    exact absurd this (by decide)
  have hsplit : ∀ i : ZMod 18,
      C18adj j i * Fmat i k
        = (if i = j + 1 then Fmat i k else 0) + (if i = j - 1 then Fmat i k else 0) := by
    intro i
    simp only [C18adj, Matrix.of_apply]
    by_cases h1 : i = j + 1
    · subst h1; simp [hne]
    · by_cases h2 : i = j - 1
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (j + 1) (fun i => Fmat i k),
    Finset.sum_ite_eq' Finset.univ (j - 1) (fun i => Fmat i k)]
  simp only [Finset.mem_univ, if_true]
  rw [Dmat, Matrix.mul_diagonal]
  simp only [Fmat, Matrix.of_apply]
  rw [← w_add_neg k, show (j + 1) * k = j * k + k by ring,
    show (j - 1) * k = j * k + -k by ring, w_add, w_add]
  ring

/-- The Hückel molecular orbitals: for each `k`, the vector `j ↦ exp (2πI jk/18)` is a nonzero
eigenvector of the adjacency matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
theorem C18adj_mulVec_eq (k : ZMod 18) :
    C18adj *ᵥ (fun j => w (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) • (fun j => w (j * k))
      ∧ (fun j : ZMod 18 => w (j * k)) ≠ 0 := by
  constructor
  · funext j
    have h := congrFun (congrFun C18adj_mul_Fmat j) k
    rw [Dmat, Matrix.mul_diagonal] at h
    simp only [Matrix.mul_apply, Fmat, Matrix.of_apply] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  · intro h
    have h0 := congrFun h 0
    simp [w] at h0

/-- The adjacency eigenvalues of the cycle graph `C₁₈` are exactly the numbers
`2 cos (2πk/18)`, `k = 0, …, 17`. -/
theorem huckel_C18 :
    spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 18, μ = ((2 * Real.cos (2 * Real.pi * k / 18) : ℝ) : ℂ)} := by
  rw [← C18adj_eq_adjMatrix]
  let u : (Matrix (ZMod 18) (ZMod 18) ℂ)ˣ := ⟨Fmat, Gmat, Fmat_mul_Gmat, Gmat_mul_Fmat⟩
  have hA : C18adj = (u : Matrix (ZMod 18) (ZMod 18) ℂ) * Dmat
      * ((u⁻¹ : (Matrix (ZMod 18) (ZMod 18) ℂ)ˣ) : Matrix (ZMod 18) (ZMod 18) ℂ) := by
    show C18adj = Fmat * Dmat * Gmat
    rw [← C18adj_mul_Fmat, Matrix.mul_assoc, Fmat_mul_Gmat, Matrix.mul_one]
  rw [hA, spectrum.units_conjugate, Dmat, _root_.spectrum_diagonal]
  ext μ
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, ZMod.val_lt k⟩, by norm_num⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(k : ZMod 18), rfl⟩

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


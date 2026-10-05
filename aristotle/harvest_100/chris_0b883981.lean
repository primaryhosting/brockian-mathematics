/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- The standard additive character `ZMod 14 → ℂ`, `j ↦ exp (2πI j / 14)`. -/
noncomputable def ee : AddChar (ZMod 14) ℂ := ZMod.stdAddChar

/-- Adjacency matrix of the cycle graph `C₁₄`, with vertices indexed by `ZMod 14`:
`i` and `j` are adjacent iff they differ by `±1`. -/
noncomputable def C14adj : Matrix (ZMod 14) (ZMod 14) ℂ :=
  Matrix.circulant (fun d : ZMod 14 => if d = 1 ∨ d = -1 then (1 : ℂ) else 0)

/-- The `k`-th Hückel eigenvalue of `C₁₄`: `2 cos (2πk/14)`. -/
noncomputable def huckelEigval (k : ℕ) : ℝ := 2 * Real.cos (2 * Real.pi * k / 14)

/-- The `k`-th eigenvector of the adjacency matrix of `C₁₄`: `j ↦ exp (2πI jk/14)`. -/
noncomputable def C14vec (k : ℕ) : ZMod 14 → ℂ := fun j => ee (j * (k : ZMod 14))

/-! ### Basic facts about the character `ee` -/

lemma ee_apply (k : ZMod 14) : ee k = Complex.exp (2 * Real.pi * Complex.I * k.val / 14) := by
  rw [ee, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  norm_num

lemma ee_ne_zero (k : ZMod 14) : ee k ≠ 0 := by
  rw [ee_apply]; exact Complex.exp_ne_zero _

/-- `ee k + ee (-k) = 2 cos (2π k.val / 14)`. -/
lemma ee_add_ee_neg (k : ZMod 14) :
    ee k + ee (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 14) : ℝ) : ℂ) := by
  have hx : ee k = Complex.exp (((2 * Real.pi * k.val / 14 : ℝ) : ℂ) * Complex.I) := by
    rw [ee_apply]; push_cast; ring_nf
  rw [AddChar.map_neg_eq_inv, hx, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-! ### The eigenvalue equation -/

/-- The key computation: applying the adjacency matrix to the character vector. -/
lemma C14adj_sum (i k : ZMod 14) :
    ∑ j : ZMod 14, C14adj i j * ee (j * k) = (ee k + ee (-k)) * ee (i * k) := by
  have hne : (i - 1 : ZMod 14) ≠ i + 1 := by
    intro h
    have : (2 : ZMod 14) = 0 := by linear_combination -h
    revert this; decide
  have hstep : ∀ j : ZMod 14, C14adj i j * ee (j * k)
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 14)) then ee (j * k) else 0 := by
    intro j
    have h1 : (i - j = 1) ↔ (j = i - 1) := by
      constructor <;> (intro h; linear_combination -h)
    have h2 : (i - j = -1) ↔ (j = i + 1) := by
      constructor <;> (intro h; linear_combination -h)
    simp only [C14adj, Matrix.circulant_apply, h1, h2, Finset.mem_insert,
      Finset.mem_singleton]
    split <;> simp
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

lemma huckelEigval_eq (k : ℕ) (hk : k < 14) :
    ((huckelEigval k : ℝ) : ℂ) = ee (k : ZMod 14) + ee (-(k : ZMod 14)) := by
  have hval : ((k : ZMod 14)).val = k := ZMod.val_natCast_of_lt hk
  rw [ee_add_ee_neg, hval, huckelEigval]

theorem C14adj_mulVec (k : ℕ) (hk : k < 14) :
    C14adj.mulVec (C14vec k) = ((huckelEigval k : ℝ) : ℂ) • C14vec k := by
  funext i
  simp only [Matrix.mulVec, dotProduct, C14vec, Pi.smul_apply, smul_eq_mul]
  rw [C14adj_sum i (k : ZMod 14), huckelEigval_eq k hk]

theorem C14vec_ne_zero (k : ℕ) : C14vec k ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [C14vec, Pi.zero_apply, zero_mul] at this
  exact ee_ne_zero 0 this

/-! ### Diagonalisation via the DFT matrix -/

/-- The DFT matrix. -/
noncomputable def U14 : Matrix (ZMod 14) (ZMod 14) ℂ := fun j k => ee (j * k)

/-- The (scaled) inverse DFT matrix. -/
noncomputable def V14 : Matrix (ZMod 14) (ZMod 14) ℂ :=
  fun k l => (14 : ℂ)⁻¹ * ee (-(k * l))

lemma U14_mul_V14 : U14 * V14 = 1 := by
  ext j l
  have hsum : ∑ x : ZMod 14, ee (x * (j - l))
      = ((if (j - l : ZMod 14) = 0 then (Fintype.card (ZMod 14)) else 0 : ℕ) : ℂ) :=
    AddChar.sum_mulShift (ψ := ee) (j - l) (ZMod.isPrimitive_stdAddChar 14)
  have hcard : Fintype.card (ZMod 14) = 14 := by simp
  rw [hcard] at hsum
  simp only [Matrix.mul_apply, U14, V14]
  have hterm : ∀ x : ZMod 14, ee (j * x) * ((14 : ℂ)⁻¹ * ee (-(x * l)))
      = (14 : ℂ)⁻¹ * ee (x * (j - l)) := by
    intro x
    have : x * (j - l) = j * x + -(x * l) := by ring
    rw [this, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum, hsum]
  by_cases h : j = l
  · subst h
    simp
  · have h' : (j - l : ZMod 14) ≠ 0 := sub_ne_zero_of_ne h
    simp [h', h]

lemma V14_mul_U14 : V14 * U14 = 1 := mul_eq_one_comm.mp U14_mul_V14

/-- `U14` as a unit of the matrix ring. -/
noncomputable def U14unit : (Matrix (ZMod 14) (ZMod 14) ℂ)ˣ :=
  ⟨U14, V14, U14_mul_V14, V14_mul_U14⟩

/-- Eigenvalue function on `ZMod 14`. -/
noncomputable def mu (k : ZMod 14) : ℂ := ee k + ee (-k)

lemma C14adj_mul_U14 : C14adj * U14 = U14 * Matrix.diagonal mu := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  show ∑ j : ZMod 14, C14adj i j * ee (j * k) = ee (i * k) * mu k
  rw [C14adj_sum i k, mu]
  ring

lemma C14adj_eq_conj : C14adj = (U14unit : Matrix (ZMod 14) (ZMod 14) ℂ)
    * Matrix.diagonal mu * (↑U14unit⁻¹ : Matrix (ZMod 14) (ZMod 14) ℂ) := by
  have h : (↑U14unit⁻¹ : Matrix (ZMod 14) (ZMod 14) ℂ) = V14 := rfl
  rw [h]
  show C14adj = U14 * Matrix.diagonal mu * V14
  rw [← C14adj_mul_U14, mul_assoc, U14_mul_V14, mul_one]

lemma charpoly_C14adj : C14adj.charpoly = ∏ k : ZMod 14, (Polynomial.X - Polynomial.C (mu k)) := by
  rw [C14adj_eq_conj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- Reindexing a product over `ZMod 14` as a product over `Finset.range 14`. -/
lemma prod_zmod14_eq_range {M : Type*} [CommMonoid M] (g : ZMod 14 → M) :
    ∏ k : ZMod 14, g k = ∏ k ∈ Finset.range 14, g (k : ZMod 14) := by
  refine Finset.prod_nbij' (fun k => k.val) (fun k => (k : ZMod 14)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simpa using ZMod.val_lt a
  · intro a _; exact Finset.mem_univ _
  · intro a _; simp
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; simp

/-! ### Main theorem -/

/-- **Hückel theory for `C₁₄`.**  The adjacency matrix of the cycle graph `C₁₄` has
eigenvalues `2 cos (2πk/14)` for `k = 0, …, 13`:  each vector
`j ↦ exp (2πI jk/14)` is a nonzero eigenvector with eigenvalue `2 cos (2πk/14)`, and the
characteristic polynomial of the adjacency matrix is exactly
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, so there are no other eigenvalues. -/
theorem huckel_C14 :
    (∀ k : ℕ, k < 14 →
        C14vec k ≠ 0 ∧
        C14adj.mulVec (C14vec k) = ((huckelEigval k : ℝ) : ℂ) • C14vec k) ∧
      C14adj.charpoly =
        ∏ k ∈ Finset.range 14,
          (Polynomial.X - Polynomial.C ((huckelEigval k : ℝ) : ℂ)) := by
  refine ⟨fun k hk => ⟨C14vec_ne_zero k, C14adj_mulVec k hk⟩, ?_⟩
  rw [charpoly_C14adj, prod_zmod14_eq_range]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  rw [huckelEigval_eq k (Finset.mem_range.mp hk), mu]

end Chem


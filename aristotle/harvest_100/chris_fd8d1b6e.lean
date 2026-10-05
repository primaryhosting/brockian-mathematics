/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Complex Matrix Polynomial

namespace Chem

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`.  In Hückel theory (with `α = 0`,
`β = 1`) this is the Hückel matrix of the annulene `C₂₀`. -/
noncomputable def C20adj : Matrix (ZMod 20) (ZMod 20) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue of `C₂₀`, namely `2 cos (2πk/20)`. -/
noncomputable def C20eigenvalue (k : ZMod 20) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 20)

/-- The `k`-th (unnormalized) Hückel eigenvector of `C₂₀`:
its `i`-th entry is `exp (2πi·k/20) ^ i`. -/
noncomputable def C20vec (k : ZMod 20) : ZMod 20 → ℂ :=
  fun i => Complex.exp (((2 * Real.pi * (k.val : ℝ) / 20 : ℝ) : ℂ) * Complex.I) ^ i.val

/-- Multiplying the adjacency matrix into a vector adds the two neighbouring entries. -/
lemma C20adj_mulVec (v : ZMod 20 → ℂ) (i : ZMod 20) :
    (C20adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hne : (i + 1) ≠ (i - 1) := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination h
    revert h2; decide
  have key : ∀ j : ZMod 20, C20adj i j * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · subst h1; simp [C20adj, hne]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · subst h2; simp [C20adj, Ne.symm hne]
      · simp [C20adj, h1, h2]
  simp only [Matrix.mulVec, dotProduct, key, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i + 1) v, Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- If `a ^ 20 = 1`, then `a ^ (n % 20) = a ^ n`. -/
lemma pow_mod_twenty {a : ℂ} (ha : a ^ 20 = 1) (n : ℕ) : a ^ (n % 20) = a ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 20, pow_add, pow_mul, ha, one_pow, one_mul]

/-- If `a ^ 20 = 1`, then `i ↦ a ^ i.val` is multiplicative on `ZMod 20`. -/
lemma pow_val_add {a : ℂ} (ha : a ^ 20 = 1) (i j : ZMod 20) :
    a ^ (i + j).val = a ^ i.val * a ^ j.val := by
  rw [ZMod.val_add, pow_mod_twenty ha, pow_add]

/-- The main computation: if `a ^ 20 = 1` then `i ↦ a ^ i.val` is an eigenvector of the
adjacency matrix of `C₂₀` with eigenvalue `a + a⁻¹`. -/
lemma C20adj_mulVec_pow {a : ℂ} (ha : a ^ 20 = 1) :
    C20adj *ᵥ (fun i : ZMod 20 => a ^ i.val) = (a + a⁻¹) • (fun i : ZMod 20 => a ^ i.val) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hv1 : (1 : ZMod 20).val = 1 := rfl
  funext i
  rw [C20adj_mulVec]
  have h1 : a ^ (i + 1).val = a ^ i.val * a := by
    rw [pow_val_add ha, hv1, pow_one]
  have h2 : a ^ (i - 1).val * a = a ^ i.val := by
    have h := pow_val_add ha (i - 1) 1
    rw [sub_add_cancel, hv1, pow_one] at h
    rw [h]
  have h2' : a ^ (i - 1).val = a ^ i.val * a⁻¹ := by
    field_simp at h2 ⊢
    linear_combination h2
  simp only [Pi.smul_apply, smul_eq_mul, h1, h2']
  ring

/-- The primitive 20-th root of unity `exp (2πi k / 20)` attached to `k`. -/
noncomputable def C20root (k : ZMod 20) : ℂ :=
  Complex.exp (((2 * Real.pi * (k.val : ℝ) / 20 : ℝ) : ℂ) * Complex.I)

lemma C20vec_eq (k i : ZMod 20) : C20vec k i = (C20root k) ^ i.val := rfl

lemma C20root_pow_twenty (k : ZMod 20) : (C20root k) ^ 20 = 1 := by
  rw [C20root, ← Complex.exp_nat_mul]
  have h : ((20 : ℕ) : ℂ) * (((2 * Real.pi * (k.val : ℝ) / 20 : ℝ) : ℂ) * Complex.I)
      = ((k.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma C20root_ne_zero (k : ZMod 20) : C20root k ≠ 0 := Complex.exp_ne_zero _

/-- `C20root k + (C20root k)⁻¹ = 2 cos (2πk/20)`, the `k`-th Hückel eigenvalue. -/
lemma C20root_add_inv (k : ZMod 20) :
    C20root k + (C20root k)⁻¹ = ((C20eigenvalue k : ℝ) : ℂ) := by
  rw [C20eigenvalue, C20root]
  push_cast
  rw [Complex.two_cos, ← Complex.exp_neg]
  ring_nf

/-- Each `2 cos (2πk/20)` is an eigenvalue of the adjacency matrix of `C₂₀`,
with explicit eigenvector `C20vec k`. -/
lemma C20adj_mulVec_C20vec (k : ZMod 20) :
    C20adj *ᵥ C20vec k = ((C20eigenvalue k : ℝ) : ℂ) • C20vec k := by
  rw [← C20root_add_inv k]
  exact C20adj_mulVec_pow (C20root_pow_twenty k)

lemma C20vec_ne_zero (k : ZMod 20) : C20vec k ≠ 0 := by
  intro h
  have h0 : C20vec k 0 = 0 := by rw [h]; rfl
  rw [C20vec_eq] at h0
  simp only [show (0 : ZMod 20).val = 0 from rfl, pow_zero] at h0
  exact one_ne_zero h0

/-! ### The full spectrum -/

lemma C20root_isPrimitiveRoot : IsPrimitiveRoot (C20root 1) 20 := by
  have h : C20root 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / ((20 : ℕ) : ℂ)) := by
    rw [C20root]
    congr 1
    push_cast [show (1 : ZMod 20).val = 1 from rfl]
    ring
  rw [h]
  exact Complex.isPrimitiveRoot_exp 20 (by norm_num)

lemma C20root_eq_pow (k : ZMod 20) : C20root k = (C20root 1) ^ k.val := by
  rw [C20root, C20root, ← Complex.exp_nat_mul]
  congr 1
  push_cast [show (1 : ZMod 20).val = 1 from rfl]
  ring

lemma C20root_symm (i k : ZMod 20) : (C20root k) ^ i.val = (C20root i) ^ k.val := by
  rw [C20root_eq_pow k, C20root_eq_pow i, ← pow_mul, ← pow_mul, Nat.mul_comm]

lemma C20root_inj {i j : ZMod 20} (h : C20root i = C20root j) : i = j := by
  rw [C20root_eq_pow i, C20root_eq_pow j] at h
  have := C20root_isPrimitiveRoot.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) h
  exact (ZMod.val_injective 20) this

lemma sum_pow_val {b : ℂ} (hb : b ^ 20 = 1) :
    ∑ k : ZMod 20, b ^ k.val = if b = 1 then 20 else 0 := by
  have h0 : ∑ k : ZMod 20, b ^ k.val = ∑ n ∈ Finset.range 20, b ^ n :=
    Fin.sum_univ_eq_sum_range (fun n => b ^ n) 20
  rw [h0]
  by_cases h : b = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hb]
    simp

/-- The (unnormalized) discrete Fourier matrix, whose `k`-th column is `C20vec k`. -/
noncomputable def C20dft : Matrix (ZMod 20) (ZMod 20) ℂ := fun i k => C20vec k i

/-- Its inverse, up to the factor `20`. -/
noncomputable def C20dftInv : Matrix (ZMod 20) (ZMod 20) ℂ :=
  fun k j => ((C20root j) ^ k.val)⁻¹

lemma C20dft_mul_inv : C20dft * C20dftInv = (20 : ℂ) • (1 : Matrix (ZMod 20) (ZMod 20) ℂ) := by
  ext i j
  have hterm : ∀ k : ZMod 20, C20dft i k * C20dftInv k j
      = (C20root i * (C20root j)⁻¹) ^ k.val := by
    intro k
    rw [C20dft, C20dftInv, C20vec_eq, C20root_symm i k, mul_pow, ← inv_pow]
  have hb : (C20root i * (C20root j)⁻¹) ^ 20 = 1 := by
    rw [mul_pow, inv_pow, C20root_pow_twenty, C20root_pow_twenty, inv_one, mul_one]
  rw [Matrix.mul_apply]
  simp only [hterm]
  rw [sum_pow_val hb]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [if_pos (mul_inv_cancel₀ (C20root_ne_zero i))]
    simp
  · rw [if_neg, Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero]
    intro hcon
    refine h (C20root_inj ?_)
    have hj := C20root_ne_zero j
    field_simp at hcon
    exact hcon

lemma C20adj_mul_dft :
    C20adj * C20dft = C20dft * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ)) := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have h : ∑ j, C20adj i j * C20dft j k = (C20adj *ᵥ C20vec k) i := rfl
  rw [h, C20adj_mulVec_C20vec]
  simp [C20dft, mul_comm]

lemma C20dft_mul_inv_one : C20dft * ((20 : ℂ)⁻¹ • C20dftInv) = 1 := by
  rw [Matrix.mul_smul, C20dft_mul_inv, smul_smul]
  norm_num

/-- The Fourier matrix as a unit of the matrix ring. -/
noncomputable def C20dftUnit : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ :=
  ⟨C20dft, (20 : ℂ)⁻¹ • C20dftInv, C20dft_mul_inv_one,
    mul_eq_one_comm.mp C20dft_mul_inv_one⟩

/-- The characteristic polynomial of the adjacency matrix of `C₂₀` factors as
`∏ₖ (X - 2 cos (2πk/20))`: the eigenvalues are exactly the `2 cos (2πk/20)`,
with multiplicity. -/
theorem C20adj_charpoly :
    C20adj.charpoly = ∏ k : ZMod 20, (X - C ((C20eigenvalue k : ℝ) : ℂ)) := by
  have hconj : C20adj = (C20dftUnit : Matrix (ZMod 20) (ZMod 20) ℂ)
      * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ))
      * (↑C20dftUnit⁻¹ : Matrix (ZMod 20) (ZMod 20) ℂ) := by
    show C20adj = C20dft * Matrix.diagonal (fun k => ((C20eigenvalue k : ℝ) : ℂ))
      * ((20 : ℂ)⁻¹ • C20dftInv)
    rw [← C20adj_mul_dft, Matrix.mul_assoc, C20dft_mul_inv_one, mul_one]
  rw [hconj, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- Conversely, every eigenvalue of the adjacency matrix of `C₂₀` is of the form
`2 cos (2πk/20)`. -/
theorem C20adj_eigenvalue_eq {mu : ℂ} (v : ZMod 20 → ℂ) (hv : v ≠ 0)
    (h : C20adj *ᵥ v = mu • v) : ∃ k : ZMod 20, mu = ((C20eigenvalue k : ℝ) : ℂ) := by
  have hdet : (Matrix.scalar (ZMod 20) mu - C20adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, h]
    funext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have heval := Matrix.eval_charpoly C20adj mu
  rw [hdet, C20adj_charpoly, Polynomial.eval_prod] at heval
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp heval
  refine ⟨k, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
  exact hk

/-- **Hückel theory for the annulene C₂₀.**  The adjacency (Hückel) matrix of the cycle
graph `C₂₀` has eigenvalues exactly `2 cos (2πk/20)` for `k = 0, …, 19`:

* each `2 cos (2πk/20)` is an eigenvalue, with explicit nonzero eigenvector `C20vec k`;
* the characteristic polynomial is `∏ₖ (X - 2 cos (2πk/20))`, so there are no others,
  even counting multiplicities;
* consequently every eigenvalue is of this form. -/
theorem huckel_C20 :
    (∀ k : ZMod 20, C20vec k ≠ 0 ∧
        C20adj *ᵥ C20vec k
          = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 20) : ℝ) : ℂ) • C20vec k) ∧
    C20adj.charpoly
      = ∏ k : ZMod 20, (X - C ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 20) : ℝ) : ℂ)) ∧
    ∀ (mu : ℂ) (v : ZMod 20 → ℂ), v ≠ 0 → C20adj *ᵥ v = mu • v →
      ∃ k : ZMod 20, mu = ((2 * Real.cos (2 * Real.pi * (k.val : ℝ) / 20) : ℝ) : ℂ) :=
  ⟨fun k => ⟨C20vec_ne_zero k, C20adj_mulVec_C20vec k⟩, C20adj_charpoly,
    fun _ v hv h => C20adj_eigenvalue_eq v hv h⟩

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


/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` only because Lean 4 does not allow a module
-- docstring to precede the `import` commands; the same header is repeated below verbatim.)

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Hückel (tight-binding) Hamiltonian of the cyclic polyene `C₁₈` is, up to the affine
normalisation `H = α + β A`, the adjacency matrix `A` of the cycle graph `C₁₈`.
We prove that a complex number `μ` is an eigenvalue of that adjacency matrix precisely when
`μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`.

The vertex type of `SimpleGraph.cycleGraph 18` is `Fin 18`, which is `ZMod 18`; all index
arithmetic below is therefore modulo `18`.
-/

namespace Chem

open Complex Matrix Finset

/-- A primitive 18-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

lemma zeta_pow_18 : zeta ^ 18 = 1 := by
  rw [zeta, ← Complex.exp_nat_mul,
    show ((18 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 18) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 18 :=
  Complex.isPrimitiveRoot_exp 18 (by norm_num)

lemma zeta_pow_mod (a : ℕ) : zeta ^ (a % 18) = zeta ^ a := by
  conv_rhs => rw [show a = 18 * (a / 18) + a % 18 by omega]
  rw [pow_add, pow_mul, zeta_pow_18, one_pow, one_mul]

/-- The additive character `k ↦ ζ^k` of `ZMod 18`. -/
noncomputable def chi : AddChar (ZMod 18) ℂ := AddChar.zmodChar 18 zeta_pow_18

lemma chi_apply (k : ZMod 18) : chi k = zeta ^ k.val := AddChar.zmodChar_apply _ _

lemma chi_add (a b : ZMod 18) : chi (a + b) = chi a * chi b := chi.map_add_eq_mul a b

lemma chi_zero : chi 0 = 1 := chi.map_zero_eq_one

/-- The candidate eigenvalues `2 cos (2πk/18)`, in exponential form. -/
noncomputable def eig (k : ZMod 18) : ℂ := chi k + chi (-k)

/-- The Fourier (Vandermonde) matrix diagonalising the adjacency matrix. -/
noncomputable def Pm : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.vandermonde (fun j : Fin 18 => zeta ^ (j : ℕ))

lemma Pm_apply (j k : ZMod 18) : Pm j k = chi (j * k) := by
  simp only [Pm, Matrix.vandermonde, Matrix.of_apply, chi_apply, ZMod.val_mul, zeta_pow_mod,
    pow_mul]
  rfl

lemma Pm_det_ne_zero : Pm.det ≠ 0 := by
  have h : Pm.det = (Matrix.vandermonde (fun j : Fin 18 => zeta ^ (j : ℕ))).det := rfl
  rw [h, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  simp only at hab
  exact Fin.ext (zeta_isPrimitiveRoot.pow_inj a.isLt b.isLt hab)

/-- The adjacency matrix of the cycle graph `C₁₈`, indexed by `ZMod 18`. -/
noncomputable def Adj : Matrix (ZMod 18) (ZMod 18) ℂ := (SimpleGraph.cycleGraph 18).adjMatrix ℂ

lemma Adj_apply (i j : ZMod 18) : Adj i j = if i - j = 1 ∨ j - i = 1 then 1 else 0 := by
  simp [Adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]

lemma Adj_sum (f : ZMod 18 → ℂ) (j : ZMod 18) :
    ∑ l, Adj j l * f l = f (j - 1) + f (j + 1) := by
  have hset : (Finset.univ.filter (fun l : ZMod 18 => j - l = 1 ∨ l - j = 1)) = {j - 1, j + 1} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (h | h)
      · left; rw [h]; ring
      · right; rw [h]; ring
  have hne : (j - 1) ≠ (j + 1) := by
    intro h
    have h2 : (2 : ZMod 18) = 0 := by linear_combination -h
    revert h2; decide
  calc ∑ l, Adj j l * f l
      = ∑ l ∈ Finset.univ.filter (fun l : ZMod 18 => j - l = 1 ∨ l - j = 1), f l := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun l _ => by rw [Adj_apply]; split <;> simp)
    _ = f (j - 1) + f (j + 1) := by rw [hset, Finset.sum_pair hne]

/-- The diagonalisation identity `A · P = P · D`. -/
lemma Adj_mul_Pm : Adj * Pm = Pm * Matrix.diagonal eig := by
  ext j k
  rw [Matrix.mul_apply, Adj_sum (fun l => Pm l k) j, Matrix.mul_diagonal, Pm_apply, Pm_apply,
    Pm_apply]
  have h1 : (j - 1) * k = j * k + (-k) := by ring
  have h2 : (j + 1) * k = j * k + k := by ring
  rw [h1, h2, chi_add, chi_add, eig]
  ring

lemma det_sub_smul (μ : ℂ) :
    (Adj - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)).det = ∏ k : ZMod 18, (eig k - μ) := by
  have key : (Adj - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)) * Pm
      = Pm * (Matrix.diagonal eig - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Adj_mul_Pm, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hD : (Matrix.diagonal eig - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)).det
      = ∏ k : ZMod 18, (eig k - μ) := by
    rw [show Matrix.diagonal eig - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)
        = Matrix.diagonal (fun k => eig k - μ) by
      ext i j
      by_cases h : i = j <;> simp [h]]
    exact Matrix.det_diagonal
  rw [hD] at hdet
  exact mul_right_cancel₀ Pm_det_ne_zero (by rw [hdet]; ring)

lemma eig_eq (k : ZMod 18) : eig k = 2 * Real.cos (2 * Real.pi * k.val / 18) := by
  have hchi : chi k = Complex.exp ((2 * Real.pi * k.val / 18 : ℝ) * Complex.I) := by
    rw [chi_apply, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hprod : chi k * chi (-k) = 1 := by rw [← chi_add, add_neg_cancel, chi_zero]
  have hne : chi k ≠ 0 := by rw [hchi]; exact Complex.exp_ne_zero _
  have hchi' : chi (-k) = Complex.exp (-(2 * Real.pi * k.val / 18 : ℝ) * Complex.I) := by
    have hinv : chi (-k) = (chi k)⁻¹ := by
      field_simp
      linear_combination hprod
    rw [hinv, hchi, ← Complex.exp_neg]
    congr 1
    ring
  rw [eig, hchi, hchi', Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

/-- **Hückel spectrum of C₁₈.** A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₁₈` (the Hückel Hamiltonian of the cyclic polyene `C₁₈` in units where
`α = 0`, `β = 1`) if and only if `μ = 2 cos (2πk/18)` for some `k ∈ {0, …, 17}`. -/
theorem huckel_C18 (μ : ℂ) :
    (∃ v : ZMod 18 → ℂ, v ≠ 0 ∧
        ((SimpleGraph.cycleGraph 18).adjMatrix ℂ : Matrix (ZMod 18) (ZMod 18) ℂ).mulVec v = μ • v)
      ↔ ∃ k : ZMod 18, μ = 2 * Real.cos (2 * Real.pi * k.val / 18) := by
  have hiff : (∃ v : ZMod 18 → ℂ, v ≠ 0 ∧
        ((SimpleGraph.cycleGraph 18).adjMatrix ℂ : Matrix (ZMod 18) (ZMod 18) ℂ).mulVec v = μ • v)
      ↔ ∃ v : ZMod 18 → ℂ, v ≠ 0 ∧ (Adj - μ • (1 : Matrix (ZMod 18) (ZMod 18) ℂ)).mulVec v = 0 := by
    constructor
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
      exact hAv
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hAv
      exact hAv
  rw [hiff, Matrix.exists_mulVec_eq_zero_iff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k, ?_⟩
    rw [← eig_eq k]
    exact (sub_eq_zero.mp hk).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, eig_eq]
    exact hk.symm

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


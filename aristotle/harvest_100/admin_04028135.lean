/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-! -/` module docstring,
-- because in Lean 4.28 a module docstring is a command and cannot precede `import`.
-- The same text is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel spectrum of the cyclic polyene C₁₉: the eigenvalues of the adjacency matrix of the
cycle graph `C₁₉` are exactly the numbers `2 cos (2πk/19)`, `k = 0, …, 18`.

The proof identifies the adjacency matrix with `S + S¹⁸`, where `S` is the cyclic shift matrix
(a circulant matrix), computes `spectrum ℂ S` (all 19-th roots of unity), and then applies the
spectral mapping theorem `spectrum.map_polynomial_aeval_of_degree_pos` for the polynomial
`X + X ^ 18`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Matrix Complex Polynomial SimpleGraph

/-- A primitive 19-th root of unity. -/
noncomputable def zeta19 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 19)

lemma isPrimitiveRoot_zeta19 : IsPrimitiveRoot zeta19 19 := by
  have h := Complex.isPrimitiveRoot_exp 19 (by norm_num)
  simpa [zeta19] using h

lemma zeta19_pow_19 : zeta19 ^ 19 = 1 := isPrimitiveRoot_zeta19.pow_eq_one

/-- The cyclic shift matrix on `Fin 19`. -/
noncomputable def shift19 : Matrix (Fin 19) (Fin 19) ℂ := Matrix.circulant (Pi.single 1 1)

/-- Circulant matrices of indicator vectors multiply by adding their indices. -/
lemma circulant_single_mul (a b : Fin 19) :
    Matrix.circulant (Pi.single a (1 : ℂ)) * Matrix.circulant (Pi.single b (1 : ℂ)) =
      Matrix.circulant (Pi.single (a + b) (1 : ℂ)) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (i - a)]
  · have h1 : i - (i - a) = a := by abel
    have hiff : (i - a - j = b) ↔ (i - j = a + b) := by
      constructor
      · intro h; rw [← h]; abel
      · intro h; rw [sub_right_comm, h]; abel
    simp only [Matrix.circulant_apply, h1, Pi.single_apply, if_true, one_mul]
    rw [if_congr hiff rfl rfl]
  · intro k _ hk
    have h0 : (if i - k = a then (1 : ℂ) else 0) = 0 := by
      apply if_neg
      intro h
      exact hk (by rw [← h]; abel)
    simp only [Matrix.circulant_apply, Pi.single_apply, h0, zero_mul]
  · simp

lemma shift19_pow (m : ℕ) :
    shift19 ^ m = Matrix.circulant (Pi.single (Fin.ofNat 19 m) (1 : ℂ)) := by
  induction m with
  | zero => simp [Fin.ofNat]
  | succ m ih =>
      have hstep : Fin.ofNat 19 (m + 1) = Fin.ofNat 19 m + 1 := by
        simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
      rw [pow_succ, ih, shift19, circulant_single_mul, hstep]

lemma shift19_pow_19 : shift19 ^ 19 = 1 := by
  rw [shift19_pow, show Fin.ofNat 19 19 = 0 from by decide, Matrix.circulant_single_one]

lemma shift19_pow_18 :
    shift19 ^ 18 = Matrix.circulant (Pi.single (18 : Fin 19) (1 : ℂ)) := by
  rw [shift19_pow, show Fin.ofNat 19 18 = 18 from by decide]

lemma cycleGraph19_adj (i j : Fin 19) :
    (SimpleGraph.cycleGraph 19).Adj i j ↔ (i - j = 1 ∨ i - j = 18) := by
  rw [SimpleGraph.cycleGraph_adj (n := 17)]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have hh : i - j = -(j - i) := by abel
      rw [hh, h]; decide
  · rintro (h | h)
    · exact Or.inl h
    · right
      have hh : j - i = -(i - j) := by abel
      rw [hh, h]; decide

/-- The adjacency matrix of `C₁₉` is `S + S¹⁸`, where `S` is the cyclic shift. -/
lemma adjMatrix_cycleGraph19 :
    (SimpleGraph.cycleGraph 19).adjMatrix ℂ = shift19 + shift19 ^ 18 := by
  rw [shift19_pow_18, shift19, ← Matrix.circulant_add]
  ext i j
  rw [SimpleGraph.adjMatrix_apply, Matrix.circulant_apply]
  simp only [cycleGraph19_adj, Pi.add_apply, Pi.single_apply]
  by_cases h1 : i - j = 1 <;> by_cases h2 : i - j = 18 <;> simp [h1, h2]

/-- If `M *ᵥ v = μ • v` for a nonzero vector `v`, then `μ` lies in the spectrum of `M`. -/
lemma mem_spectrum_of_mulVec {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (μ : ℂ) (v : n → ℂ) (hv : v ≠ 0) (h : M *ᵥ v = μ • v) :
    μ ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff]
  intro hu
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  apply hu
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  have hmul : (algebraMap ℂ (Matrix n n ℂ) μ - M) *ᵥ v = μ • v - M *ᵥ v := by
    rw [Matrix.sub_mulVec]
    congr 1
    rw [Matrix.algebraMap_eq_diagonal]
    ext i
    simp [Matrix.mulVec, Matrix.diagonal, dotProduct]
  rw [hmul, h, sub_self]

lemma shift19_mulVec (v : Fin 19 → ℂ) (i : Fin 19) : (shift19 *ᵥ v) i = v (i - 1) := by
  rw [shift19, Matrix.mulVec, dotProduct, Finset.sum_eq_single (i - 1)]
  · have h1 : i - (i - 1) = 1 := by abel
    rw [Matrix.circulant_apply, h1, Pi.single_eq_same, one_mul]
  · intro k _ hk
    have h0 : (if i - k = 1 then (1 : ℂ) else 0) = 0 := by
      apply if_neg
      intro h
      exact hk (by rw [← h]; abel)
    simp only [Matrix.circulant_apply, Pi.single_apply, h0, zero_mul]
  · simp

/-- The shift relation satisfied by the eigenvector `j ↦ μ ^ (19 - j)`. -/
lemma pow_shift_relation (μ : ℂ) (h : μ ^ 19 = 1) (i : Fin 19) :
    μ ^ (19 - (i - 1).val) = μ * μ ^ (19 - i.val) := by
  fin_cases i <;> simp [Fin.sub_def] <;> ring_nf
  rw [show (20 : ℕ) = 19 + 1 from rfl, pow_succ, h, one_mul]

lemma zeta_pow_mem_spectrum_shift19 (k : ℕ) : zeta19 ^ k ∈ spectrum ℂ shift19 := by
  set μ : ℂ := zeta19 ^ k with hμ
  have hμ19 : μ ^ 19 = 1 := by
    rw [hμ, ← pow_mul, mul_comm, pow_mul, zeta19_pow_19, one_pow]
  refine mem_spectrum_of_mulVec shift19 μ (fun j => μ ^ (19 - j.val)) ?_ ?_
  · intro hv
    have h0 : μ ^ (19 - (0 : Fin 19).val) = 0 := congrFun hv 0
    rw [show (19 - (0 : Fin 19).val) = 19 from rfl, hμ19] at h0
    exact one_ne_zero h0
  · funext i
    rw [shift19_mulVec, Pi.smul_apply, smul_eq_mul]
    exact pow_shift_relation μ hμ19 i

lemma spectrum_shift19 :
    spectrum ℂ shift19 = Set.range (fun k : Fin 19 => zeta19 ^ (k : ℕ)) := by
  apply Set.eq_of_subset_of_subset
  · intro μ hμ
    have h1 : μ ^ 19 ∈ spectrum ℂ (shift19 ^ 19) := spectrum.pow_mem_pow shift19 19 hμ
    rw [shift19_pow_19, spectrum.one_eq] at h1
    have h2 : μ ^ 19 = 1 := h1
    obtain ⟨i, hi, hval⟩ := isPrimitiveRoot_zeta19.eq_pow_of_pow_eq_one h2
    exact ⟨⟨i, hi⟩, hval⟩
  · rintro _ ⟨k, rfl⟩
    exact zeta_pow_mem_spectrum_shift19 (k : ℕ)

lemma eval_eigenvalue (k : ℕ) :
    zeta19 ^ k + (zeta19 ^ k) ^ 18 = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 19 with hθ
  have hz : zeta19 ^ k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta19, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have h18 : (zeta19 ^ k) ^ 18 = Complex.exp (-(θ : ℂ) * Complex.I) := by
    rw [hz, ← Complex.exp_nat_mul]
    have key : ((18 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)
        = -(θ : ℂ) * Complex.I + ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hθ]; push_cast; ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h18, hz, ← Complex.two_cos, ← Complex.ofReal_cos]
  push_cast
  ring

/-- **Hückel theory for C₁₉.** The eigenvalues (spectrum) of the adjacency matrix of the cycle
graph `C₁₉` are exactly the numbers `2 cos (2πk/19)` for `k = 0, 1, …, 18`. -/
theorem huckel_C19 :
    spectrum ℂ ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) =
      Set.range (fun k : Fin 19 => ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)) := by
  have hp : (Polynomial.aeval shift19) (X + X ^ 18 : ℂ[X]) =
      (SimpleGraph.cycleGraph 19).adjMatrix ℂ := by
    rw [adjMatrix_cycleGraph19]
    simp
  have hd : (X + X ^ 18 : ℂ[X]).degree = 18 := by compute_degree!
  have hdeg : 0 < (X + X ^ 18 : ℂ[X]).degree := by
    rw [hd]; decide
  rw [← hp, spectrum.map_polynomial_aeval_of_degree_pos _ _ hdeg, spectrum_shift19,
    ← Set.range_comp]
  apply congrArg
  funext k
  simpa using eval_eigenvalue (k : ℕ)

end Chem


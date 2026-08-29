import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset Polynomial

set_option maxHeartbeats 1000000

/-! ## Generalities on eigenvalues of matrices -/

/-- A scalar `μ` is an eigenvalue of `M` iff `M - μ • 1` is singular. -/
lemma exists_eigenvector_iff_det_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {K : Type*}
    [Field K] (M : Matrix n n K) (μ : K) :
    (∃ v : n → K, v ≠ 0 ∧ M *ᵥ v = μ • v) ↔ (M - μ • 1).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]⟩
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h

/-- If `v` is an eigenvector of `M` with eigenvalue `c`, it is an eigenvector of `M ^ d`. -/
lemma pow_mulVec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {v : n → ℂ} {c : ℂ}
    (h : M *ᵥ v = c • v) (d : ℕ) : M ^ d *ᵥ v = c ^ d • v := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, pow_succ']
    simp [smul_smul, mul_comm]

/-- If `v` is an eigenvector of `M` with eigenvalue `c`, it is an eigenvector of `g(M)`. -/
lemma aeval_mulVec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} {v : n → ℂ} {c : ℂ}
    (h : M *ᵥ v = c • v) (g : ℂ[X]) : (aeval M g) *ᵥ v = (g.eval c) • v := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [Matrix.add_mulVec, hp, hq, add_smul]
  | monomial d a =>
    simp only [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one]
    rw [smul_mul_assoc, one_mul, smul_mulVec, pow_mulVec h d, smul_smul]

/-! ## The 20-th root of unity -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

lemma w_primitive : IsPrimitiveRoot w 20 := by
  simpa [w] using Complex.isPrimitiveRoot_exp 20 (by norm_num)

lemma w_pow_twenty : w ^ 20 = 1 := w_primitive.pow_eq_one

/-- `w ^ n` only depends on `n % 20`. -/
lemma w_pow_mod (a b : ℕ) (h : a % 20 = b % 20) : w ^ a = w ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 20, pow_add, pow_mul, w_pow_twenty, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 20, pow_add, pow_mul, w_pow_twenty, one_pow, one_mul]

lemma w_pow_eq_exp (k : ℕ) : w ^ k = Complex.exp ((2 * Real.pi * k / 20 : ℝ) * Complex.I) := by
  rw [w, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma w_pow_nineteen (k : ℕ) (hk : k ≤ 20) : (w ^ k) ^ 19 = w ^ (20 - k) := by
  rw [← pow_mul]
  apply w_pow_mod
  have h1 : (k * 19 + k) % 20 = ((20 - k) + k) % 20 := by
    rw [show k * 19 + k = 20 * k by ring, Nat.sub_add_cancel hk]
    simp [Nat.mul_mod_right]
  exact Nat.ModEq.add_right_cancel' k h1

/-- The eigenvalues, in exponential form. -/
lemma two_cos_eq (k : ℕ) (hk : k ≤ 20) :
    ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ) = w ^ k + w ^ (20 - k) := by
  have hmul : w ^ k * w ^ (20 - k) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hk, w_pow_twenty]
  have hne : (w : ℂ) ^ k ≠ 0 := by
    rw [w_pow_eq_exp]; exact Complex.exp_ne_zero _
  have hinv : w ^ (20 - k) = (w ^ k)⁻¹ := by
    field_simp
    linear_combination hmul
  rw [hinv, w_pow_eq_exp, Complex.ofReal_mul, Complex.ofReal_cos, ← Complex.exp_neg,
    show ((2 : ℝ) : ℂ) = 2 from by norm_num, Complex.two_cos]
  ring_nf

/-! ## The cyclic shift matrix and the adjacency matrix of `C₂₀` -/

/-- The cyclic shift matrix on `Fin 20`. -/
def S : Matrix (Fin 20) (Fin 20) ℂ := Matrix.of fun i j => if j = i + 1 then 1 else 0

private lemma ofNat_succ (k : ℕ) : (Fin.ofNat 20 (k + 1) : Fin 20) = Fin.ofNat 20 k + 1 := by
  apply Fin.ext; simp [Fin.ofNat, Fin.add_def]

lemma S_pow (k : ℕ) : S ^ k = Matrix.of fun i j => if j = i + Fin.ofNat 20 k then 1 else 0 := by
  induction k with
  | zero => ext i j; simp [Matrix.one_apply, Fin.ofNat, eq_comm]
  | succ k ih =>
    ext i j
    rw [pow_succ', ih]
    simp only [Matrix.mul_apply, Matrix.of_apply, S]
    rw [Finset.sum_eq_single (i + 1)]
    · rw [ofNat_succ]; simp [add_comm, add_left_comm]
    · intro b _ hb; rw [if_neg hb, zero_mul]
    · intro h; simp at h

lemma S_pow_twenty : S ^ 20 = 1 := by
  rw [S_pow]; ext i j; simp [Matrix.one_apply, Fin.ofNat, eq_comm]

/-- The adjacency matrix of the cycle graph `C₂₀`, over `ℂ`. -/
noncomputable def AC : Matrix (Fin 20) (Fin 20) ℂ := (SimpleGraph.cycleGraph 20).adjMatrix ℂ

lemma AC_eq : AC = S + S ^ 19 := by
  rw [AC, S_pow]
  ext i j
  have hadj : (SimpleGraph.cycleGraph 20).Adj i j ↔ (j = i + 1 ∨ j = i + Fin.ofNat 20 19) := by
    revert i j; decide
  have hex : ¬(j = i + 1 ∧ j = i + Fin.ofNat 20 19) := by revert i j; decide
  simp only [SimpleGraph.adjMatrix_apply, Matrix.add_apply, Matrix.of_apply, S]
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i + Fin.ofNat 20 19 <;>
    simp [h1, h2, hadj] at * <;> tauto

/-! ## The eigenvectors -/

/-- The discrete Fourier vector `j ↦ w ^ (j k)`. -/
noncomputable def fvec (k : ℕ) : Fin 20 → ℂ := fun j => w ^ (j.val * k)

lemma fvec_ne_zero (k : ℕ) : fvec k ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [fvec] at this

lemma S_mulVec_fvec (k : ℕ) : S *ᵥ fvec k = w ^ k • fvec k := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, S, Pi.smul_apply, smul_eq_mul, fvec]
  rw [Finset.sum_eq_single (i + 1)]
  · rw [if_pos rfl, one_mul]
    have h1 : ((i + 1 : Fin 20)).val = (i.val + 1) % 20 := by simp [Fin.add_def]
    rw [h1, ← pow_add]
    apply w_pow_mod
    have h2 : ((i.val + 1) % 20) * k ≡ (i.val + 1) * k [MOD 20] :=
      Nat.ModEq.mul_right k (Nat.mod_modEq (i.val + 1) 20)
    calc ((i.val + 1) % 20) * k % 20 = ((i.val + 1) * k) % 20 := h2
      _ = (k + i.val * k) % 20 := by ring_nf
  · intro b _ hb; rw [if_neg hb, zero_mul]
  · intro h; simp at h

lemma AC_mulVec_fvec (k : ℕ) (hk : k ≤ 20) :
    AC *ᵥ fvec k = (w ^ k + w ^ (20 - k)) • fvec k := by
  rw [AC_eq, Matrix.add_mulVec, S_mulVec_fvec, pow_mulVec (S_mulVec_fvec k) 19,
    w_pow_nineteen k hk, add_smul]

/-! ## The annihilating polynomial -/

/-- The polynomial `∏ (X - (wᵏ + w⁻ᵏ))`, whose roots are the claimed eigenvalues. -/
noncomputable def pt : ℂ[X] := ∏ k ∈ range 20, (X - C (w ^ k + w ^ (20 - k)))

/-- The composition `pt (X + X¹⁹)` is divisible by `X²⁰ - 1`. -/
lemma key_dvd : (X ^ 20 - 1 : ℂ[X]) ∣ pt.comp (X + X ^ 19) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set I : Ideal ℂ[X] := Ideal.span {(X ^ 20 - 1 : ℂ[X])} with hI
  set φ := Ideal.Quotient.mk I with hphi
  have hzero : φ (X ^ 20 - 1) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  set x := φ X with hx
  have hx20 : x ^ 20 = 1 := by
    have h : φ (X ^ 20) - φ (1 : ℂ[X]) = 0 := by rw [← map_sub]; exact hzero
    rw [map_pow, map_one, ← hx, sub_eq_zero] at h
    exact h
  have hfact : ∏ k ∈ range 20, (x - φ (C (w ^ k))) = 0 := by
    have h1 : (X ^ 20 - C 1 : ℂ[X]) = ∏ k ∈ range 20, (X - C (w ^ k * 1)) :=
      X_pow_sub_C_eq_prod w_primitive (by norm_num) (one_pow 20)
    have h2 : φ (X ^ 20 - C 1) = 0 := by rw [C_1]; exact hzero
    rw [h1, map_prod] at h2
    rw [← h2]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [mul_one, map_sub, ← hx]
  have hcomp : pt.comp (X + X ^ 19) =
      ∏ k ∈ range 20, ((X + X ^ 19) - C (w ^ k + w ^ (20 - k))) := by
    rw [pt, Polynomial.prod_comp]
    simp
  rw [hcomp, map_prod]
  have hy : ∀ k ∈ range 20, φ (C (w ^ k)) * φ (C (w ^ (20 - k))) = 1 := by
    intro k hk
    have hk' : k ≤ 20 := by have := Finset.mem_range.mp hk; omega
    rw [← map_mul, ← C_mul, ← pow_add, Nat.add_sub_cancel' hk', w_pow_twenty, C_1, map_one]
  have hstep : ∀ k ∈ range 20,
      x * (φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k))))
        = (x - φ (C (w ^ k))) * (x - φ (C (w ^ (20 - k)))) := by
    intro k hk
    have h := hy k hk
    rw [C_add, map_sub, map_add, map_add, map_pow, ← hx]
    linear_combination hx20 - h
  calc ∏ k ∈ range 20, φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k)))
      = (∏ _k ∈ range 20, x) * ∏ k ∈ range 20, φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k))) := by
        rw [Finset.prod_const, card_range, hx20, one_mul]
    _ = ∏ k ∈ range 20, (x * φ (X + X ^ 19 - C (w ^ k + w ^ (20 - k)))) := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ k ∈ range 20, ((x - φ (C (w ^ k))) * (x - φ (C (w ^ (20 - k))))) :=
        Finset.prod_congr rfl hstep
    _ = (∏ k ∈ range 20, (x - φ (C (w ^ k)))) * ∏ k ∈ range 20, (x - φ (C (w ^ (20 - k)))) := by
        rw [Finset.prod_mul_distrib]
    _ = 0 := by rw [hfact, zero_mul]

/-- `pt` annihilates the adjacency matrix. -/
lemma aeval_AC_pt : aeval AC pt = 0 := by
  obtain ⟨c, hc⟩ := key_dvd
  have h1 : aeval S (pt.comp (X + X ^ 19)) = aeval AC pt := by
    rw [Polynomial.aeval_comp]
    simp [AC_eq]
  rw [← h1, hc, map_mul]
  have : aeval S (X ^ 20 - 1 : ℂ[X]) = 0 := by
    simp [S_pow_twenty]
  rw [this, zero_mul]

/-! ## The main results -/

lemma huckel_C20_complex (μ : ℂ) :
    (∃ v : Fin 20 → ℂ, v ≠ 0 ∧ AC *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 20 ∧ μ = w ^ k + w ^ (20 - k) := by
  constructor
  · rintro ⟨v, hv, h⟩
    have h1 : (pt.eval μ) • v = 0 := by
      rw [← aeval_mulVec h pt, aeval_AC_pt, Matrix.zero_mulVec]
    have h2 : pt.eval μ = 0 := by
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hv
    rw [pt, eval_prod] at h2
    obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.mp h2
    refine ⟨k, Finset.mem_range.mp hk, ?_⟩
    simp only [eval_sub, eval_X, eval_C] at hk0
    exact sub_eq_zero.mp hk0
  · rintro ⟨k, hk, rfl⟩
    exact ⟨fvec k, fvec_ne_zero k, AC_mulVec_fvec k (by omega)⟩

lemma AC_eq_map : AC = Complex.ofRealHom.mapMatrix ((SimpleGraph.cycleGraph 20).adjMatrix ℝ) := by
  ext i j
  simp [AC, SimpleGraph.adjMatrix_apply]

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` (the Hückel matrix of the annulene C₂₀, in units of `β`, with `α = 0`) are exactly the
numbers `2 cos (2πk/20)` for `k = 0, …, 19`. -/
theorem huckel_C20 (μ : ℝ) :
    (∃ v : Fin 20 → ℝ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 20).adjMatrix ℝ *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 20 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 20) := by
  have hdet : ((SimpleGraph.cycleGraph 20).adjMatrix ℝ - μ • 1).det = 0 ↔
      (AC - (μ : ℂ) • 1).det = 0 := by
    have hmap : Complex.ofRealHom.mapMatrix
        ((SimpleGraph.cycleGraph 20).adjMatrix ℝ - μ • 1) = AC - (μ : ℂ) • 1 := by
      rw [map_sub, ← AC_eq_map]
      congr 1
      ext i j
      simp [Matrix.smul_apply, Matrix.one_apply, apply_ite (fun r : ℝ => (r : ℂ))]
    rw [← hmap, ← RingHom.map_det]
    simp
  rw [exists_eigenvector_iff_det_eq_zero, hdet, ← exists_eigenvector_iff_det_eq_zero,
    huckel_C20_complex]
  constructor
  · rintro ⟨k, hk, hval⟩
    refine ⟨k, hk, ?_⟩
    have := two_cos_eq k (by omega)
    rw [← hval] at this
    exact_mod_cast this.symm
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, two_cos_eq k (by omega)⟩

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


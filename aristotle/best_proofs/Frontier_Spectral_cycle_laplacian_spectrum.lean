import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/
noncomputable def cycleShift (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (Pi.single 1 1)

/-- The graph Laplacian of the cycle graph `C n`, modelled as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals. -/
noncomputable def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun i => if i = 0 then 2 else if i = 1 ∨ i = -1 then -1 else 0)

/-- Circulant matrices of "delta functions" multiply by adding the indices. -/
lemma circulant_single_mul_single (n : ℕ) [NeZero n] (a b : ZMod n) :
    (Matrix.circulant (Pi.single a 1) : Matrix (ZMod n) (ZMod n) ℂ) *
        Matrix.circulant (Pi.single b 1) =
      Matrix.circulant (Pi.single (a + b) 1) := by
  rw [Matrix.circulant_mul]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  simp only [eq_iff_iff]
  exact sub_eq_iff_eq_add

/-- Powers of the shift matrix are the circulants of the delta functions. -/
lemma cycleShift_pow (n : ℕ) [NeZero n] (k : ℕ) :
    (cycleShift n) ^ k = Matrix.circulant (Pi.single ((k : ZMod n)) 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, cycleShift, circulant_single_mul_single]; push_cast; ring_nf

/-- The shift matrix has order dividing `n`. -/
lemma cycleShift_pow_card (n : ℕ) [NeZero n] : (cycleShift n) ^ n = 1 := by
  rw [cycleShift_pow]
  simp

/-- For `n ≥ 3` the three residues `0`, `1`, `-1` are pairwise distinct in `ZMod n`. -/
lemma zmod_zero_one_neg_one_distinct (n : ℕ) (hn : 3 ≤ n) :
    (1 : ZMod n) ≠ 0 ∧ (1 : ZMod n) ≠ -1 ∧ (-1 : ZMod n) ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : Fact (1 < m + 1) := ⟨by omega⟩
  have h1 : (1 : ZMod (m + 1)).val = 1 := ZMod.val_one _
  have h2 : (-1 : ZMod (m + 1)).val = m := ZMod.val_neg_one m
  have h0 : (0 : ZMod (m + 1)).val = 0 := ZMod.val_zero
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    [(rw [h, h0] at h1); (rw [h, h2] at h1); (rw [h, h0] at h2)] <;> omega

/-- The Laplacian is the polynomial `2 - X - X ^ (n - 1)` evaluated at the shift matrix. -/
lemma cycleLaplacian_eq_aeval (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    cycleLaplacian n = aeval (cycleShift n) (C 2 - X - X ^ (n - 1) : ℂ[X]) := by
  obtain ⟨e1, e2, e3⟩ := zmod_zero_one_neg_one_distinct n hn
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h1 : (1 : ℕ) ≤ n := by omega
    push_cast [Nat.cast_sub h1]
    simp
  rw [show (aeval (cycleShift n) (C 2 - X - X ^ (n - 1) : ℂ[X]))
      = algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) 2 - cycleShift n - (cycleShift n) ^ (n - 1) by
    simp [map_sub]]
  rw [cycleShift_pow, hcast, cycleShift, cycleLaplacian]
  ext i j
  simp only [Matrix.circulant_apply, Matrix.sub_apply, Pi.single_apply,
    Matrix.algebraMap_matrix_apply, ← sub_eq_zero (a := i) (b := j)]
  by_cases h0 : i - j = 0 <;> by_cases h1 : i - j = 1 <;> by_cases h2 : i - j = -1 <;> simp_all

/-- If `v ^ n = 1` then the exponent of `v` only matters modulo `n`. -/
lemma pow_mod_eq {n : ℕ} {v : ℂ} (hv : v ^ n = 1) (x : ℕ) : v ^ (x % n) = v ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n, pow_add, pow_mul, hv, one_pow, one_mul]

/-- If `v ^ n = 1` then `a ↦ v ^ a.val` is an additive-to-multiplicative character of `ZMod n`. -/
lemma pow_val_add {n : ℕ} [NeZero n] {v : ℂ} (hv : v ^ n = 1) (a b : ZMod n) :
    v ^ (a + b).val = v ^ a.val * v ^ b.val := by
  rw [ZMod.val_add, pow_mod_eq hv, pow_add]

/-- Every `n`-th root of unity is an eigenvalue of the shift matrix, with the discrete Fourier
eigenvector `j ↦ z⁻¹ ^ j`. -/
lemma mem_spectrum_cycleShift (n : ℕ) [NeZero n] (hn : 2 ≤ n) {z : ℂ} (hz : z ^ n = 1) :
    z ∈ spectrum ℂ (cycleShift n) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hz; exact zero_ne_one hz
  have hwn : (z⁻¹) ^ n = 1 := by rw [inv_pow, hz, inv_one]
  set v : ZMod n → ℂ := fun j => (z⁻¹) ^ j.val with hvdef
  have hvm1 : v (-1) = z := by
    have h := pow_val_add (v := z⁻¹) hwn (-1) 1
    rw [neg_add_cancel, ZMod.val_zero, pow_zero, ZMod.val_one n, pow_one] at h
    field_simp at h
    simpa [hvdef, one_div] using h.symm
  have hshift : ∀ i : ZMod n, v (i - 1) = z * v i := by
    intro i
    have h := pow_val_add (v := z⁻¹) hwn i (-1)
    rw [show i + (-1 : ZMod n) = i - 1 by ring] at h
    calc v (i - 1) = z⁻¹ ^ i.val * z⁻¹ ^ ((-1 : ZMod n)).val := h
      _ = v i * v (-1) := rfl
      _ = z * v i := by rw [hvm1]; ring
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, ?_, ?_⟩
  · intro h
    have h0 : v 0 = 0 := by rw [h]; rfl
    simp [hvdef] at h0
  · funext i
    show ((algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) z - cycleShift n) *ᵥ v) i = 0
    simp only [cycleShift, Matrix.mulVec, dotProduct, Matrix.circulant_apply, Pi.single_apply,
      Matrix.algebraMap_matrix_apply, Matrix.sub_apply]
    have key : ∑ x, ((if i = x then z else 0) - if i - x = 1 then 1 else 0) * v x
        = z * v i - v (i - 1) := by
      simp only [sub_mul, ite_mul, zero_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      congr 1
      rw [Finset.sum_eq_single (i - 1)]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (by rw [← h]; ring)
      · intro h; exact absurd (Finset.mem_univ _) h
    have hfin : z * v i - v (i - 1) = 0 := by rw [hshift i, sub_self]
    exact key.trans hfin

/-- The spectrum of the cyclic shift matrix is the set of `n`-th roots of unity. -/
lemma spectrum_cycleShift (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    spectrum ℂ (cycleShift n) = {z : ℂ | z ^ n = 1} := by
  refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => mem_spectrum_cycleShift n hn hz)
  have h := spectrum.map_pow_of_pos (𝕜 := ℂ) (cycleShift n) (n := n) (by omega)
  rw [cycleShift_pow_card, spectrum.one_eq] at h
  have hmem : z ^ n ∈ (fun x : ℂ => x ^ n) '' spectrum ℂ (cycleShift n) := ⟨z, hz, rfl⟩
  rw [← h] at hmem
  simpa using hmem

/-- The `n`-th roots of unity in `ℂ` are exactly the numbers `exp (2 π i k / n)`, `k < n`. -/
lemma rootsOfUnity_eq_image (n : ℕ) (hn : n ≠ 0) :
    {z : ℂ | z ^ n = 1} =
      (fun k : ℕ => Complex.exp (2 * Real.pi * Complex.I * k / n)) '' (Finset.range n : Set ℕ) := by
  haveI : NeZero n := ⟨hn⟩
  have hprim := Complex.isPrimitiveRoot_exp n hn
  have hpow : ∀ k : ℕ, Complex.exp (2 * Real.pi * Complex.I / n) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
    intro k
    rw [← Complex.exp_nat_mul]
    ring_nf
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · intro hz
    obtain ⟨i, hi, hie⟩ := hprim.eq_pow_of_pow_eq_one hz
    exact ⟨i, hi, by rw [← hpow i, hie]⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have h : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    push_cast
    ring

/-- The value of the symbol `2 - X - X ^ (n - 1)` at the `n`-th root of unity `exp (2 π i k / n)`
is the real number `2 - 2 cos (2 π k / n)`. -/
lemma eval_at_root (n k : ℕ) (hn : 1 ≤ n) :
    eval (Complex.exp (2 * Real.pi * Complex.I * k / n)) (C 2 - X - X ^ (n - 1) : ℂ[X]) =
      ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / n) with hzdef
  have hzn : z ^ n = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨k, ?_⟩
    have h : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
    push_cast
    ring
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hpow : z ^ (n - 1) = z⁻¹ := by
    have h : z ^ (n - 1) * z = 1 := by rw [← pow_succ, Nat.sub_add_cancel hn, hzn]
    field_simp at h ⊢
    linear_combination h
  set t : ℝ := 2 * Real.pi * k / n with ht
  have hzt : z = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [hzdef, ht]; push_cast; ring_nf
  simp only [eval_sub, eval_pow, eval_C, eval_X]
  rw [hpow, hzt, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos, show -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I by ring]
  ring

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3` the eigenvalues of the graph Laplacian of
the cycle graph `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`.

The instance argument `[NeZero n]` is implied by `3 ≤ n`; it appears in the statement only so
that the index type `ZMod n` of the matrix is finite. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Set ℕ) := by
  have hn0 : n ≠ 0 := by omega
  have hspec : spectrum ℂ (cycleShift n) = {z : ℂ | z ^ n = 1} :=
    spectrum_cycleShift n (by omega)
  have hne : (spectrum ℂ (cycleShift n)).Nonempty := by
    refine ⟨1, ?_⟩
    rw [hspec]
    simp
  rw [cycleLaplacian_eq_aeval n hn, spectrum.map_polynomial_aeval_of_nonempty _ _ hne, hspec,
    rootsOfUnity_eq_image n hn0, Set.image_image]
  refine Set.image_congr ?_
  intro k _
  exact eval_at_root n k (by omega)

end Frontier.Spectral


/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command; the module docstring below
-- repeats the header verbatim.)
import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod n`: `shiftM n a i j = 1` exactly when `i - j = a`. -/
def shiftM (n : ℕ) [NeZero n] (a : ZMod n) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun x => if x = a then 1 else 0)

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.circulant (fun x => if x = 0 then (2 : ℂ) else if x = 1 ∨ x = -1 then -1 else 0)

section Shift

variable {n : ℕ} [NeZero n]

lemma shiftM_apply (a i j : ZMod n) : shiftM n a i j = if i - j = a then 1 else 0 := rfl

lemma cycleLaplacian_apply (i j : ZMod n) :
    cycleLaplacian n i j =
      if i - j = 0 then (2 : ℂ) else if i - j = 1 ∨ i - j = -1 then -1 else 0 := rfl

lemma shiftM_mulVec (a : ZMod n) (v : ZMod n → ℂ) (i : ZMod n) :
    (shiftM n a *ᵥ v) i = v (i - a) := by
  have hcond : ∀ j : ZMod n, (i - j = a) = (j = i - a) := by
    intro j
    apply propext
    constructor <;> intro h <;> linear_combination -h
  simp only [Matrix.mulVec, dotProduct, shiftM_apply, hcond, ite_mul, one_mul, zero_mul]
  exact (Finset.sum_ite_eq' Finset.univ (i - a) v).trans (by simp)

lemma shiftM_mul (a b : ZMod n) : shiftM n a * shiftM n b = shiftM n (a + b) := by
  ext i j
  have h1 : (shiftM n a * shiftM n b) i j = (shiftM n a *ᵥ (fun k => shiftM n b k j)) i := rfl
  rw [h1, shiftM_mulVec, shiftM_apply, shiftM_apply]
  exact if_congr (by constructor <;> intro h <;> linear_combination h) rfl rfl

lemma shiftM_zero : shiftM n 0 = 1 := by
  ext i j
  rw [shiftM_apply, Matrix.one_apply]
  exact if_congr sub_eq_zero rfl rfl

lemma shiftM_neg_one_pow (m : ℕ) : (shiftM n (-1)) ^ m = shiftM n (-(m : ZMod n)) := by
  induction m with
  | zero => simpa using (shiftM_zero (n := n)).symm
  | succ m ih =>
      rw [pow_succ, ih, shiftM_mul]
      congr 1
      push_cast
      ring

end Shift

section Distinct

variable {n : ℕ} [NeZero n]

/-- For `3 ≤ n`, `1 ≠ 0` in `ZMod n`. -/
lemma one_ne_zero_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  intro h
  have h1 : (1 : ZMod n).val = 1 := ZMod.val_one n
  rw [h, ZMod.val_zero] at h1
  exact absurd h1 (by norm_num)

/-- For `3 ≤ n`, `1 ≠ -1` in `ZMod n`. -/
lemma one_ne_neg_one_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := by
  intro h
  have h3 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h
  have h4 : (((2 : ℕ) : ZMod n)).val = 2 := ZMod.val_cast_of_lt (by omega)
  rw [h3, ZMod.val_zero] at h4
  exact absurd h4 (by norm_num)

/-- The entrywise identity behind `cycleLaplacian = 2·1 - S - S⁻¹`. -/
lemma laplacian_entry_identity (h10 : (1 : ZMod n) ≠ 0) (h1n : (1 : ZMod n) ≠ -1)
    (d : ZMod n) :
    (2 : ℂ) * (if d = 0 then 1 else 0) - (if d = -1 then 1 else 0) - (if d = 1 then 1 else 0)
      = if d = 0 then (2 : ℂ) else if d = 1 ∨ d = -1 then -1 else 0 := by
  have h0n : (0 : ZMod n) ≠ -1 := fun h => h10 (by linear_combination h)
  by_cases h0 : d = 0
  · subst h0
    simp [Ne.symm h10, h0n]
  · by_cases h1 : d = 1
    · subst h1
      simp [h10, h1n]
    · by_cases hm : d = -1
      · subst hm
        simp [h0, h1]
      · simp [h0, h1, hm]

/-- The cycle Laplacian is the polynomial `2 - X - X^(n-1)` evaluated at the cyclic shift. -/
lemma cycleLaplacian_eq_aeval (hn : 3 ≤ n) :
    (Polynomial.aeval (shiftM n (-1))) ((C 2 - X - X ^ (n - 1) : ℂ[X])) = cycleLaplacian n := by
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h : ((n - 1 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) - ((1 : ℕ) : ZMod n) := by
      rw [← Nat.cast_sub (by omega)]
    rw [h, ZMod.natCast_self]
    simp
  rw [map_sub, map_sub, aeval_C, map_pow, aeval_X, shiftM_neg_one_pow, hcast, neg_neg]
  have h10 : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod hn
  have h1n : (1 : ZMod n) ≠ -1 := one_ne_neg_one_zmod hn
  ext i j
  have hij : (i = j) ↔ (i - j = 0) := sub_eq_zero.symm
  simp only [Matrix.sub_apply, shiftM_apply, cycleLaplacian_apply,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hij]
  exact laplacian_entry_identity h10 h1n (i - j)

end Distinct

section Eigen

variable {n : ℕ} [NeZero n]

/-- If `M *ᵥ v = μ • v` for some nonzero `v`, then `μ` lies in the spectrum of `M`. -/
lemma mem_spectrum_of_mulVec_eq (M : Matrix (ZMod n) (ZMod n) ℂ) (mu : ℂ) (v : ZMod n → ℂ)
    (hv : v ≠ 0) (h : M *ᵥ v = mu • v) : mu ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  have halg : (algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ)) mu = mu • (1 : Matrix _ _ ℂ) :=
    Algebra.algebraMap_eq_smul_one mu
  rw [Matrix.sub_mulVec, h, halg, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

/-- Every `n`-th root of unity is an eigenvalue of the cyclic shift, with the discrete
Fourier eigenvector `j ↦ z ^ j`. -/
lemma shiftM_neg_one_eigen (hn : 3 ≤ n) (z : ℂ) (hz : z ^ n = 1) :
    z ∈ spectrum ℂ (shiftM n (-1)) := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  set v : ZMod n → ℂ := fun j => z ^ j.val with hv
  have hmod : ∀ m : ℕ, z ^ (m % n) = z ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, hz, one_pow, one_mul]
  have hvne : v ≠ 0 := by
    intro hc
    have h0 : v 0 = 0 := by rw [hc]; rfl
    simp [hv, ZMod.val_zero] at h0
  refine mem_spectrum_of_mulVec_eq _ z v hvne ?_
  funext i
  rw [shiftM_mulVec, sub_neg_eq_add]
  have hval : (i + 1 : ZMod n).val = (i.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one]
  simp only [hv, Pi.smul_apply, smul_eq_mul]
  rw [hval, hmod, pow_succ]
  ring

end Eigen

/-- For `z = exp (2πi/n)`, the value `2 - z^k - (z^k)^(n-1)` equals `2 - 2 cos (2πk/n)`. -/
lemma eval_at_root (n : ℕ) [NeZero n] (hn : 1 ≤ n) (k : ℕ) :
    (2 : ℂ) - (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
        - ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k) ^ (n - 1)
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).2 (by omega : n ≠ 0)
  set theta : ℝ := 2 * Real.pi * k / n with htheta
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hzdef
  have hzn : z ^ n = 1 := (Complex.isPrimitiveRoot_exp n (by omega)).pow_eq_one
  have hzk : z ^ k = Complex.exp ((theta : ℂ) * Complex.I) := by
    rw [hzdef, ← Complex.exp_nat_mul]
    congr 1
    rw [htheta]
    push_cast
    field_simp
    ring
  have hzkn : (z ^ k) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hzn, one_pow]
  have h1 : (z ^ k) ^ (n - 1) * (z ^ k) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, hzkn]
  have hinv : (z ^ k) ^ (n - 1) = (z ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hinv, hzk, ← Complex.exp_neg]
  have hcos : Complex.exp ((theta : ℂ) * Complex.I) + Complex.exp (-((theta : ℂ) * Complex.I))
      = 2 * Complex.cos (theta : ℂ) := by
    have h := Complex.two_cos (theta : ℂ)
    rw [h]
    ring_nf
  have hc2 : Complex.cos ((theta : ℝ) : ℂ) = ((Real.cos theta : ℝ) : ℂ) :=
    (Complex.ofReal_cos theta).symm
  push_cast
  linear_combination -hcos - 2 * hc2

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3`, the eigenvalues of the graph Laplacian
of the cycle graph `C n` — modelled as the `n × n` circulant matrix with `2` on the diagonal
and `-1` on the two cyclic off-diagonals — are exactly the numbers `2 - 2 cos (2πk/n)`
for `k ∈ Finset.range n`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      (fun k : ℕ => ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) ''
        (Finset.range n : Finset ℕ) := by
  classical
  set S : Matrix (ZMod n) (ZMod n) ℂ := shiftM n (-1) with hS
  set p : ℂ[X] := C 2 - X - X ^ (n - 1) with hp
  have hne : (spectrum ℂ S).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ S
  have hLp : cycleLaplacian n = (Polynomial.aeval S) p := (cycleLaplacian_eq_aeval hn).symm
  rw [hLp, spectrum.map_polynomial_aeval_of_nonempty S p hne]
  -- the spectrum of the shift is contained in the set of `n`-th roots of unity
  have hroot : ∀ z ∈ spectrum ℂ S, z ^ n = 1 := by
    intro z hz
    have hsub := spectrum.subset_polynomial_aeval S (X ^ n : ℂ[X])
    have hmem : z ^ n ∈ spectrum ℂ ((Polynomial.aeval S) (X ^ n : ℂ[X])) :=
      hsub ⟨z, hz, by simp⟩
    have hSn : (Polynomial.aeval S) (X ^ n : ℂ[X]) = 1 := by
      rw [map_pow, aeval_X, hS, shiftM_neg_one_pow, ZMod.natCast_self, neg_zero, shiftM_zero]
    rw [hSn, spectrum.one_eq] at hmem
    simpa using hmem
  set w : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hw
  have hprim : IsPrimitiveRoot w n := Complex.isPrimitiveRoot_exp n (by omega)
  have heval : ∀ z : ℂ, eval z p = 2 - z - z ^ (n - 1) := by
    intro z; simp [hp]
  ext mu
  simp only [Set.mem_image, Finset.coe_range, Set.mem_Iio]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hprim.eq_pow_of_pow_eq_one (hroot z hz)
    exact ⟨k, hk, by rw [heval]; exact eval_at_root n (by omega) k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨w ^ k, ?_, ?_⟩
    · refine shiftM_neg_one_eigen hn _ ?_
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    · rw [heval]
      exact eval_at_root n (by omega) k

end Frontier.Spectral


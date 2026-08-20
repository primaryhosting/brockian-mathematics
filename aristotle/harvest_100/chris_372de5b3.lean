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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/
def cycShift : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The graph Laplacian of the cycle `C n`, as the circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/
def cycleLaplacian : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if i = j then 2 else if i = j + 1 ∨ j = i + 1 then -1 else 0

/-- The `k`-th discrete Fourier frequency `exp (2πik/n)`. -/
noncomputable def zeta (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k / n)

section Shift

lemma cycShift_pow (m : ℕ) :
    (cycShift n) ^ m = Matrix.of fun i j => if j = i + (m : ZMod n) then 1 else 0 := by
  induction m with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ m ih =>
      ext i j
      rw [pow_succ, ih]
      simp only [Matrix.mul_apply, Matrix.of_apply, cycShift, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      push_cast
      rw [add_assoc]

lemma cycShift_pow_card : (cycShift n) ^ n = 1 := by
  ext i j
  rw [cycShift_pow]
  simp [Matrix.one_apply, eq_comm]

lemma cycShift_mulVec (v : ZMod n → ℂ) (i : ZMod n) : (cycShift n *ᵥ v) i = v (i + 1) := by
  simp [cycShift, Matrix.mulVec, dotProduct]

end Shift

section Spectrum

lemma mem_spectrum_iff_exists_eigenvector (M : Matrix (ZMod n) (ZMod n) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : ZMod n → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have key : ∀ v : ZMod n → ℂ,
      (algebraMap ℂ (Matrix (ZMod n) (ZMod n) ℂ) μ - M) *ᵥ v = μ • v - M *ᵥ v := by
    intro v
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, sub_eq_zero] at h; exact h.symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, sub_eq_zero, h]⟩

lemma pow_mulVec_of_eigen {M : Matrix (ZMod n) (ZMod n) ℂ} {v : ZMod n → ℂ} {μ : ℂ}
    (h : M *ᵥ v = μ • v) (m : ℕ) : M ^ m *ᵥ v = μ ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ,
        mul_comm]

end Spectrum

section RootsOfUnity

omit [NeZero n] in
lemma pow_mod_eq {z : ℂ} (hz : z ^ n = 1) (a : ℕ) : z ^ (a % n) = z ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

omit [NeZero n] in
lemma pow_eq_pow_of_natCast_eq {z : ℂ} (hz : z ^ n = 1) {a b : ℕ}
    (hab : (a : ZMod n) = (b : ZMod n)) : z ^ a = z ^ b := by
  have h : a % n = b % n := (ZMod.natCast_eq_natCast_iff' a b n).mp hab
  rw [← pow_mod_eq n hz a, ← pow_mod_eq n hz b, h]

lemma spectrum_cycShift : spectrum ℂ (cycShift n) = {z : ℂ | z ^ n = 1} := by
  ext z
  rw [mem_spectrum_iff_exists_eigenvector]
  constructor
  · rintro ⟨v, hv, h⟩
    have hpow := pow_mulVec_of_eigen n h n
    rw [cycShift_pow_card, Matrix.one_mulVec] at hpow
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have h2 := congrFun hpow i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2 hi
    have : (z ^ n - 1) * v i = 0 := by rw [sub_mul, one_mul, ← h2]; ring
    rcases mul_eq_zero.mp this with h3 | h3
    · simpa [sub_eq_zero] using h3
    · exact absurd h3 hi
  · intro hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨fun i => z ^ (i.val), ?_, ?_⟩
    · intro h
      have h0 := congrFun h (0 : ZMod n)
      simp only [ZMod.val_zero, pow_zero, Pi.zero_apply] at h0
      exact one_ne_zero h0
    · funext i
      rw [cycShift_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      have : z ^ ((i + 1).val) = z ^ (i.val + 1) := by
        refine pow_eq_pow_of_natCast_eq n hz ?_
        push_cast [ZMod.natCast_val, ZMod.cast_id]
        ring
      rw [this, pow_succ, mul_comm]

lemma zeta_pow_card (k : ℕ) : (zeta n k) ^ n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [zeta, ← Complex.exp_nat_mul]
  have : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * k / n) = (k : ℤ) * (2 * Real.pi * Complex.I) := by
    field_simp
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma exists_zeta_eq {z : ℂ} (hz : z ^ n = 1) : ∃ k < n, z = zeta n k := by
  obtain ⟨k, hk, hkz⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨k, hk, ?_⟩
  rw [← hkz, zeta, ← Complex.exp_nat_mul]
  congr 1
  ring

end RootsOfUnity

section Laplacian

omit [NeZero n] in
lemma one_ne_zero_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  intro h
  have : ((1 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 1 n).mp this
  have := Nat.le_of_dvd Nat.one_pos hd
  omega

omit [NeZero n] in
lemma two_ne_zero_zmod (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 2 n).mp this
  have := Nat.le_of_dvd (by norm_num) hd
  omega

lemma cycleLaplacian_eq_aeval (hn : 3 ≤ n) :
    cycleLaplacian n = aeval (cycShift n) ((C 2 - X - X ^ (n - 1) : ℂ[X])) := by
  have h1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
      have : ((n - 1 : ℕ) : ZMod n) + ((1 : ℕ) : ZMod n) = ((n : ℕ) : ZMod n) := by
        rw [← Nat.cast_add]
        congr 1
        omega
      simpa [ZMod.natCast_self] using this
    linear_combination this
  have hone : (1 : ZMod n) ≠ 0 := one_ne_zero_zmod n hn
  have htwo : (2 : ZMod n) ≠ 0 := two_ne_zero_zmod n hn
  have e1 : ∀ a : ZMod n, ¬ (a = a + 1) := by
    intro a h; exact hone (by linear_combination -h)
  have e2 : ∀ a : ZMod n, ¬ (a = a + -1) := by
    intro a h; exact hone (by linear_combination h)
  ext i j
  have hS : cycShift n i j = if j = i + 1 then (1 : ℂ) else 0 := rfl
  have hSp : (cycShift n ^ (n - 1)) i j = if j = i + -1 then (1 : ℂ) else 0 := by
    rw [cycShift_pow, Matrix.of_apply, h1]
  have hL : cycleLaplacian n i j
      = if i = j then (2 : ℂ) else if i = j + 1 ∨ j = i + 1 then -1 else 0 := rfl
  have hR : (aeval (cycShift n) ((C 2 - X - X ^ (n - 1) : ℂ[X]))) i j
      = (if i = j then (2 : ℂ) else 0) - (if j = i + 1 then 1 else 0)
        - (if j = i + -1 then 1 else 0) := by
    simp only [map_sub, aeval_C, map_pow, aeval_X, Matrix.sub_apply, hS, hSp,
      Matrix.algebraMap_matrix_apply, Algebra.algebraMap_self_apply]
  rw [hL, hR]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl, if_neg (e1 i), if_neg (e2 i)]
    ring
  · rw [if_neg hij, if_neg hij]
    by_cases hA : j = i + 1
    · have hB : ¬ (j = i + -1) := by
        intro h
        apply htwo
        rw [hA] at h
        linear_combination h
      rw [if_pos hA, if_neg hB, if_pos (Or.inr hA)]
      ring
    · by_cases hD : j = i + -1
      · have hE : i = j + 1 := by rw [hD]; ring
        rw [if_neg hA, if_pos hD, if_pos (Or.inl hE)]
        ring
      · have hF : ¬ (i = j + 1 ∨ j = i + 1) := by
          rintro (h | h)
          · exact hD (by rw [h]; ring)
          · exact hA h
        rw [if_neg hA, if_neg hD, if_neg hF]
        ring

end Laplacian

/-- For `n ≥ 3` the spectrum of the Laplacian of the cycle graph `C n` is exactly
`{2 - 2 cos (2πk/n) : k ∈ range n}`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n) =
      {z : ℂ | ∃ k ∈ Finset.range n,
        z = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)} := by
  have hnonempty : (spectrum ℂ (cycShift n)).Nonempty := by
    refine ⟨1, ?_⟩
    rw [spectrum_cycShift]
    simp
  have heval : ∀ k : ℕ, eval (zeta n k) ((C 2 - X - X ^ (n - 1) : ℂ[X]))
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
    intro k
    have hz0 : zeta n k ≠ 0 := by rw [zeta]; exact Complex.exp_ne_zero _
    have hinv : (zeta n k) ^ (n - 1) = (zeta n k)⁻¹ := by
      have hnn : n - 1 + 1 = n := by omega
      field_simp
      rw [← pow_succ, hnn, zeta_pow_card]
    have hzeq : zeta n k = Complex.exp ((2 * Real.pi * k / n : ℝ) * Complex.I) := by
      rw [zeta]
      congr 1
      push_cast
      ring
    have hsum : zeta n k + (zeta n k)⁻¹ = 2 * ((Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
      rw [hzeq, ← Complex.exp_neg, ← neg_mul, Complex.ofReal_cos, ← Complex.two_cos]
    simp only [eval_sub, eval_C, eval_X, eval_pow, hinv, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    linear_combination -hsum
  rw [cycleLaplacian_eq_aeval n hn,
    spectrum.map_polynomial_aeval_of_nonempty _ _ hnonempty, spectrum_cycShift]
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, Finset.mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := exists_zeta_eq n hw
    exact ⟨k, hk, heval k⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨zeta n k, zeta_pow_card n k, heval k⟩

end Frontier.Spectral


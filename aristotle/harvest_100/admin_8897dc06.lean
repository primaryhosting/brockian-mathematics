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

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/
noncomputable def cycleLaplacian (n : ℕ) : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if i = j then 2 else if i = j + 1 ∨ i = j - 1 then -1 else 0

section

variable {n : ℕ} [NeZero n]

/-- If `ζ ^ n = 1`, then `j ↦ ζ ^ j.val` is multiplicative on `ZMod n`. -/
lemma pow_val_add {ζ : ℂ} (hζ : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) n]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

lemma ne_zero_of_pow_eq_one {ζ : ℂ} (hζ : ζ ^ n = 1) : ζ ≠ 0 := by
  intro h
  rw [h, zero_pow (NeZero.ne n)] at hζ
  exact zero_ne_one hζ

omit [NeZero n] in
lemma val_one_eq (hn : 3 ≤ n) : (1 : ZMod n).val = 1 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  exact ZMod.val_one n

/-- The action of the cycle Laplacian on a vector. -/
lemma cycleLaplacian_mulVec (hn : 3 ≤ n) (v : ZMod n → ℂ) (i : ZMod n) :
    (cycleLaplacian n *ᵥ v) i = 2 * v i - v (i + 1) - v (i - 1) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    haveI : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have hc : ((2 : ℕ) : ZMod n) = 0 := by push_cast; exact h
    have h3 := ZMod.val_natCast (n := n) 2
    rw [hc, Nat.mod_eq_of_lt (show 2 < n by omega)] at h3
    simp at h3
  have hd1 : (i : ZMod n) ≠ i - 1 := fun h => h1 (by linear_combination h)
  have hd2 : (i : ZMod n) ≠ i + 1 := fun h => h1 (by linear_combination -h)
  have hd3 : (i : ZMod n) - 1 ≠ i + 1 := fun h => h2 (by linear_combination -h)
  have key : ∀ j : ZMod n, cycleLaplacian n i j =
      (if j = i then (2 : ℂ) else 0) + (if j = i + 1 then -1 else 0)
        + (if j = i - 1 then -1 else 0) := by
    intro j
    simp only [cycleLaplacian, Matrix.of_apply]
    have c0 : (i = j) ↔ (j = i) := eq_comm
    have c1 : (i = j + 1) ↔ (j = i - 1) :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    have c2 : (i = j - 1) ↔ (j = i + 1) :=
      ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
    simp only [c0, c1, c2]
    split_ifs <;> simp_all
  rw [Matrix.mulVec]
  simp only [dotProduct, key, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq' Finset.univ, Finset.mem_univ, if_true]
  ring

/-- The discrete Fourier vector attached to an `n`-th root of unity `ζ` is an eigenvector of
the cycle Laplacian, with eigenvalue `2 - ζ - ζ⁻¹`. -/
lemma mulVec_pow_val (hn : 3 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) (i : ZMod n) :
    (cycleLaplacian n *ᵥ fun j => ζ ^ j.val) i = (2 - ζ - ζ⁻¹) * ζ ^ i.val := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζ
  have hsucc : ∀ a : ZMod n, ζ ^ (a + 1).val = ζ ^ a.val * ζ := by
    intro a
    rw [pow_val_add hζ, val_one_eq hn, pow_one]
  have hpred : ζ ^ (i - 1).val = ζ ^ i.val * ζ⁻¹ := by
    have h := hsucc (i - 1)
    rw [sub_add_cancel] at h
    rw [h, mul_assoc, mul_inv_cancel₀ hζ0, mul_one]
  rw [cycleLaplacian_mulVec hn]
  rw [hsucc i, hpred]
  ring

/-- The `ζ`-Fourier component of a vector `v`: `∑_m ζ^(-m) v(j + m)`. -/
noncomputable def fourierComp (ζ : ℂ) (v : ZMod n → ℂ) (j : ZMod n) : ℂ :=
  ∑ m : ZMod n, (ζ ^ m.val)⁻¹ * v (j + m)

/-- The `ζ`-Fourier component is an eigenvector of the cyclic shift with eigenvalue `ζ`. -/
lemma fourierComp_shift (hn : 3 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) (v : ZMod n → ℂ) (j : ZMod n) :
    fourierComp ζ v (j + 1) = ζ * fourierComp ζ v j := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζ
  have hreindex : ∀ F : ZMod n → ℂ, ∑ m : ZMod n, F m = ∑ m : ZMod n, F (m + 1) :=
    fun F => (Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) _ _ (fun _ => rfl)).symm
  simp only [fourierComp, Finset.mul_sum]
  rw [hreindex fun m => ζ * ((ζ ^ m.val)⁻¹ * v (j + m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hval : ζ ^ (m + 1).val = ζ ^ m.val * ζ := by
    rw [pow_val_add hζ, val_one_eq hn, pow_one]
  have hjm : j + 1 + m = j + m + 1 := by ring
  rw [hval, hjm]
  have hne : ζ ^ m.val ≠ 0 := pow_ne_zero _ hζ0
  field_simp
  rw [add_assoc]

/-- Taking Fourier components preserves the eigenvector equation for the Laplacian. -/
lemma fourierComp_mulVec (hn : 3 ≤ n) {ζ μ : ℂ} (v : ZMod n → ℂ)
    (hv : cycleLaplacian n *ᵥ v = μ • v) (j : ZMod n) :
    (cycleLaplacian n *ᵥ fourierComp ζ v) j = μ * fourierComp ζ v j := by
  rw [cycleLaplacian_mulVec hn]
  simp only [fourierComp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := congrFun hv (j + m)
  rw [cycleLaplacian_mulVec hn] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have e1 : j + 1 + m = j + m + 1 := by ring
  have e2 : j - 1 + m = j + m - 1 := by ring
  rw [e1, e2]
  linear_combination (ζ ^ m.val)⁻¹ * h

/-- The Fourier components over all `n`-th roots of unity reconstruct the vector. -/
lemma sum_fourierComp (v : ZMod n → ℂ) (j : ZMod n) :
    ∑ k ∈ Finset.range n, fourierComp (Complex.exp (2 * Real.pi * I / n) ^ k) v j
      = (n : ℂ) * v j := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / n)) n :=
    Complex.isPrimitiveRoot_exp n (NeZero.ne n)
  set ω := Complex.exp (2 * Real.pi * I / n) with hωdef
  have hωn : ω ^ n = 1 := hprim.pow_eq_one
  simp only [fourierComp]
  rw [Finset.sum_comm]
  have key : ∀ m : ZMod n, (∑ k ∈ Finset.range n, ((ω ^ k) ^ m.val)⁻¹ * v (j + m))
      = if m = 0 then (n : ℂ) * v j else 0 := by
    intro m
    rw [← Finset.sum_mul]
    have hrw : ∀ k : ℕ, ((ω ^ k) ^ m.val)⁻¹ = ((ω ^ m.val)⁻¹) ^ k := by
      intro k; rw [← pow_mul, mul_comm k m.val, pow_mul, inv_pow]
    simp only [hrw]
    by_cases hm : m = 0
    · subst hm; simp
    · have hmv : m.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hm
      have hmlt : m.val < n := ZMod.val_lt m
      have hne1 : ω ^ m.val ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hmv hmlt
      have hinv1 : (ω ^ m.val)⁻¹ ≠ 1 := fun h => hne1 (inv_eq_one.mp h)
      rw [geom_sum_eq hinv1]
      have hp : ((ω ^ m.val)⁻¹) ^ n = 1 := by
        rw [inv_pow, ← pow_mul, mul_comm m.val n, pow_mul, hωn, one_pow, inv_one]
      rw [hp]
      simp [hm]
  rw [Finset.sum_congr rfl fun m _ => key m]
  simp

end

lemma two_sub_exp_sub_inv (n k : ℕ) :
    (2 : ℂ) - Complex.exp (2 * Real.pi * I * k / n) - (Complex.exp (2 * Real.pi * I * k / n))⁻¹
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / n with hθ
  have hexp : (2 * (Real.pi : ℂ) * I * k / n) = (θ : ℂ) * I := by
    rw [hθ]; push_cast; ring
  have hc : Complex.cos (θ : ℂ) = (Complex.exp ((θ : ℂ) * I) + Complex.exp (-(θ : ℂ) * I)) / 2 := by
    rw [Complex.cos]
  have hinv : (Complex.exp ((θ : ℂ) * I))⁻¹ = Complex.exp (-(θ : ℂ) * I) := by
    rw [← Complex.exp_neg]
    congr 1
    ring
  rw [hexp, hinv]
  push_cast [Complex.ofReal_cos]
  rw [hc]
  ring

/-- **Spectrum of the cycle Laplacian.** For `n ≥ 3` the eigenvalues of the graph Laplacian of
the cycle `C n` are exactly `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
theorem cycle_laplacian_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    {μ : ℂ | ∃ v : ZMod n → ℂ, v ≠ 0 ∧ cycleLaplacian n *ᵥ v = μ • v}
      = {μ : ℂ | ∃ k ∈ Finset.range n,
          μ = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)} := by
  have hω : Complex.exp (2 * Real.pi * I / n) ^ n = 1 :=
    (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).pow_eq_one
  have hpow : ∀ k : ℕ, Complex.exp (2 * Real.pi * I / n) ^ k
      = Complex.exp (2 * Real.pi * I * k / n) := by
    intro k
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hζn : ∀ k : ℕ, (Complex.exp (2 * Real.pi * I / n) ^ k) ^ n = 1 := by
    intro k
    rw [← pow_mul, mul_comm k n, pow_mul, hω, one_pow]
  ext μ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv0, hv⟩
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv0 (funext h)
    have hsum := sum_fourierComp v j
    have hne : ∑ k ∈ Finset.range n,
        fourierComp (Complex.exp (2 * Real.pi * I / n) ^ k) v j ≠ 0 := by
      rw [hsum]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) hj
    obtain ⟨k, hk, hwk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨k, hk, ?_⟩
    obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * Real.pi * I / n) ^ k := ⟨_, rfl⟩
    rw [← hζdef] at hwk
    have hζ1 : ζ ^ n = 1 := by rw [hζdef]; exact hζn k
    have hζ0 : ζ ≠ 0 := ne_zero_of_pow_eq_one hζ1
    have hshift : fourierComp ζ v (j + 1) = ζ * fourierComp ζ v j :=
      fourierComp_shift hn hζ1 v j
    have hpred : fourierComp ζ v (j - 1) = ζ⁻¹ * fourierComp ζ v j := by
      have h := fourierComp_shift hn hζ1 v (j - 1)
      rw [sub_add_cancel] at h
      rw [h, ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
    have heig := fourierComp_mulVec hn (ζ := ζ) v hv j
    rw [cycleLaplacian_mulVec hn, hshift, hpred] at heig
    have hcancel : (2 - ζ - ζ⁻¹) * fourierComp ζ v j = μ * fourierComp ζ v j := by
      linear_combination heig
    have hμ : μ = 2 - ζ - ζ⁻¹ := (mul_right_cancel₀ hwk hcancel).symm
    rw [hμ, hζdef, hpow k]
    exact two_sub_exp_sub_inv n k
  · rintro ⟨k, -, rfl⟩
    obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = Complex.exp (2 * Real.pi * I / n) ^ k := ⟨_, rfl⟩
    have hζ1 : ζ ^ n = 1 := by rw [hζdef]; exact hζn k
    refine ⟨fun j => ζ ^ j.val, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp only [ZMod.val_zero, pow_zero, Pi.zero_apply] at h0
      exact one_ne_zero h0
    · funext i
      rw [mulVec_pow_val hn hζ1 i]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hζdef, hpow k, two_sub_exp_sub_inv n k]

/-- Over `ℂ`, membership in the spectrum of a matrix is the existence of an eigenvector. -/
lemma mem_spectrum_iff_exists_eigenvector {m : Type} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ M ↔ ∃ v : m → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  have hone : ∀ v : m → ℂ, ((μ • 1 : Matrix m m ℂ)) *ᵥ v = μ • v := by
    intro v; rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, hone] at hv
    exact ⟨v, hv0, hv.symm⟩
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero, Algebra.algebraMap_eq_smul_one, hone, hv]

/-- The same result phrased with the algebraic spectrum of the matrix. -/
theorem spectrum_cycleLaplacian (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleLaplacian n)
      = {μ : ℂ | ∃ k ∈ Finset.range n,
          μ = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)} := by
  rw [← cycle_laplacian_spectrum n hn]
  ext μ
  exact mem_spectrum_iff_exists_eigenvector _ μ

end Frontier.Spectral


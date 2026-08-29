import Mathlib
/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Singular value decomposition -/

/-- Every square complex matrix admits a singular value decomposition
`M = U * diagonal s * V` with `U`, `V` unitary and `s` a nonnegative real vector. -/

theorem exists_svd (M : Matrix n n ℂ) :
    ∃ (U V : Matrix n n ℂ) (s : n → ℝ), (∀ i, 0 ≤ s i) ∧
      U ∈ Matrix.unitaryGroup n ℂ ∧ V ∈ Matrix.unitaryGroup n ℂ ∧
      M = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V := by
  classical
  have hHpsd : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hH : (Mᴴ * M).IsHermitian := hHpsd.1
  set lam := hH.eigenvalues with hlamdef
  have hlam : ∀ i, 0 ≤ lam i := hHpsd.eigenvalues_nonneg
  set V₀ : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hV₀def
  have hV₀ : V₀ ∈ Matrix.unitaryGroup n ℂ := (hH.eigenvectorUnitary).2
  have hdiag : V₀ᴴ * (Mᴴ * M) * V₀ = diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose, Function.comp] using this
  set c : n → EuclideanSpace ℂ n := fun i => WithLp.toLp 2 (fun j => (M * V₀) j i) with hc
  have hinner : ∀ i i', (inner ℂ (c i) (c i') : ℂ) = if i = i' then ((lam i : ℝ) : ℂ) else 0 := by
    intro i i'
    have h1 : (inner ℂ (c i) (c i') : ℂ) = ((M * V₀)ᴴ * (M * V₀)) i i' := by
      simp [hc, Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply,
        RCLike.inner_apply, mul_comm]
    have h2 : (M * V₀)ᴴ * (M * V₀) = diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
      rw [Matrix.conjTranspose_mul, ← hdiag]; noncomm_ring
    rw [h1, h2, Matrix.diagonal_apply]
  set s : n → ℝ := fun i => Real.sqrt (lam i) with hs
  set S : Set n := {i | lam i ≠ 0} with hS
  set u : n → EuclideanSpace ℂ n := fun i => ((s i : ℂ))⁻¹ • c i with hu
  have hsq : ∀ i, s i ^ 2 = lam i := fun i => Real.sq_sqrt (hlam i)
  have hspos : ∀ i ∈ S, 0 < s i := fun i hi =>
    Real.sqrt_pos.2 (lt_of_le_of_ne (hlam i) (Ne.symm hi))
  have horth : Orthonormal ℂ (S.restrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨i', hi'⟩
    have hsi : (0:ℝ) < s i := hspos i hi
    simp only [Set.restrict_apply, hu, inner_smul_left, inner_smul_right, hinner]
    by_cases h : i = i'
    · subst h
      have hne : ((s i : ℂ)) ≠ 0 := by exact_mod_cast hsi.ne'
      rw [← hsq i]
      push_cast
      simp only [Complex.conj_ofReal, map_inv₀, if_pos]
      field_simp
    · simp [h, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (ι := n) (finrank_euclideanSpace (𝕜 := ℂ) (ι := n))
  set U : Matrix n n ℂ := Matrix.of (fun j i => (b i) j) with hU
  have hUunit : U ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i i'
    have h : (star U * U) i i' = (inner ℂ (b i) (b i') : ℂ) := by
      simp [hU, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    rw [h, orthonormal_iff_ite.1 b.orthonormal i i']
    simp [Matrix.one_apply]
  refine ⟨U, V₀ᴴ, s, fun i => Real.sqrt_nonneg _, hUunit, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hV₀
  · have key : M * V₀ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) := by
      ext j i
      rw [Matrix.mul_diagonal]
      by_cases hi : lam i = 0
      · have hci : c i = 0 := by
          have h0 : (inner ℂ (c i) (c i) : ℂ) = 0 := by rw [hinner]; simp [hi]
          simpa using inner_self_eq_zero.1 h0
        have h0 : (M * V₀) j i = 0 := by
          have := congrFun (congrArg (fun (x : EuclideanSpace ℂ n) => x.ofLp) hci) j
          simpa [hc] using this
        have hsi0 : s i = 0 := by simp [hs, hi]
        simp [h0, hsi0]
      · have hiS : i ∈ S := hi
        have hsi : (0:ℝ) < s i := hspos i hiS
        have hbi : b i = u i := hb i hiS
        have hUji : (U : Matrix n n ℂ) j i = ((s i : ℂ))⁻¹ * (M * V₀) j i := by
          simp [hU, hbi, hu, hc]
        rw [hUji]
        have hne : ((s i : ℂ)) ≠ 0 := by exact_mod_cast hsi.ne'
        field_simp
    calc M = M * V₀ * V₀ᴴ := by
            rw [Matrix.mul_assoc]
            rw [show V₀ * V₀ᴴ = 1 from by
              simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hV₀]
            simp
      _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V₀ᴴ := by rw [key]

/-! ## Auxiliary matrix facts -/

omit [Fintype n] in
/-- A real diagonal matrix is Hermitian. -/

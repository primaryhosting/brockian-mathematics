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
lemma diagonal_real_conjTranspose (s : n → ℝ) :
    (diagonal (fun i => ((s i : ℝ) : ℂ)))ᴴ = diagonal (fun i => ((s i : ℝ) : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [RCLike.star_def]

/-- Squaring a real diagonal matrix. -/
lemma diagonal_real_sq (s : n → ℝ) :
    diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))
      = diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  ring

/-- A unitary conjugate of a nonnegative diagonal matrix is positive semidefinite. -/
lemma posSemidef_unitary_conj (U : Matrix n n ℂ) (s : n → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ).PosSemidef := by
  have h : U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ
      = (U * diagonal (fun i => ((Real.sqrt (s i) : ℝ) : ℂ))) *
        (U * diagonal (fun i => ((Real.sqrt (s i) : ℝ) : ℂ)))ᴴ := by
    rw [Matrix.conjTranspose_mul, diagonal_real_conjTranspose]
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hs i)]
  rw [h]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- The positive semidefinite square root of `U * diagonal (s ^ 2) * Uᴴ`. -/
lemma sqrt_unitary_conj (U : Matrix n n ℂ) (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (s : n → ℝ) (hs : ∀ i, 0 ≤ s i) :
    CFC.sqrt (U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ)
      = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ := by
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU
  have ha : (0 : Matrix n n ℂ) ≤ U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ :=
    (posSemidef_unitary_conj U _ (fun i => sq_nonneg (s i))).nonneg
  have hb : (0 : Matrix n n ℂ) ≤ U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ :=
    (posSemidef_unitary_conj U s hs).nonneg
  rw [CFC.sqrt_eq_iff _ _ ha hb]
  calc _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * (Uᴴ * U) *
              diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ := by noncomm_ring
    _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by
        rw [hUU]; noncomm_ring
    _ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by rw [diagonal_real_sq]

/-- If `M = U * diagonal s * V` is a singular value decomposition, then
`M * Mᴴ = U * diagonal (s ^ 2) * Uᴴ`. -/
lemma svd_mul_conjTranspose {U V : Matrix n n ℂ} (hV : V ∈ Matrix.unitaryGroup n ℂ) (s : n → ℝ) :
    (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V) *
        (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V)ᴴ
      = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
  have hVV : V * Vᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hV
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, diagonal_real_conjTranspose]
  calc _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * (V * Vᴴ) *
              diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by noncomm_ring
    _ = U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * diagonal (fun i => ((s i : ℝ) : ℂ))) * Uᴴ := by
        rw [hVV]; noncomm_ring
    _ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by rw [diagonal_real_sq]

/-- Entries of a unitary matrix have norm at most one. -/
lemma unitary_entry_norm_le_one {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) (i j : n) :
    ‖W i j‖ ≤ 1 := by
  have hWW : Wᴴ * W = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hW
  have h0 : ∑ k, Wᴴ j k * W k j = (1 : Matrix n n ℂ) j j := by
    rw [← Matrix.mul_apply, hWW]
  rw [Matrix.one_apply_eq] at h0
  have h1 : ((∑ k, ‖W k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h0]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  have h2 : (∑ k, ‖W k j‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h1
  have h3 : ‖W i j‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖W k j‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [norm_nonneg (W i j)]

/-- Polar-type factorization: if `A * Aᴴ = ρ` then `A = √ρ * V` for some unitary `V`. -/
lemma exists_unitary_factor {A ρ : Matrix n n ℂ} (h : A * Aᴴ = ρ) :
    ∃ V ∈ Matrix.unitaryGroup n ℂ, A = CFC.sqrt ρ * V := by
  obtain ⟨U, V', s, hs, hU, hV', hA⟩ := exists_svd A
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU
  have hrho : ρ = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    rw [← h, hA, svd_mul_conjTranspose hV' s]
  refine ⟨U * V', (Matrix.unitaryGroup n ℂ).mul_mem hU hV', ?_⟩
  rw [hrho, sqrt_unitary_conj U hU s hs, hA]
  calc _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * (Uᴴ * U) * V' := by rw [hUU]; noncomm_ring
    _ = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * Uᴴ * (U * V') := by noncomm_ring

/-! ## Fidelity and purifications -/

/-- The (Uhlmann) fidelity of two positive semidefinite matrices,
`F(ρ, σ) = tr √(√ρ σ √ρ)`. -/
noncomputable def fidelity (ρ σ : Matrix n n ℂ) : ℝ :=
  (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace.re

/-- A vector `ψ` of the bipartite space `H ⊗ K` (here `EuclideanSpace ℂ (n × m)`)
is a purification of `ρ` when the partial trace of `|ψ⟩⟨ψ|` over the ancilla `K` equals `ρ`. -/
def IsPurification {m : Type*} [Fintype m] (ρ : Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ (n × m)) : Prop :=
  ∀ i j, ∑ k, ψ (i, k) * (starRingEnd ℂ) (ψ (j, k)) = ρ i j

omit [DecidableEq n] in
/-- The matrix of coefficients of a purification `ψ` of `ρ` satisfies `A * Aᴴ = ρ`. -/
lemma purification_matrix {ρ : Matrix n n ℂ} {ψ : EuclideanSpace ℂ (n × n)}
    (h : IsPurification ρ ψ) :
    (Matrix.of fun i k => ψ (i, k)) * (Matrix.of fun i k => ψ (i, k))ᴴ = ρ := by
  ext i j
  rw [Matrix.mul_apply]
  simpa [Matrix.conjTranspose_apply, RCLike.star_def] using h i j

omit [DecidableEq n] in
/-- The vector of coefficients of `A` is a purification of `A * Aᴴ`. -/
lemma isPurification_toLp (A : Matrix n n ℂ) :
    IsPurification (A * Aᴴ) (WithLp.toLp 2 (fun p : n × n => A p.1 p.2)) := by
  intro i j
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply, RCLike.star_def]

omit [DecidableEq n] in
/-- The overlap of two purifications is the Hilbert-Schmidt inner product of their
coefficient matrices. -/
lemma inner_toLp_eq_trace (A B : Matrix n n ℂ) :
    (inner ℂ (WithLp.toLp 2 (fun p : n × n => A p.1 p.2) : EuclideanSpace ℂ (n × n))
      (WithLp.toLp 2 (fun p : n × n => B p.1 p.2)) : ℂ) = (Aᴴ * B).trace := by
  rw [Matrix.trace_mul_comm]
  simp [PiLp.inner_apply, RCLike.inner_apply, Matrix.trace, Matrix.mul_apply, Matrix.diag,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]

omit [Fintype n] [DecidableEq n] in
lemma toLp_coeff_self (ψ : EuclideanSpace ℂ (n × n)) :
    (WithLp.toLp 2 (fun p : n × n => (Matrix.of fun i k => ψ (i, k)) p.1 p.2)) = ψ := rfl

/-- **Uhlmann's theorem**: the fidelity `tr √(√ρ σ √ρ)` is the maximum of the overlap
`|⟪ψ, ξ⟫|` taken over all purifications `ψ` of `ρ` and `ξ` of `σ`. -/
theorem uhlmann_fidelity (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    IsGreatest {x : ℝ | ∃ ψ ξ : EuclideanSpace ℂ (n × n),
      IsPurification ρ ψ ∧ IsPurification σ ξ ∧ x = ‖(inner ℂ ψ ξ : ℂ)‖} (fidelity ρ σ) := by
  classical
  set R : Matrix n n ℂ := CFC.sqrt ρ with hRdef
  set S : Matrix n n ℂ := CFC.sqrt σ with hSdef
  have hRh : Rᴴ = R := ((CFC.sqrt_nonneg ρ).posSemidef).1
  have hSh : Sᴴ = S := ((CFC.sqrt_nonneg σ).posSemidef).1
  have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hSS : S * S = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  obtain ⟨U, V, s, hs, hU, hV, hM⟩ := exists_svd (R * S)
  have hUU : Uᴴ * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hU
  have hVV : V * Vᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hV
  -- the fidelity is the sum of the singular values of `√ρ √σ`
  have hRsigmaR : R * σ * R = U * diagonal (fun i => (((s i) ^ 2 : ℝ) : ℂ)) * Uᴴ := by
    have h1 : R * σ * R = (R * S) * (R * S)ᴴ := by
      rw [Matrix.conjTranspose_mul, hRh, hSh, ← hSS]; noncomm_ring
    rw [h1, hM, svd_mul_conjTranspose hV s]
  have hfid : fidelity ρ σ = ∑ i, s i := by
    rw [fidelity, ← hRdef, hRsigmaR, sqrt_unitary_conj U hU s hs, Matrix.trace_mul_cycle, hUU,
      Matrix.one_mul, Matrix.trace_diagonal, ← Complex.ofReal_sum, Complex.ofReal_re]
  constructor
  · -- the fidelity is attained
    refine ⟨WithLp.toLp 2 (fun p : n × n => R p.1 p.2),
      WithLp.toLp 2 (fun p : n × n => (S * (Vᴴ * Uᴴ)) p.1 p.2), ?_, ?_, ?_⟩
    · have h := isPurification_toLp R
      rwa [hRh, hRR] at h
    · have h := isPurification_toLp (S * (Vᴴ * Uᴴ))
      have hZ : (S * (Vᴴ * Uᴴ)) * (S * (Vᴴ * Uᴴ))ᴴ = σ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hSh]
        calc _ = S * (Vᴴ * (Uᴴ * U) * V) * S := by noncomm_ring
          _ = S * (Vᴴ * V) * S := by rw [hUU]; noncomm_ring
          _ = S * S := by
              rw [show Vᴴ * V = 1 from by
                simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hV]
              noncomm_ring
          _ = σ := hSS
      rwa [hZ] at h
    · rw [inner_toLp_eq_trace, hRh, hfid]
      have htr : (R * (S * (Vᴴ * Uᴴ))).trace = ∑ i, ((s i : ℝ) : ℂ) := by
        have h1 : R * (S * (Vᴴ * Uᴴ)) = (R * S) * (Vᴴ * Uᴴ) := by noncomm_ring
        rw [h1, hM]
        have h2 : U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V * (Vᴴ * Uᴴ)
            = U * diagonal (fun i => ((s i : ℝ) : ℂ)) * (V * Vᴴ) * Uᴴ := by noncomm_ring
        rw [h2, hVV, Matrix.mul_one, Matrix.trace_mul_cycle, hUU, Matrix.one_mul,
          Matrix.trace_diagonal]
      rw [htr, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun i _ => hs i)]
  · -- the fidelity is an upper bound
    rintro x ⟨ψ, ξ, hψ, hξ, rfl⟩
    set A : Matrix n n ℂ := Matrix.of fun i k => ψ (i, k) with hAdef
    set B : Matrix n n ℂ := Matrix.of fun i k => ξ (i, k) with hBdef
    have hA : A * Aᴴ = ρ := purification_matrix hψ
    have hB : B * Bᴴ = σ := purification_matrix hξ
    have hinner : (inner ℂ ψ ξ : ℂ) = (Aᴴ * B).trace := by
      rw [← toLp_coeff_self ψ, ← toLp_coeff_self ξ, inner_toLp_eq_trace]
    obtain ⟨V₁, hV₁, hAeq⟩ := exists_unitary_factor hA
    obtain ⟨V₂, hV₂, hBeq⟩ := exists_unitary_factor hB
    rw [← hRdef] at hAeq
    rw [← hSdef] at hBeq
    set W : Matrix n n ℂ := V * (V₂ * (V₁ᴴ * U)) with hWdef
    have hWunit : W ∈ Matrix.unitaryGroup n ℂ := by
      refine (Matrix.unitaryGroup n ℂ).mul_mem hV
        ((Matrix.unitaryGroup n ℂ).mul_mem hV₂ ((Matrix.unitaryGroup n ℂ).mul_mem ?_ hU))
      rw [Matrix.mem_unitaryGroup_iff]
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hV₁
    have htr : (Aᴴ * B).trace = ∑ i, ((s i : ℝ) : ℂ) * W i i := by
      have h1 : Aᴴ * B = V₁ᴴ * ((R * S) * V₂) := by
        rw [hAeq, hBeq, Matrix.conjTranspose_mul, hRh]; noncomm_ring
      rw [h1, hM]
      have h2 : V₁ᴴ * (U * diagonal (fun i => ((s i : ℝ) : ℂ)) * V * V₂)
          = V₁ᴴ * U * (diagonal (fun i => ((s i : ℝ) : ℂ)) * (V * V₂)) := by noncomm_ring
      rw [h2, Matrix.trace_mul_comm]
      have h3 : diagonal (fun i => ((s i : ℝ) : ℂ)) * (V * V₂) * (V₁ᴴ * U)
          = diagonal (fun i => ((s i : ℝ) : ℂ)) * W := by rw [hWdef]; noncomm_ring
      rw [h3]
      simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    rw [hinner, htr, hfid]
    calc ‖∑ i, ((s i : ℝ) : ℂ) * W i i‖ ≤ ∑ i, ‖((s i : ℝ) : ℂ) * W i i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, s i := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs i)]
          nlinarith [unitary_entry_norm_le_one hWunit i i, hs i, norm_nonneg (W i i)]

end QI


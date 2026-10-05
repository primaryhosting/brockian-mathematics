import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped ComplexConjugate MatrixOrder ComplexOrder

namespace QI

/-! ### Basic definitions -/

section Defs

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- A density matrix (mixed state): a positive semidefinite matrix of unit trace. -/
def IsDensityMatrix (ρ : Matrix H H ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The reduced density matrix on the system `H` of the pure state `|ψ⟩⟨ψ|` living on
`H ⊗ K`, i.e. the partial trace of `|ψ⟩⟨ψ|` over the ancilla `K`. -/
noncomputable def reducedState (ψ : H × K → ℂ) : Matrix H H ℂ :=
  Matrix.of fun i j => ∑ k, ψ (i, k) * conj (ψ (j, k))

/-- `ψ`, a vector of the composite system `H ⊗ K`, is a purification of the state `ρ` on `H`
if tracing out the ancilla `K` returns `ρ`. -/
def IsPurification (ρ : Matrix H H ℂ) (ψ : H × K → ℂ) : Prop := reducedState ψ = ρ

/-- The action `(1 ⊗ U) ψ` of a matrix `U` on the ancilla factor of `ψ`. -/
noncomputable def ancillaAct (U : Matrix K K ℂ) (ψ : H × K → ℂ) : H × K → ℂ :=
  fun p => ∑ l, U p.2 l * ψ (p.1, l)

/-- The matrix whose `(i, k)` entry is the amplitude `ψ (i, k)`. -/
def amplitudeMatrix (ψ : H × K → ℂ) : Matrix H K ℂ := Matrix.of fun i k => ψ (i, k)

omit [Fintype H] [DecidableEq H] [DecidableEq K] in
lemma reducedState_eq_mul_conjTranspose (ψ : H × K → ℂ) :
    reducedState ψ = amplitudeMatrix ψ * (amplitudeMatrix ψ)ᴴ := by
  ext i j
  simp [reducedState, amplitudeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

end Defs

/-! ### From matrices to linear maps on Euclidean space -/

section Lin

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The linear map on Euclidean space determined by a matrix. -/
noncomputable def lmap (M : Matrix K H ℂ) : EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ K :=
  Matrix.toLpLin 2 2 M

omit [DecidableEq K] in
lemma lmap_apply (M : Matrix K H ℂ) (x : EuclideanSpace ℂ H) (k : K) :
    (lmap M x) k = ∑ i, M k i * x i := by
  simp [lmap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

omit [DecidableEq K] in
lemma inner_lmap_self (A : Matrix H K ℂ) (x : EuclideanSpace ℂ H) :
    (inner ℂ (lmap Aᴴ x) (lmap Aᴴ x) : ℂ) = ∑ i, ∑ j, conj (x i) * x j * (A * Aᴴ) i j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, lmap, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.mul_apply, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul, RCLike.star_def, starRingEnd_self_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq K] in
lemma norm_lmap_eq_of_mul_conjTranspose_eq {A B : Matrix H K ℂ} (h : A * Aᴴ = B * Bᴴ)
    (x : EuclideanSpace ℂ H) : ‖lmap Aᴴ x‖ = ‖lmap Bᴴ x‖ := by
  have h1 : (inner ℂ (lmap Aᴴ x) (lmap Aᴴ x) : ℂ) = inner ℂ (lmap Bᴴ x) (lmap Bᴴ x) := by
    rw [inner_lmap_self, inner_lmap_self, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖lmap Aᴴ x‖ ^ 2 = ‖lmap Bᴴ x‖ ^ 2 := by exact_mod_cast h1
  nlinarith [norm_nonneg (lmap Aᴴ x), norm_nonneg (lmap Bᴴ x)]

end Lin

/-! ### Extending a partial isometry -/

section Isom

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Two linear maps into a finite-dimensional inner product space with the same pointwise
norms differ by a linear isometry of the target. -/
theorem exists_isometry_comp (f g : E →ₗ[ℂ] F) (hn : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ L : F →ₗᵢ[ℂ] F, ∀ x, L (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have := hn x
    rw [LinearMap.mem_ker.1 hx, norm_zero] at this
    exact LinearMap.mem_ker.2 (norm_eq_zero.1 this.symm)
  set g' := (LinearMap.ker f).liftQ g hker with hg'
  set q := f.quotKerEquivRange with hq
  set φ₀ : ↥(LinearMap.range f) →ₗ[ℂ] F := g'.comp q.symm.toLinearMap with hφ₀def
  have key : ∀ x : E, φ₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have hqx : q (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x)
    have h2 : q.symm ⟨f x, ⟨x, rfl⟩⟩ = Submodule.Quotient.mk x := by
      rw [← hqx, LinearEquiv.symm_apply_apply]
    simp [hφ₀def, h2, hg']
  have hnorm : ∀ y : ↥(LinearMap.range f), ‖φ₀ y‖ = ‖y‖ := by
    rintro ⟨y, x, rfl⟩
    rw [key x]
    simpa using (hn x).symm
  refine ⟨(⟨φ₀, hnorm⟩ : ↥(LinearMap.range f) →ₗᵢ[ℂ] F).extend, fun x => ?_⟩
  have := LinearIsometry.extend_apply (⟨φ₀, hnorm⟩ : ↥(LinearMap.range f) →ₗᵢ[ℂ] F)
      ⟨f x, ⟨x, rfl⟩⟩
  simpa [key x] using this

end Isom

/-! ### The unitary freedom in decompositions `A Aᴴ = B Bᴴ` -/

section Freedom

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The matrix of a linear isometry of `EuclideanSpace ℂ K`. -/
noncomputable def isomMatrix (L : EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ K) :
    Matrix K K ℂ := Matrix.of fun i j => (L (EuclideanSpace.single j (1 : ℂ))) i

lemma isomMatrix_mulVec (L : EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ K)
    (v : EuclideanSpace ℂ K) (i : K) : (L v) i = ∑ j, isomMatrix L i j * v j := by
  have hv : v = ∑ j, v j • (EuclideanSpace.single j (1 : ℂ)) := by
    ext k; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp [isomMatrix, mul_comm]

lemma isomMatrix_mem_unitaryGroup (L : EuclideanSpace ℂ K →ₗᵢ[ℂ] EuclideanSpace ℂ K) :
    isomMatrix L ∈ Matrix.unitaryGroup K ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k l
  have hinner := L.inner_map_map (EuclideanSpace.single k (1 : ℂ))
    (EuclideanSpace.single l (1 : ℂ))
  simp only [PiLp.inner_apply, RCLike.inner_apply] at hinner
  have hl : (star (isomMatrix L) * isomMatrix L) k l
      = ∑ i, conj (isomMatrix L i k) * isomMatrix L i l := by
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  rw [hl]
  have : ∑ i, conj (isomMatrix L i k) * isomMatrix L i l
      = ∑ i, (L (EuclideanSpace.single l (1 : ℂ))) i *
          conj ((L (EuclideanSpace.single k (1 : ℂ))) i) := by
    exact Finset.sum_congr rfl fun i _ => by simp [isomMatrix, mul_comm]
  rw [this, hinner]
  simp [EuclideanSpace.single_apply, Matrix.one_apply, eq_comm]

omit [Fintype K] [DecidableEq K] in
lemma star_eq_star_transpose (U : Matrix K K ℂ) : (star U)ᵀ = star (Uᵀ) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.transpose_apply]

lemma transpose_mem_unitaryGroup {U : Matrix K K ℂ} (h : U ∈ Matrix.unitaryGroup K ℂ) :
    Uᵀ ∈ Matrix.unitaryGroup K ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_one, star_eq_star_transpose] at h2
  exact h2

/-- **Unitary freedom**: if `A Aᴴ = B Bᴴ` then `B = A Uᵀ` for some unitary `U`. -/
theorem exists_unitary_of_mul_conjTranspose_eq {A B : Matrix H K ℂ} (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix K K ℂ, U ∈ Matrix.unitaryGroup K ℂ ∧ B = A * Uᵀ := by
  obtain ⟨L, hL⟩ := exists_isometry_comp (lmap Aᴴ) (lmap Bᴴ)
    (norm_lmap_eq_of_mul_conjTranspose_eq h)
  set U₀ := isomMatrix L with hU₀
  have hcol : ∀ (i : H) (l : K), (lmap Aᴴ (EuclideanSpace.single i (1 : ℂ))) l = Aᴴ l i := by
    intro i l
    rw [lmap_apply]
    simp [EuclideanSpace.single_apply, eq_comm]
  have hcolB : ∀ (i : H) (l : K), (lmap Bᴴ (EuclideanSpace.single i (1 : ℂ))) l = Bᴴ l i := by
    intro i l
    rw [lmap_apply]
    simp [EuclideanSpace.single_apply, eq_comm]
  have hmain : U₀ * Aᴴ = Bᴴ := by
    ext k i
    have h1 : (U₀ * Aᴴ) k i
        = ∑ l, U₀ k l * (lmap Aᴴ (EuclideanSpace.single i (1 : ℂ))) l := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [hcol i l]
    rw [h1, ← isomMatrix_mulVec L, hL, hcolB]
  refine ⟨(U₀ᴴ)ᵀ, ?_, ?_⟩
  · exact transpose_mem_unitaryGroup (Unitary.star_mem (isomMatrix_mem_unitaryGroup L))
  · have : ((U₀ᴴ)ᵀ)ᵀ = U₀ᴴ := Matrix.transpose_transpose _
    rw [this]
    have := congrArg Matrix.conjTranspose hmain
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using this.symm

end Freedom

/-! ### The main theorem -/

section Main

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
/-- The total probability carried by a purification of a unit-trace state is `1`. -/
theorem sum_normSq_of_isPurification {K : Type*} [Fintype K] [DecidableEq K]
    {ρ : Matrix H H ℂ} (hρ : ρ.trace = 1) {ψ : H × K → ℂ} (hψ : IsPurification ρ ψ) :
    ∑ p : H × K, ‖ψ p‖ ^ 2 = 1 := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    ring
  have h1 : ((∑ p : H × K, ‖ψ p‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← hρ, ← hψ]
    simp only [Matrix.trace, Matrix.diag, reducedState, Matrix.of_apply, Complex.ofReal_sum,
      Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hz _
  exact_mod_cast h1

/-- The positive square root of a mixed state `ρ`, read as a vector of `H ⊗ H`, purifies `ρ`. -/
theorem isPurification_sqrt {ρ : Matrix H H ℂ} (hpsd : ρ.PosSemidef) :
    IsPurification ρ (fun p : H × H => CFC.sqrt ρ p.1 p.2) := by
  have hsq : (CFC.sqrt ρ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ρ)
  have hmul : CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
    CFC.sqrt_mul_sqrt_self ρ (Matrix.nonneg_iff_posSemidef.mpr hpsd)
  show reducedState _ = ρ
  ext i j
  have hij : (CFC.sqrt ρ * (CFC.sqrt ρ)ᴴ) i j = ρ i j := by rw [hsq.isHermitian.eq, hmul]
  simpa [reducedState, Matrix.mul_apply, Matrix.conjTranspose_apply] using hij

/-- **Purification exists and is unique up to an isometry of the ancilla.**

For every mixed state `ρ` (a positive semidefinite matrix of unit trace) on a finite dimensional
system `H`:

* there is a pure state `ψ` of `H ⊗ H` (a unit vector, as recorded by the second conjunct)
  whose reduced state on `H` — the partial trace over the ancilla — is `ρ`;
* any two purifications `ψ`, `φ` of `ρ` sharing the same ancilla `K` are related by a
  unitary (hence isometric) transformation `U` acting on the ancilla alone. -/
theorem purification_exists (ρ : Matrix H H ℂ) (hρ : IsDensityMatrix ρ) :
    (∃ ψ : H × H → ℂ, IsPurification ρ ψ ∧ ∑ p : H × H, ‖ψ p‖ ^ 2 = 1) ∧
    (∀ {K : Type*} [Fintype K] [DecidableEq K] (ψ φ : H × K → ℂ),
      IsPurification ρ ψ → IsPurification ρ φ →
      ∃ U : Matrix K K ℂ, U ∈ Matrix.unitaryGroup K ℂ ∧ φ = ancillaAct U ψ) := by
  obtain ⟨hpsd, htr⟩ := hρ
  constructor
  · -- existence: take the positive square root of `ρ`
    exact ⟨fun p => CFC.sqrt ρ p.1 p.2, isPurification_sqrt hpsd,
      sum_normSq_of_isPurification htr (isPurification_sqrt hpsd)⟩
  · intro K _ _ ψ φ hψ hφ
    have hA : amplitudeMatrix ψ * (amplitudeMatrix ψ)ᴴ = ρ := by
      rw [← reducedState_eq_mul_conjTranspose]; exact hψ
    have hB : amplitudeMatrix φ * (amplitudeMatrix φ)ᴴ = ρ := by
      rw [← reducedState_eq_mul_conjTranspose]; exact hφ
    obtain ⟨U, hU, hBU⟩ := exists_unitary_of_mul_conjTranspose_eq (hA.trans hB.symm)
    refine ⟨U, hU, ?_⟩
    funext p
    have := congrArg (fun M => M p.1 p.2) hBU
    simpa [amplitudeMatrix, ancillaAct, Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
      using this

/-- Sanity check: the hypothesis of `purification_exists` is satisfiable. -/
example : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) := ⟨Matrix.PosSemidef.one, by simp⟩

end Main

end QI

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


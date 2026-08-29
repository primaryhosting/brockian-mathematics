import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

section Defs

variable {n m : Type*}

/-- The density matrix `|ψ⟩⟨ψ|` of a state vector `ψ` of a composite system whose
product basis is indexed by `n × m`. -/
def pureDensity (ψ : n × m → ℂ) : Matrix (n × m) (n × m) ℂ :=
  Matrix.of fun p q => ψ p * star (ψ q)

/-- The partial trace over the second (ancilla) tensor factor. -/
noncomputable def ptraceRight [Fintype m] (R : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i i' => ∑ j : m, R (i, j) (i', j)

/-- The matrix of coefficients of a vector of the composite system, i.e. the identification
of `H_A ⊗ H_B` with the space of `n × m` matrices. -/
def coeffMatrix (ψ : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i j => ψ (i, j)

/-- `ψ`, a state vector of the composite system `H_A ⊗ H_B`, is a *purification* of the
state `ρ` on `H_A` when tracing out the ancilla `H_B` from `|ψ⟩⟨ψ|` returns `ρ`. -/
def IsPurification [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) : Prop :=
  ptraceRight (pureDensity ψ) = ρ

end Defs

variable {n m : Type*}

lemma ptraceRight_pureDensity [Fintype m] (ψ : n × m → ℂ) :
    ptraceRight (pureDensity ψ) = coeffMatrix ψ * (coeffMatrix ψ)ᴴ := by
  ext i i'
  simp [ptraceRight, pureDensity, coeffMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]

lemma isPurification_iff [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) :
    IsPurification ρ ψ ↔ coeffMatrix ψ * (coeffMatrix ψ)ᴴ = ρ := by
  rw [IsPurification, ptraceRight_pureDensity]

/-- Sanity check on the definitions: the Bell state `(|00⟩ + |11⟩)/√2` is a purification of the
maximally mixed qubit state. -/
theorem bell_isPurification_maximallyMixed :
    IsPurification ((1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (fun p : Fin 2 × Fin 2 => if p.1 = p.2 then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptraceRight, pureDensity] <;>
    · field_simp
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

/-! ### The linear-algebraic core -/

/-- Two linear maps with the same pointwise norms differ by a linear isometry of the
target space. -/
lemma exists_linearIsometry_comp [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (f g : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ m) (hnorm : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ W : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m, ∀ x, W (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    simp only [LinearMap.mem_ker] at *
    have h2 := hnorm x
    rw [hx] at h2
    exact norm_eq_zero.mp (by simpa using h2.symm)
  set L₀ : (LinearMap.range f) →ₗ[ℂ] EuclideanSpace ℂ m :=
    ((LinearMap.ker f).liftQ g hker).comp (f.quotKerEquivRange.symm : (LinearMap.range f) →ₗ[ℂ] _)
    with hL₀def
  have hL₀ : ∀ x : EuclideanSpace ℂ n, L₀ ⟨f x, ⟨x, rfl⟩⟩ = g x := by
    intro x
    have h1 : f.quotKerEquivRange (Submodule.Quotient.mk x) = ⟨f x, ⟨x, rfl⟩⟩ := rfl
    simp only [hL₀def, LinearMap.comp_apply, LinearEquiv.coe_coe, ← h1,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  set L : (LinearMap.range f) →ₗᵢ[ℂ] EuclideanSpace ℂ m :=
    { toLinearMap := L₀
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hL₀ x]
        exact (hnorm x).symm } with hLdef
  refine ⟨L.extend, fun x => ?_⟩
  have hx := L.extend_apply ⟨f x, ⟨x, rfl⟩⟩
  simpa [hLdef, hL₀ x] using hx

/-- Every linear isometry of `EuclideanSpace ℂ m` is given by a unitary matrix. -/
lemma exists_unitary_of_linearIsometry [Fintype m] [DecidableEq m]
    (W : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ x : EuclideanSpace ℂ m, Matrix.toEuclideanLin U x = W x := by
  set U : Matrix m m ℂ := Matrix.toEuclideanLin.symm W.toLinearMap with hUdef
  have hWU : ∀ x : EuclideanSpace ℂ m, Matrix.toEuclideanLin U x = W x := by
    intro x; simp [hUdef]
  have hcol : ∀ j i, (W (EuclideanSpace.single j (1:ℂ))).ofLp i = U i j := by
    intro j i
    rw [← hWU (EuclideanSpace.single j (1:ℂ))]
    simp
  refine ⟨U, ?_, hWU⟩
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have key : (inner ℂ (W (EuclideanSpace.single i (1:ℂ))) (W (EuclideanSpace.single j (1:ℂ))) : ℂ)
      = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) :=
    W.inner_map_map _ _
  rw [PiLp.inner_apply] at key
  simp only [hcol, RCLike.inner_apply] at key
  rw [Matrix.mul_apply]
  have key2 : ∑ x, (star U) i x * U x j
      = inner ℂ (EuclideanSpace.single i (1:ℂ)) (EuclideanSpace.single j (1:ℂ)) := by
    rw [← key]
    exact Finset.sum_congr rfl fun x _ => by simp [Matrix.star_apply, RCLike.star_def, mul_comm]
  rw [key2]
  simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, Matrix.one_apply]

lemma norm_toEuclideanLin_conjTranspose_eq [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A B : Matrix n m ℂ} (h : A * Aᴴ = B * Bᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Bᴴ x‖ := by
  have gen : ∀ M : Matrix n m ℂ,
      (inner ℂ (Matrix.toEuclideanLin Mᴴ x) (Matrix.toEuclideanLin Mᴴ x) : ℂ)
        = inner ℂ x (Matrix.toEuclideanLin (M * Mᴴ) x) := by
    intro M
    have hadj : (Matrix.toEuclideanLin Mᴴ).adjoint = Matrix.toEuclideanLin M := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; simp
    have hmul : Matrix.toEuclideanLin M (Matrix.toEuclideanLin Mᴴ x)
        = Matrix.toEuclideanLin (M * Mᴴ) x := by
      simp
    rw [← hmul, ← hadj, LinearMap.adjoint_inner_right]
  have key : (inner ℂ (Matrix.toEuclideanLin Aᴴ x) (Matrix.toEuclideanLin Aᴴ x) : ℂ)
      = inner ℂ (Matrix.toEuclideanLin Bᴴ x) (Matrix.toEuclideanLin Bᴴ x) := by
    rw [gen A, gen B, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have key' : ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Bᴴ x‖ ^ 2 := by
    exact_mod_cast key
  nlinarith [norm_nonneg (Matrix.toEuclideanLin Aᴴ x), norm_nonneg (Matrix.toEuclideanLin Bᴴ x)]

/-- If `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U`. -/
theorem exists_unitary_mul_eq [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A B : Matrix n m ℂ} (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧ B = A * U := by
  obtain ⟨W, hW⟩ := exists_linearIsometry_comp (Matrix.toEuclideanLin Aᴴ)
    (Matrix.toEuclideanLin Bᴴ) (norm_toEuclideanLin_conjTranspose_eq h)
  obtain ⟨V, hVmem, hV⟩ := exists_unitary_of_linearIsometry W
  refine ⟨Vᴴ, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hVmem
  · have hmat : Matrix.toEuclideanLin (V * Aᴴ) = Matrix.toEuclideanLin Bᴴ := by
      apply LinearMap.ext
      intro x
      have h1 : Matrix.toEuclideanLin (V * Aᴴ) x
          = Matrix.toEuclideanLin V (Matrix.toEuclideanLin Aᴴ x) := by
        simp
      rw [h1, hV, hW x]
    have h2 : V * Aᴴ = Bᴴ := Matrix.toEuclideanLin.injective hmat
    have h3 := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul] using h3.symm

/-- If `A Aᴴ = B Bᴴ` and the second index type of `A` embeds into that of `B`, then `B = A V`
for some isometry `V` (a matrix with orthonormal rows, `V Vᴴ = 1`). -/
theorem exists_isometry_mul_eq {m' : Type*} [Fintype n] [Fintype m] [Fintype m'] [DecidableEq n]
    [DecidableEq m] [DecidableEq m'] {A : Matrix n m ℂ} {B : Matrix n m' ℂ}
    (h : A * Aᴴ = B * Bᴴ) (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ B = A * V := by
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  set E : Matrix m m' ℂ := (1 : Matrix m' m' ℂ).submatrix ι id with hE
  have hEE : E * Eᴴ = 1 := by
    ext k l
    simp [hE, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.one_apply, Finset.sum_ite_eq',
      ι.injective.eq_iff, eq_comm]
  have h' : (A * E) * (A * E)ᴴ = B * Bᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc A E, hEE,
      Matrix.mul_one, h]
  obtain ⟨U, hUmem, hU⟩ := exists_unitary_mul_eq h'
  have hUU : U * Uᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff (A := U)).mp hUmem
  refine ⟨E * U, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc E U, hUU,
      Matrix.mul_one, hEE]
  · rw [hU, Matrix.mul_assoc]

/-! ### Purification -/

/-- **Existence of purifications.** Every mixed state `ρ` on `H_A` (a positive semidefinite
matrix of trace one) has a purification by a unit vector of `H_A ⊗ H_A`. -/
theorem exists_purification [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ ψ : n × n → ℂ, IsPurification ρ ψ ∧ ∑ p, ‖ψ p‖ ^ 2 = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  set A : Matrix n n ℂ := Bᴴ with hA
  have hAA : A * Aᴴ = ρ := by simpa [hA, Matrix.star_eq_conjTranspose] using hB.symm
  refine ⟨fun p => A p.1 p.2, ?_, ?_⟩
  · rw [isPurification_iff]
    have : coeffMatrix (fun p : n × n => A p.1 p.2) = A := rfl
    rw [this, hAA]
  · have htrace : ((∑ p : n × n, ‖A p.1 p.2‖ ^ 2 : ℝ) : ℂ) = ρ.trace := by
      rw [← hAA]
      rw [Matrix.trace]
      push_cast
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj]
      simp [Complex.normSq_eq_norm_sq]
    rw [htr] at htrace
    exact_mod_cast htrace

/-- **Uniqueness of purifications up to a unitary on the ancilla.** Any two purifications of
the same state `ρ`, using the same ancilla, are related by a unitary acting on the ancilla
alone. -/
theorem purification_unique_up_to_unitary [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {ρ : Matrix n n ℂ} (ψ φ : n × m → ℂ) (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * U k j := by
  rw [isPurification_iff] at hψ hφ
  obtain ⟨U, hUmem, hU⟩ := exists_unitary_mul_eq (hψ.trans hφ.symm)
  refine ⟨U, hUmem, fun i j => ?_⟩
  have := congrFun (congrFun hU i) j
  simpa [coeffMatrix, Matrix.mul_apply] using this

/-- **Uniqueness of purifications up to an isometry of the ancillas.** Any two purifications
of the same state `ρ`, the first with an ancilla no larger than the second, are related by an
isometry `V` (`V Vᴴ = 1`) acting on the ancilla alone. -/
theorem purification_unique_up_to_isometry {m' : Type*} [Fintype n] [Fintype m] [Fintype m']
    [DecidableEq n] [DecidableEq m] [DecidableEq m'] {ρ : Matrix n n ℂ}
    (ψ : n × m → ℂ) (φ : n × m' → ℂ) (hψ : IsPurification ρ ψ) (hφ : IsPurification ρ φ)
    (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * V k j := by
  rw [isPurification_iff] at hψ hφ
  obtain ⟨V, hViso, hV⟩ := exists_isometry_mul_eq (hψ.trans hφ.symm) hcard
  refine ⟨V, hViso, fun i j => ?_⟩
  have := congrFun (congrFun hV i) j
  simpa [coeffMatrix, Matrix.mul_apply] using this

/-- **Purification exists, and is unique up to an isometry (indeed a unitary) on the
ancilla.** Every mixed state `ρ` on `H_A` — a positive semidefinite matrix of trace one —
admits a purification: a unit vector `ψ` of `H_A ⊗ H_B` whose reduced density matrix,
obtained by tracing out the ancilla, is `ρ`. Moreover any two purifications of `ρ` with the
same ancilla are related by a unitary acting on the ancilla only. -/
theorem purification_exists.{u} {n : Type u} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (∃ ψ : n × n → ℂ, IsPurification ρ ψ ∧ ∑ p, ‖ψ p‖ ^ 2 = 1) ∧
      (∀ (m : Type u) [Fintype m] [DecidableEq m] (ψ φ : n × m → ℂ),
        IsPurification ρ ψ → IsPurification ρ φ →
        ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
          ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * U k j) ∧
      (∀ (m m' : Type u) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
        (ψ : n × m → ℂ) (φ : n × m' → ℂ), IsPurification ρ ψ → IsPurification ρ φ →
        Fintype.card m ≤ Fintype.card m' →
        ∃ V : Matrix m m' ℂ, V * Vᴴ = 1 ∧ ∀ i j, φ (i, j) = ∑ k, ψ (i, k) * V k j) :=
  ⟨exists_purification hρ htr,
    fun _ _ _ ψ φ hψ hφ => purification_unique_up_to_unitary ψ φ hψ hφ,
    fun _ _ _ _ _ _ ψ φ hψ hφ hcard =>
      purification_unique_up_to_isometry ψ φ hψ hφ hcard⟩

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


import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

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

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/
theorem inner_toEuclideanLin_eq {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (M : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin M x) (Matrix.toEuclideanLin M y)
      = ((Mᴴ * M) *ᵥ y.ofLp) ⬝ᵥ star x.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec, dotProduct_comm]

/-- The matrix of a linear isometry of a finite-dimensional Euclidean space is unitary. -/
theorem toEuclideanLin_symm_mem_unitaryGroup {m : Type*} [Fintype m] [DecidableEq m]
    (U : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    (Matrix.toEuclideanLin.symm U.toLinearMap) ∈ Matrix.unitaryGroup m ℂ := by
  set M := (Matrix.toEuclideanLin.symm U.toLinearMap : Matrix m m ℂ) with hM
  have hMU : Matrix.toEuclideanLin M = U.toLinearMap := by rw [hM]; simp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h1 := inner_toEuclideanLin_eq M (WithLp.toLp 2 (Pi.single i 1))
    (WithLp.toLp 2 (Pi.single j 1))
  rw [hMU] at h1
  simp only [LinearIsometry.coe_toLinearMap] at h1
  rw [U.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct] at h1
  rw [Matrix.star_eq_conjTranspose]
  simpa [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Pi.single_apply, apply_ite, eq_comm] using h1.symm

/-- Two linear maps into a finite-dimensional inner product space which induce the same
inner products differ by a linear isometry of the target. -/
theorem exists_isometry_of_inner_eq {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (a b : V →ₗ[ℂ] W)
    (hinner : ∀ x y : V, inner ℂ (a x) (a y) = inner ℂ (b x) (b y)) :
    ∃ U : W →ₗᵢ[ℂ] W, ∀ x : V, U (a x) = b x := by
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    simp only [LinearMap.mem_ker] at hx ⊢
    have hxx := hinner x x
    rw [hx] at hxx
    simpa [inner_self_eq_zero] using hxx.symm
  let bq := (LinearMap.ker a).liftQ b hker
  let e := LinearMap.quotKerEquivRange a
  let g : ↥(LinearMap.range a) →ₗ[ℂ] W := bq ∘ₗ (e.symm : ↥(LinearMap.range a) →ₗ[ℂ] _)
  have hgap : ∀ x : V, g ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    have h1 : e.symm ⟨a x, LinearMap.mem_range_self a x⟩ = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      simp [e, LinearMap.quotKerEquivRange_apply_mk]
    show bq (e.symm _) = b x
    rw [h1]
    simp [bq]
  have hiso : ∀ w z : ↥(LinearMap.range a), inner ℂ (g w) (g z) = inner ℂ w z := by
    rintro ⟨w, x, rfl⟩ ⟨z, y, rfl⟩
    rw [hgap x, hgap y, ← hinner x y]
    rfl
  refine ⟨(LinearMap.isometryOfInner g hiso).extend, fun x => ?_⟩
  have hext := (LinearMap.isometryOfInner g hiso).extend_apply
    ⟨a x, LinearMap.mem_range_self a x⟩
  simpa [hgap x] using hext

/-- If `A * Aᴴ = B * Bᴴ` then `B = A * U` for some unitary matrix `U`. -/
theorem exists_unitary_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧ B = A * U := by
  have hinner : ∀ x y : EuclideanSpace ℂ n,
      inner ℂ (Matrix.toEuclideanLin Aᴴ x) (Matrix.toEuclideanLin Aᴴ y)
        = inner ℂ (Matrix.toEuclideanLin Bᴴ x) (Matrix.toEuclideanLin Bᴴ y) := by
    intro x y
    rw [inner_toEuclideanLin_eq, inner_toEuclideanLin_eq]
    simp [Matrix.conjTranspose_conjTranspose, h]
  obtain ⟨U, hU⟩ := exists_isometry_of_inner_eq _ _ hinner
  set M := (Matrix.toEuclideanLin.symm U.toLinearMap : Matrix m m ℂ) with hM
  have hMU : Matrix.toEuclideanLin M = U.toLinearMap := by rw [hM]; simp
  have hkey : M * Aᴴ = Bᴴ := by
    ext k i
    have hUi := hU (WithLp.toLp 2 (Pi.single i 1))
    have h2 : Matrix.toEuclideanLin M (Matrix.toEuclideanLin Aᴴ (WithLp.toLp 2 (Pi.single i 1)))
        = Matrix.toEuclideanLin Bᴴ (WithLp.toLp 2 (Pi.single i 1)) := by
      rw [hMU]; exact hUi
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, mulVec_mulVec] at h2
    have h3 := congrFun (congrArg WithLp.ofLp h2) k
    simpa [Matrix.mulVec_single] using h3
  refine ⟨Mᴴ, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem (toEuclideanLin_symm_mem_unitaryGroup U)
  · have hc := congrArg Matrix.conjTranspose hkey
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hc.symm

/-! ## States, purifications -/

/-- The reduced density matrix (partial trace over the ancilla) of the bipartite pure state
`ψ : n × m → ℂ`, i.e. the matrix `Tr_B |ψ⟩⟨ψ|`. -/
noncomputable def reducedState {n m : Type*} [Fintype m] (ψ : n × m → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k : m, ψ (i, k) * star (ψ (j, k))

/-- A mixed state (density matrix): a positive semidefinite matrix of trace one. -/
structure IsMixedState {n : Type*} [Fintype n] (ρ : Matrix n n ℂ) : Prop where
  posSemidef : ρ.PosSemidef
  trace_one : ρ.trace = 1

/-- `ψ` is a purification of `ρ` if tracing out the ancilla yields `ρ`. -/
def IsPurification {n m : Type*} [Fintype m] (ρ : Matrix n n ℂ) (ψ : n × m → ℂ) : Prop :=
  reducedState ψ = ρ

/-- The matrix (in `n × m` form) associated with a bipartite vector. -/
noncomputable def bipartiteMatrix {n m : Type*} (ψ : n × m → ℂ) : Matrix n m ℂ :=
  Matrix.of fun i k => ψ (i, k)

theorem reducedState_eq_mul_conjTranspose {n m : Type*} [Fintype m] (ψ : n × m → ℂ) :
    reducedState ψ = bipartiteMatrix ψ * (bipartiteMatrix ψ)ᴴ := by
  ext i j
  simp [reducedState, bipartiteMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]

/-- The squared norm of a bipartite vector equals the trace of its reduced state. -/
theorem sum_normSq_eq_trace_reducedState {n m : Type*} [Fintype n] [Fintype m] (ψ : n × m → ℂ) :
    ((∑ p : n × m, ‖ψ p‖ ^ 2 : ℝ) : ℂ) = (reducedState ψ).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, reducedState, Matrix.of_apply]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.star_def, Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq _).symm

/-- A purification of a mixed state is a unit vector. -/
theorem sum_normSq_purification {n m : Type*} [Fintype n] [Fintype m] {ρ : Matrix n n ℂ}
    (hρ : IsMixedState ρ) {ψ : n × m → ℂ} (hψ : IsPurification ρ ψ) :
    ∑ p : n × m, ‖ψ p‖ ^ 2 = 1 := by
  have h := sum_normSq_eq_trace_reducedState ψ
  rw [show reducedState ψ = ρ from hψ, hρ.trace_one] at h
  exact_mod_cast h

/-! ## Existence of purifications -/

/-- Every mixed state `ρ` on `n` admits a purification on `n × n`, given by the entries of the
positive semidefinite square root of `ρ`. -/
theorem exists_purification {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) :
    IsPurification ρ (fun p : n × n => (CFC.sqrt ρ) p.1 p.2) := by
  have hsqrt : (CFC.sqrt ρ).PosSemidef := Matrix.PosSemidef.posSemidef_sqrt
  have hsq : CFC.sqrt ρ * CFC.sqrt ρ = ρ := by
    have := Matrix.PosSemidef.sq_sqrt hρ
    rwa [pow_two] at this
  ext i j
  simp only [reducedState, Matrix.of_apply]
  have hH : ∀ a b : n, star ((CFC.sqrt ρ) b a) = (CFC.sqrt ρ) a b := by
    intro a b
    have := hsqrt.isHermitian
    calc star ((CFC.sqrt ρ) b a) = (CFC.sqrt ρ)ᴴ a b := by
          simp [Matrix.conjTranspose_apply]
      _ = (CFC.sqrt ρ) a b := by rw [this]
  calc ∑ k : n, (CFC.sqrt ρ) i k * star ((CFC.sqrt ρ) j k)
      = ∑ k : n, (CFC.sqrt ρ) i k * (CFC.sqrt ρ) k j := by
        exact Finset.sum_congr rfl fun k _ => by rw [hH k j]
    _ = (CFC.sqrt ρ * CFC.sqrt ρ) i j := by rw [Matrix.mul_apply]
    _ = ρ i j := by rw [hsq]

/-! ## Uniqueness of purifications up to a unitary on the ancilla -/

/-- Any two purifications of the same state with the same ancilla are related by a unitary
acting on the ancilla. -/
theorem purification_unique {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {ψ ψ' : n × m → ℂ} (hψ : IsPurification ρ ψ) (hψ' : IsPurification ρ ψ') :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ i : n, ∀ k : m, ψ' (i, k) = ∑ l : m, ψ (i, l) * U l k := by
  have hA : bipartiteMatrix ψ * (bipartiteMatrix ψ)ᴴ
      = bipartiteMatrix ψ' * (bipartiteMatrix ψ')ᴴ := by
    rw [← reducedState_eq_mul_conjTranspose, ← reducedState_eq_mul_conjTranspose,
      show reducedState ψ = ρ from hψ, show reducedState ψ' = ρ from hψ']
  obtain ⟨U, hUmem, hU⟩ :=
    exists_unitary_of_mul_conjTranspose_eq (bipartiteMatrix ψ) (bipartiteMatrix ψ') hA
  refine ⟨U, hUmem, fun i k => ?_⟩
  have := congrFun (congrFun hU i) k
  simpa [bipartiteMatrix, Matrix.mul_apply] using this

/-! ## Main theorem -/

/-- **Purification exists.** Every mixed state `ρ` on a finite-dimensional system has a
purification: a unit vector `ψ` on the doubled system whose partial trace over the ancilla
is `ρ`. Moreover any two purifications with a common ancilla are related by a unitary
transformation acting on the ancilla alone. -/
theorem purification_exists {n : Type u} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (hρ : IsMixedState ρ) :
    (∃ ψ : n × n → ℂ, IsPurification ρ ψ ∧ ∑ p : n × n, ‖ψ p‖ ^ 2 = 1) ∧
      (∀ {m : Type v} [Fintype m] [DecidableEq m] (ψ ψ' : n × m → ℂ),
        IsPurification ρ ψ → IsPurification ρ ψ' →
          ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
            ∀ i : n, ∀ k : m, ψ' (i, k) = ∑ l : m, ψ (i, l) * U l k) := by
  constructor
  · refine ⟨fun p : n × n => (CFC.sqrt ρ) p.1 p.2, ?_, ?_⟩
    · exact exists_purification hρ.posSemidef
    · exact sum_normSq_purification hρ (exists_purification hρ.posSemidef)
  · intro m _ _ ψ ψ' hψ hψ'
    exact purification_unique hψ hψ'

end QI


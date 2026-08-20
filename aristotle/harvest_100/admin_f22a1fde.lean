/-
/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the mandated header above is kept as a
-- plain comment and repeated as the module docstring below.)
-/

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

set_option grind.warning false

namespace QI

open Matrix

section Defs

variable {n m : Type*}

/-- The matrix `n × m` representation of a vector `ψ` of the tensor product `H ⊗ K`,
where `H` has orthonormal basis indexed by `n` and `K` has orthonormal basis indexed by `m`. -/
noncomputable def toMat (psi : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun i k => psi (i, k)

/-- The reduced density matrix of the pure state `|ψ⟩⟨ψ|` on `H ⊗ K`, obtained by taking the
partial trace over the ancilla space `K`:
`(ρ_ψ) i j = ∑ k, ψ (i,k) * conj (ψ (j,k))`. -/
noncomputable def reduced [Fintype m] (psi : n × m → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ k, psi (i, k) * starRingEnd ℂ (psi (j, k))

theorem reduced_eq [Fintype m] (psi : n × m → ℂ) :
    reduced psi = toMat psi * (toMat psi)ᴴ := by
  ext i j
  simp [reduced, toMat, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The squared norm of the vector `ψ` equals the trace of the corresponding reduced state. -/
theorem sum_norm_sq_eq_trace [Fintype n] [Fintype m] (A : Matrix n m ℂ) :
    ((∑ p : n × m, ‖A p.1 p.2‖ ^ 2 : ℝ) : ℂ) = (A * Aᴴ).trace := by
  push_cast
  rw [Matrix.trace, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [← Complex.mul_conj' (A i k)]; simp

end Defs

/-- If two linear maps `f g : E →ₗ[ℂ] F` into a finite dimensional inner product space have the
same "length function" `‖f x‖ = ‖g x‖`, then `g` is obtained from `f` by composing with a linear
isometry of `F`.  (This is the abstract form of the uniqueness of purifications.) -/
theorem exists_isometry_comp_of_norm_eq {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (f g : E →ₗ[ℂ] F) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ u : F →ₗᵢ[ℂ] F, ∀ x, u (f x) = g x := by
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    have hx0 : f x = 0 := LinearMap.mem_ker.mp hx
    have : ‖g x‖ = 0 := by rw [← h x, hx0, norm_zero]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp this)
  set q : (E ⧸ LinearMap.ker f) →ₗ[ℂ] F := (LinearMap.ker f).liftQ g hker with hq
  set e : (E ⧸ LinearMap.ker f) ≃ₗ[ℂ] (LinearMap.range f) := f.quotKerEquivRange with he
  have hsymm : ∀ x : E, e.symm ⟨f x, LinearMap.mem_range_self f x⟩
      = Submodule.Quotient.mk x := by
    intro x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he]
    exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x).symm
  set L₀ : (LinearMap.range f) →ₗ[ℂ] F := q ∘ₗ (e.symm : (LinearMap.range f) →ₗ[ℂ] _) with hL₀
  have hval : ∀ x : E, L₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    simp only [hL₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hsymm x, hq]
    exact (LinearMap.ker f).liftQ_apply g x
  have hnorm : ∀ y : (LinearMap.range f), ‖L₀ y‖ = ‖(y : F)‖ := by
    rintro ⟨y, x, rfl⟩
    rw [hval x, ← h x]
  refine ⟨(⟨L₀, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] F).extend, fun x => ?_⟩
  rw [(⟨L₀, hnorm⟩ : (LinearMap.range f) →ₗᵢ[ℂ] F).extend_apply
      ⟨f x, LinearMap.mem_range_self f x⟩]
  exact hval x

/-- A linear isometry of `EuclideanSpace ℂ m` is given by multiplication by a unitary matrix. -/
theorem exists_unitary_matrix_of_isometry {m : Type*} [Fintype m] [DecidableEq m]
    (u : EuclideanSpace ℂ m →ₗᵢ[ℂ] EuclideanSpace ℂ m) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ v : EuclideanSpace ℂ m, U *ᵥ v.ofLp = (u v).ofLp := by
  set U : Matrix m m ℂ := Matrix.of fun i j => (u (EuclideanSpace.single j (1:ℂ))).ofLp i with hU
  have hdecomp : ∀ v : EuclideanSpace ℂ m,
      v = ∑ j, v.ofLp j • (EuclideanSpace.single j (1:ℂ)) := by
    intro v
    ext i
    simp [Pi.single_apply, Finset.sum_ite_eq]
  have hmul : ∀ v : EuclideanSpace ℂ m, U *ᵥ v.ofLp = (u v).ofLp := by
    intro v
    funext i
    conv_rhs => rw [hdecomp v]
    rw [map_sum]
    simp [Matrix.mulVec, dotProduct, hU, mul_comm]
  refine ⟨U, ?_, hmul⟩
  have hstar : ∀ z : ℂ, star z = (starRingEnd ℂ) z := fun _ => rfl
  rw [Matrix.mem_unitaryGroup_iff']
  ext j k
  have hinner := u.inner_map_map (EuclideanSpace.single j (1:ℂ)) (EuclideanSpace.single k (1:ℂ))
  rw [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, PiLp.inner_apply] at hinner
  simp only [RCLike.inner_apply] at hinner
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, hU, Matrix.of_apply, hstar]
  rw [Finset.sum_congr rfl fun x _ =>
    mul_comm ((starRingEnd ℂ) ((u (EuclideanSpace.single j (1:ℂ))).ofLp x))
      ((u (EuclideanSpace.single k (1:ℂ))).ofLp x), hinner]
  simp

/-- If `A Aᴴ = B Bᴴ` then the columns of `Aᴴ` and `Bᴴ` have the same lengths. -/
theorem norm_toEuclideanLin_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin Aᴴ x‖ = ‖Matrix.toEuclideanLin Bᴴ x‖ := by
  have key : ∀ C : Matrix n m ℂ,
      (inner ℂ (Matrix.toEuclideanLin Cᴴ x) (Matrix.toEuclideanLin Cᴴ x) : ℂ)
        = star (x.ofLp) ᵥ* (C * Cᴴ) ⬝ᵥ x.ofLp := by
    intro C
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, dotProduct_comm,
      dotProduct_mulVec, Matrix.vecMul_vecMul]
  have h1 : (inner ℂ (Matrix.toEuclideanLin Aᴴ x) (Matrix.toEuclideanLin Aᴴ x) : ℂ)
      = inner ℂ (Matrix.toEuclideanLin Bᴴ x) (Matrix.toEuclideanLin Bᴴ x) := by
    rw [key A, key B, h]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖Matrix.toEuclideanLin Aᴴ x‖ ^ 2 = ‖Matrix.toEuclideanLin Bᴴ x‖ ^ 2 := by
    exact_mod_cast h1
  have h3 := congrArg Real.sqrt h2
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- **Uniqueness of purifications up to an isometry on the ancilla**, in matrix form:
if `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U` acting on the ancilla index. -/
theorem exists_unitary_of_mul_conjTranspose_eq {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A B : Matrix n m ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧ B = A * U := by
  obtain ⟨u, hu⟩ := exists_isometry_comp_of_norm_eq (Matrix.toEuclideanLin Aᴴ)
    (Matrix.toEuclideanLin Bᴴ) (norm_toEuclideanLin_conjTranspose_eq A B h)
  obtain ⟨U₀, hU₀, hU₀mul⟩ := exists_unitary_matrix_of_isometry u
  have hcomp : U₀ * Aᴴ = Bᴴ := by
    ext i j
    have hx := hu (WithLp.toLp 2 (Pi.single j (1 : ℂ)))
    have h1 : U₀ *ᵥ (Aᴴ *ᵥ (Pi.single j (1 : ℂ))) = Bᴴ *ᵥ (Pi.single j (1 : ℂ)) := by
      have := congrArg (fun w : EuclideanSpace ℂ m => w.ofLp) hx
      simpa [Matrix.toLpLin_apply, hU₀mul] using this
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_mulVec] at h2
    simpa using h2
  refine ⟨U₀ᴴ, ?_, ?_⟩
  · exact Unitary.star_mem hU₀
  · have := congrArg Matrix.conjTranspose hcomp
    simpa [Matrix.conjTranspose_mul] using this.symm

/-- **Purification exists and is unique up to an isometry on the ancilla.**

For a mixed state `ρ` (a positive semidefinite matrix of trace one) on a finite dimensional
Hilbert space `H` with orthonormal basis indexed by `n`:

* there is a unit vector `ψ` of `H ⊗ H` whose reduced density matrix (partial trace over the
  ancilla) is `ρ`;
* any two purifications of `ρ` on a common ancilla space `K` (basis indexed by `m`) are related
  by a unitary acting on the ancilla alone. -/
theorem purification_exists {n : Type*} [Fintype n] [DecidableEq n] (rho : Matrix n n ℂ)
    (hrho : rho.PosSemidef) (htr : rho.trace = 1) :
    (∃ psi : n × n → ℂ, reduced psi = rho ∧ ∑ p : n × n, ‖psi p‖ ^ 2 = 1) ∧
    (∀ (m : Type*) [Fintype m] [DecidableEq m] (psi₁ psi₂ : n × m → ℂ),
        reduced psi₁ = rho → reduced psi₂ = rho →
        ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
          ∀ i k, psi₂ (i, k) = ∑ l, psi₁ (i, l) * U l k) := by
  constructor
  · -- Existence: the vector with matrix `√ρ` is a purification.
    have hsq : (CFC.sqrt rho).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg rho)
    have hmul : CFC.sqrt rho * (CFC.sqrt rho)ᴴ = rho := by
      rw [hsq.1.eq, CFC.sqrt_mul_sqrt_self rho hrho.nonneg]
    refine ⟨fun p => CFC.sqrt rho p.1 p.2, ?_, ?_⟩
    · rw [reduced_eq]
      simpa [toMat] using hmul
    · have hcast : ((∑ p : n × n, ‖CFC.sqrt rho p.1 p.2‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [sum_norm_sq_eq_trace (CFC.sqrt rho), hmul, htr]
      exact_mod_cast hcast
  · -- Uniqueness up to a unitary on the ancilla.
    intro m _ _ psi₁ psi₂ h₁ h₂
    have hAB : toMat psi₁ * (toMat psi₁)ᴴ = toMat psi₂ * (toMat psi₂)ᴴ := by
      rw [← reduced_eq, ← reduced_eq, h₁, h₂]
    obtain ⟨U, hU, hBU⟩ := exists_unitary_of_mul_conjTranspose_eq _ _ hAB
    refine ⟨U, hU, fun i k => ?_⟩
    have := congrArg (fun M => M i k) hBU
    simpa [toMat, Matrix.mul_apply] using this

end QI


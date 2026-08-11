/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

/-!
## Setting

A state of a finite dimensional quantum system with basis indexed by `n` is a positive
semidefinite matrix `ρ : Matrix n n ℂ` of trace one.

A vector of the composite system `H ⊗ K`, where `K` is an ancilla with basis indexed by `m`,
is encoded by its matrix of coefficients `A : Matrix n m ℂ`, i.e. `A` encodes
`∑ i, ∑ j, A i j • (e i ⊗ f j)`.  With this encoding the reduced density matrix
(the partial trace over the ancilla) of the pure state `|A⟩⟨A|` is exactly `A * Aᴴ`, and the
squared norm of the vector is `∑ i, ∑ j, ‖A i j‖ ^ 2 = trace (A * Aᴴ)`.

Consequently `A` purifies `ρ` exactly when `A * Aᴴ = ρ`, and an isometry `K → K'` of ancillas
acting on the second tensor factor sends the vector `A` to `A * W`, where `W : Matrix m m' ℂ`
satisfies `W * Wᴴ = 1`.
-/

/-- `A` is a purification of the state `ρ`: the reduced density matrix (partial trace over the
ancilla) of the pure state given by the vector with coefficient matrix `A` equals `ρ`. -/
def IsPurification {n m : Type*} [Fintype m] (ρ : Matrix n n ℂ) (A : Matrix n m ℂ) : Prop :=
  A * Aᴴ = ρ

/-! ## Auxiliary results -/

/-- Two linear maps into a finite dimensional inner product space with the same "norm profile"
differ by a linear isometry of the target: if `‖f x‖ = ‖g x‖` for all `x`, then there is a
linear isometry `L` of the target with `L ∘ f = g`. -/
theorem exists_linearIsometry_comp_eq {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f g : E →ₗ[ℂ] V) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ L : V →ₗᵢ[ℂ] V, ∀ x, L (f x) = g x := by
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext x
    simp only [LinearMap.mem_ker, ← norm_eq_zero (a := f x), ← norm_eq_zero (a := g x), h x]
  set e₁ := f.quotKerEquivRange with he₁
  set e₂ := g.quotKerEquivRange with he₂
  set q : (E ⧸ LinearMap.ker f) ≃ₗ[ℂ] (E ⧸ LinearMap.ker g) := Submodule.quotEquivOfEq _ _ hker
  set L₀ : ↥(LinearMap.range f) →ₗ[ℂ] V :=
    (LinearMap.range g).subtype ∘ₗ e₂.toLinearMap ∘ₗ q.toLinearMap ∘ₗ e₁.symm.toLinearMap with hL₀
  have key : ∀ x : E, L₀ ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
    intro x
    have h1 : e₁.symm ⟨f x, LinearMap.mem_range_self f x⟩ = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [hL₀, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
      Submodule.coe_subtype]
    rfl
  have hnorm : ∀ z : ↥(LinearMap.range f), ‖L₀ z‖ = ‖z‖ := by
    rintro ⟨z, x, rfl⟩
    rw [key x, ← h x]; rfl
  set Li : ↥(LinearMap.range f) →ₗᵢ[ℂ] V := { toLinearMap := L₀, norm_map' := hnorm } with hLi
  refine ⟨Li.extend, fun x => ?_⟩
  have hx := Li.extend_apply ⟨f x, LinearMap.mem_range_self f x⟩
  rw [show ((⟨f x, LinearMap.mem_range_self f x⟩ : ↥(LinearMap.range f)) : V) = f x from rfl] at hx
  rw [hx]
  exact key x

theorem toEuclideanLin_mul {l m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix l m ℂ) (N : Matrix m n ℂ) :
    toEuclideanLin (M * N) = (toEuclideanLin M) ∘ₗ (toEuclideanLin N) := by
  ext x i; simp [Matrix.toEuclideanLin, mulVec_mulVec]

theorem toEuclideanLin_one {n : Type*} [Fintype n] [DecidableEq n] :
    toEuclideanLin (1 : Matrix n n ℂ) = LinearMap.id := by
  ext x i; simp [Matrix.toEuclideanLin]

/-- If `A * Aᴴ = B * Bᴴ` for two matrices of the same shape, then `A` and `B` differ by a
unitary matrix acting on the right. -/
theorem exists_unitary_mul_eq {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A B : Matrix n p ℂ) (h : A * Aᴴ = B * Bᴴ) :
    ∃ U : Matrix p p ℂ, U * Uᴴ = 1 ∧ A * U = B := by
  -- the maps `x ↦ Aᴴ x` and `x ↦ Bᴴ x` have the same norm profile
  have hnorms : ∀ x : EuclideanSpace ℂ n,
      ‖toEuclideanLin Aᴴ x‖ = ‖toEuclideanLin Bᴴ x‖ := by
    intro x
    have key : ∀ C : Matrix n p ℂ, (inner ℂ (toEuclideanLin Cᴴ x) (toEuclideanLin Cᴴ x) : ℂ)
        = inner ℂ x (toEuclideanLin (C * Cᴴ) x) := by
      intro C
      rw [toEuclideanLin_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint C,
        LinearMap.adjoint_inner_left]
      rfl
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key A, key B, h]
  obtain ⟨L, hL⟩ := exists_linearIsometry_comp_eq _ _ hnorms
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix p p ℂ, toEuclideanLin U₀ = L.toLinearMap :=
    ⟨toEuclideanLin.symm L.toLinearMap, by simp⟩
  have hstar : U₀ᴴ * U₀ = 1 := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_one, hU₀,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint U₀, hU₀]
    refine LinearMap.ext fun x => ?_
    apply ext_inner_right ℂ
    intro v
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    exact L.inner_map_map x v
  have hmul : U₀ * Aᴴ = Bᴴ := by
    apply toEuclideanLin.injective
    rw [toEuclideanLin_mul, hU₀]
    exact LinearMap.ext fun x => hL x
  refine ⟨U₀ᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose, hstar]
  · have h2 := congrArg Matrix.conjTranspose hmul
    rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_conjTranspose] at h2

/-- If `m` injects into `m'`, there is an isometric embedding `ℂ^m → ℂ^{m'}`, given by a matrix
with orthonormal columns. -/
theorem exists_isometry_matrix {m m' : Type*} [Fintype m] [DecidableEq m] [Fintype m']
    [DecidableEq m'] (h : Fintype.card m ≤ Fintype.card m') :
    ∃ J : Matrix m' m ℂ, Jᴴ * J = 1 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h
  refine ⟨Matrix.of fun (i : m') (j : m) => if i = f j then (1 : ℂ) else 0, ?_⟩
  ext j k
  simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply,
    apply_ite star, star_one, star_zero]
  rw [Finset.sum_eq_single (f j)]
  · simp [f.injective.eq_iff]
  · intro b _ hb
    simp [hb]
  · intro hb
    exact absurd (Finset.mem_univ (f j)) hb

/-! ## Purification -/

/-- The canonical purification: the positive semidefinite square root of `ρ`. -/
theorem exists_purification {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) : IsPurification ρ (CFC.sqrt ρ) := by
  have hherm : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  rw [IsPurification, hherm]
  exact CFC.sqrt_mul_sqrt_self ρ (by exact hρ.nonneg)

/-- A purification of a state of trace one is a unit vector. -/
theorem purification_unit_norm {n m : Type*} [Fintype n] [Fintype m] {ρ : Matrix n n ℂ}
    (htr : ρ.trace = 1) {A : Matrix n m ℂ} (hA : IsPurification ρ A) :
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
  have h : ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← htr, ← hA]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, conjTranspose_apply,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
    norm_cast
    exact Complex.sq_norm (A i j)
  exact_mod_cast h

/-- Any two purifications of the same state are related by an isometry acting on the ancilla:
if `A` (ancilla `m`) and `B` (ancilla `m'`) both purify `ρ` and the ancilla `m` is no bigger
than `m'`, then there is an isometry `W` (`W * Wᴴ = 1`) with `A * W = B`. -/
theorem purification_unique {n m m' : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype m'] [DecidableEq m'] {ρ : Matrix n n ℂ}
    (A : Matrix n m ℂ) (B : Matrix n m' ℂ) (hA : IsPurification ρ A) (hB : IsPurification ρ B)
    (hcard : Fintype.card m ≤ Fintype.card m') :
    ∃ W : Matrix m m' ℂ, W * Wᴴ = 1 ∧ A * W = B := by
  obtain ⟨J, hJ⟩ := exists_isometry_matrix (m := m) (m' := m') hcard
  have hA' : (A * Jᴴ) * (A * Jᴴ)ᴴ = B * Bᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.mul_assoc A Jᴴ J, hJ, Matrix.mul_one, hA, hB]
  obtain ⟨U, hU, hAU⟩ := exists_unitary_mul_eq (A * Jᴴ) B hA'
  refine ⟨Jᴴ * U, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ J, hU, Matrix.one_mul, hJ]
  · rw [← Matrix.mul_assoc, hAU]

/-- **Every mixed state has a purification, unique up to an isometry on the ancilla.**

Let `ρ` be a mixed state of a finite dimensional system (a positive semidefinite matrix of
trace one).  Then:

* (existence) there is a purification `A` of `ρ` using an ancilla of the same dimension as the
  system, and the corresponding vector of the composite system is a unit vector;
* (uniqueness) any two purifications `A` (ancilla `m`) and `B` (ancilla `m'`) of `ρ` with
  `card m ≤ card m'` are related by an isometry `W` on the ancilla, `W * Wᴴ = 1`, via
  `A * W = B`.
-/
theorem purification_exists.{u, v} {n : Type u} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (∃ A : Matrix n n ℂ, IsPurification ρ A ∧ ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1) ∧
      (∀ {m m' : Type v} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
        (A : Matrix n m ℂ) (B : Matrix n m' ℂ), IsPurification ρ A → IsPurification ρ B →
          Fintype.card m ≤ Fintype.card m' →
          ∃ W : Matrix m m' ℂ, W * Wᴴ = 1 ∧ A * W = B) := by
  refine ⟨⟨CFC.sqrt ρ, exists_purification hρ,
    purification_unit_norm htr (exists_purification hρ)⟩, ?_⟩
  intro m m' _ _ _ _ A B hA hB hcard
  exact purification_unique A B hA hB hcard

/-- Sanity check (non-vacuity): the maximally mixed state of a qubit is a mixed state, hence
has a purification given by a unit vector of the doubled system. -/
example : ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
    IsPurification ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) A ∧
      ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 :=
  (purification_exists.{0, 0} _ (Matrix.PosSemidef.one.smul (by simp)) (by simp)).1

end QI


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


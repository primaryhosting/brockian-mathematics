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

namespace QC

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Functional calculus for Hermitian matrices

Given a Hermitian matrix `A` with unitary diagonalization `A = U D Uᴴ`, and a real function `f`,
`QC.hermFun A hA f` is the matrix `U f(D) Uᴴ`.  This is the usual (Borel/continuous) functional
calculus in finite dimensions; it lets us give a literal meaning to expressions such as
`ρ log ρ`. -/

/-- Functional calculus: `f` applied to the Hermitian matrix `A` through its spectral
decomposition. -/
noncomputable def hermFun (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
    (Matrix.diagonal (RCLike.ofReal ∘ (f ∘ hA.eigenvalues)))

/-- Conjugation by a unitary preserves the trace. -/
lemma trace_conjStarAlgAut (u : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) u A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- Sanity check: the functional calculus applied to the identity function returns `A`. -/
lemma hermFun_id (A : Matrix n n ℂ) (hA : A.IsHermitian) : hermFun A hA id = A := by
  rw [hermFun]
  exact (hA.spectral_theorem).symm

/-- The trace of `f(A)` is the sum of `f` over the eigenvalues of `A`. -/
lemma trace_hermFun (A : Matrix n n ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hermFun A hA f).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hermFun, trace_conjStarAlgAut, Matrix.trace_diagonal]
  push_cast
  rfl

/-! ## Von Neumann entropy -/

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix, defined spectrally as
`-∑ᵢ λᵢ log λᵢ`, with the usual convention `0 log 0 = 0` (which is automatic in Mathlib since
`Real.log 0 = 0`).  For non-Hermitian matrices the value is set to `0`. -/
noncomputable def vonNeumannEntropy (A : Matrix n n ℂ) : ℝ :=
  if hA : A.IsHermitian then -∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) else 0

lemma vonNeumannEntropy_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    vonNeumannEntropy A = -∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
  rw [vonNeumannEntropy, dif_pos hA]

/-- The spectral definition of the von Neumann entropy really is `-Tr(ρ log ρ)`, where
`ρ log ρ` is understood via the functional calculus `QC.hermFun`. -/
theorem vonNeumannEntropy_eq_neg_trace_mul_log {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (vonNeumannEntropy A : ℂ) = -(hermFun A hA (fun x => x * Real.log x)).trace := by
  rw [vonNeumannEntropy_of_isHermitian hA, trace_hermFun]
  push_cast
  ring

/-! ## Pure states -/

/-- The density matrix `|ψ⟩⟨ψ|` of a pure state, i.e. `ρ i j = ψ i * conj (ψ j)`. -/
noncomputable def pureDensity (psi : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec psi (star psi)

omit [Fintype n] [DecidableEq n] in
lemma pureDensity_apply (psi : n → ℂ) (i j : n) :
    pureDensity psi i j = psi i * (starRingEnd ℂ) (psi j) := rfl

omit [Fintype n] [DecidableEq n] in
lemma pureDensity_isHermitian (psi : n → ℂ) : (pureDensity psi).IsHermitian := by
  ext i j
  simp [pureDensity, Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
/-- The normalisation `∑ᵢ ‖ψ i‖² = 1` written in `ℂ`. -/
lemma sum_conj_mul_of_norm (psi : n → ℂ) (h : ∑ i, ‖psi i‖ ^ 2 = 1) :
    ∑ i, (starRingEnd ℂ) (psi i) * psi i = 1 := by
  have key : ∀ i : n, (starRingEnd ℂ) (psi i) * psi i = ((‖psi i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Complex.ofReal_sum, h, Complex.ofReal_one]

omit [DecidableEq n] in
/-- A normalised pure state has unit trace, i.e. it is a density matrix. -/
lemma trace_pureDensity (psi : n → ℂ) (h : ∑ i, ‖psi i‖ ^ 2 = 1) :
    (pureDensity psi).trace = 1 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pureDensity_apply]
  rw [← sum_conj_mul_of_norm psi h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq n] in
/-- A pure state is an idempotent (a rank-one orthogonal projection). -/
lemma pureDensity_mul_self (psi : n → ℂ) (h : ∑ i, ‖psi i‖ ^ 2 = 1) :
    pureDensity psi * pureDensity psi = pureDensity psi := by
  have h' := sum_conj_mul_of_norm psi h
  ext i j
  simp only [Matrix.mul_apply, pureDensity_apply]
  have key : ∀ k : n, psi i * (starRingEnd ℂ) (psi k) * (psi k * (starRingEnd ℂ) (psi j))
      = ((starRingEnd ℂ) (psi k) * psi k) * (psi i * (starRingEnd ℂ) (psi j)) := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_mul, h', one_mul]

/-! ## Eigenvalues of an idempotent Hermitian matrix -/

/-- The eigenvalues of an idempotent Hermitian matrix satisfy `λ² = λ`. -/
lemma eigenvalues_sq_eq_self_of_idempotent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : A * A = A) (i : n) : hA.eigenvalues i * hA.eigenvalues i = hA.eigenvalues i := by
  set f := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) (star hA.eigenvectorUnitary) with hf
  have h1 : f A = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) :=
    hA.conjStarAlgAut_star_eigenvectorUnitary
  have h2 : f A * f A = f A := by rw [← map_mul, h]
  rw [h1, Matrix.diagonal_mul_diagonal] at h2
  have h3 := congrFun (congrFun h2 i) i
  simp only [Matrix.diagonal_apply_eq, Function.comp_apply] at h3
  exact_mod_cast h3

/-- Each eigenvalue of an idempotent Hermitian matrix is `0` or `1`. -/
lemma eigenvalues_eq_zero_or_one_of_idempotent {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : A * A = A) (i : n) : hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have := eigenvalues_sq_eq_self_of_idempotent hA h i
  rcases eq_or_ne (hA.eigenvalues i) 0 with h0 | h0
  · exact Or.inl h0
  · refine Or.inr (mul_right_cancel₀ h0 ?_)
    rw [one_mul]
    exact this

/-! ## Main result -/

/-- **The von Neumann entropy of a pure state vanishes.**
For a normalised vector `ψ` (`∑ᵢ ‖ψ i‖² = 1`), the density matrix `ρ = |ψ⟩⟨ψ|` satisfies
`S(ρ) = -Tr(ρ log ρ) = 0`. -/
theorem pure_state_zero_entropy {psi : n → ℂ} (h : ∑ i, ‖psi i‖ ^ 2 = 1) :
    vonNeumannEntropy (pureDensity psi) = 0 := by
  have hH := pureDensity_isHermitian psi
  have hidem := pureDensity_mul_self psi h
  rw [vonNeumannEntropy_of_isHermitian hH, neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases eigenvalues_eq_zero_or_one_of_idempotent hH hidem i with h0 | h1
  · rw [h0, zero_mul]
  · rw [h1, Real.log_one, mul_zero]

end QC


/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
Statement: The 3-qubit GHZ state yields a deterministic Mermin paradox contradiction with local hidden variables.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Kronecker

/-- Index type for three qubits. -/
abbrev Idx : Type := (Fin 2 × Fin 2) × Fin 2

/-- A measurement setting for one party: `false` means measure the Pauli `X`
observable, `true` means measure the Pauli `Y` observable. -/
abbrev Setting : Type := Bool

/-- The Pauli `X` matrix. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
noncomputable def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The observable measured for a given setting. -/
noncomputable def obs : Setting → Matrix (Fin 2) (Fin 2) ℂ
  | false => pauliX
  | true => pauliY

/-- The three-party observable `obs s₁ ⊗ obs s₂ ⊗ obs s₃`. -/
noncomputable def triObs (s₁ s₂ s₃ : Setting) : Matrix Idx Idx ℂ :=
  obs s₁ ⊗ₖ obs s₂ ⊗ₖ obs s₃

/-- The (normalized) three-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : Idx → ℂ :=
  fun i => if i = ((0, 0), 0) ∨ i = ((1, 1), 1) then ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- The Mermin sign: the GHZ state is an eigenvector of `triObs s₁ s₂ s₃` with
eigenvalue `+1` when all three settings are `X`, and `-1` when exactly two of
them are `Y`. -/
def merminSign (s₁ s₂ s₃ : Setting) : ℤ :=
  cond (s₁ || s₂ || s₃) (-1) 1

/-- The four Mermin measurement contexts: those with an even number of `Y`s. -/
def merminContext (s₁ s₂ s₃ : Setting) : Prop := (xor (xor s₁ s₂) s₃) = false

/-- The GHZ state is a unit vector. -/
theorem ghz_normalized : ∑ i : Idx, Complex.normSq (ghz i) = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [ghz, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  field_simp
  nlinarith [h2, Real.sqrt_nonneg 2]

theorem ghz_ne_zero : ghz ((0, 0), 0) ≠ 0 := by
  have h : Real.sqrt 2 ≠ 0 := by positivity
  simp [ghz, h]

/-- The GHZ eigenvalue equations: for each of the four Mermin contexts the GHZ
state is an eigenvector of the corresponding product observable with eigenvalue
`merminSign`. -/
theorem ghz_eigen (s₁ s₂ s₃ : Setting) (h : merminContext s₁ s₂ s₃) :
    (triObs s₁ s₂ s₃).mulVec ghz = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) • ghz := by
  have compute : ∀ s₁ s₂ s₃ : Setting,
      (s₁ = false ∧ s₂ = false ∧ s₃ = false) ∨ (s₁ = false ∧ s₂ = true ∧ s₃ = true) ∨
        (s₁ = true ∧ s₂ = false ∧ s₃ = true) ∨ (s₁ = true ∧ s₂ = true ∧ s₃ = false) →
      (triObs s₁ s₂ s₃).mulVec ghz = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) • ghz := by
    rintro s₁ s₂ s₃ (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      · funext i
        fin_cases i <;>
          simp [triObs, obs, merminSign, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
            Fin.sum_univ_two, ghz, pauliX, pauliY]
  refine compute s₁ s₂ s₃ ?_
  revert h
  cases s₁ <;> cases s₂ <;> cases s₃ <;> simp [merminContext]

/-- Product of the four Mermin eigenvalues is `-1`. -/
theorem mermin_sign_prod :
    merminSign false false false * merminSign false true true *
      merminSign true false true * merminSign true true false = -1 := by
  rfl

/-- **Mermin's GHZ paradox.** There is no local hidden variable model: no
assignment of (setting-dependent, but outcome-deterministic and local) values
`A`, `B`, `C` to the three parties can reproduce the quantum mechanical
predictions for the GHZ state in the four Mermin contexts, i.e. there are no
`A B C : Setting → ℤ` whose products give the eigenvalues of `triObs` on `ghz`. -/
theorem ghz_nonlocal :
    ¬ ∃ A B C : Setting → ℤ,
        ∀ s₁ s₂ s₃ : Setting, merminContext s₁ s₂ s₃ →
          (triObs s₁ s₂ s₃).mulVec ghz = ((A s₁ * B s₂ * C s₃ : ℤ) : ℂ) • ghz := by
  rintro ⟨A, B, C, hABC⟩
  -- each Mermin context forces the local product to equal the quantum eigenvalue
  have key : ∀ s₁ s₂ s₃ : Setting, merminContext s₁ s₂ s₃ →
      A s₁ * B s₂ * C s₃ = merminSign s₁ s₂ s₃ := by
    intro s₁ s₂ s₃ h
    have h1 := hABC s₁ s₂ s₃ h
    have h2 := ghz_eigen s₁ s₂ s₃ h
    have h3 : ((A s₁ * B s₂ * C s₃ : ℤ) : ℂ) • ghz = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) • ghz := by
      rw [← h1, h2]
    have h4 := congrFun h3 ((0, 0), 0)
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    have h5 : ((A s₁ * B s₂ * C s₃ : ℤ) : ℂ) = ((merminSign s₁ s₂ s₃ : ℤ) : ℂ) :=
      mul_right_cancel₀ ghz_ne_zero h4
    exact_mod_cast h5
  have e1 := key false false false rfl
  have e2 := key false true true rfl
  have e3 := key true false true rfl
  have e4 := key true true false rfl
  have hsq : (A false * A true * B false * B true * C false * C true) ^ 2 = -1 := by
    have : (A false * B false * C false) * (A false * B true * C true) *
        ((A true * B false * C true) * (A true * B true * C false)) = -1 := by
      rw [e1, e2, e3, e4]; rfl
    nlinarith [this]
  nlinarith [sq_nonneg (A false * A true * B false * B true * C false * C true)]

end QC


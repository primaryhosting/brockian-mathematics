/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Statement: Fidelity equals the maximal overlap over purifications (Uhlmann's theorem).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Basic notions

We work with a finite dimensional quantum system with Hilbert space `EuclideanSpace ℂ n`.
States are described by positive semidefinite matrices, and a purification of a state `ρ`
on the system is a vector of the composite system `EuclideanSpace ℂ (n × m)` (the tensor
product of the system with an ancilla) whose reduced density matrix (the partial trace over
the ancilla) is `ρ`.
-/

/-- The partial trace over the second (ancilla) tensor factor. -/

theorem exists_unitary_of_mul_conjTranspose_eq {A B : Matrix n n ℂ} (h : A * Aᴴ = B * Bᴴ) :
    ∃ U ∈ unitaryGroup n ℂ, A = B * U := by
  obtain ⟨W₁, hW₁, hA⟩ := exists_unitary_mul_sqrt Aᴴ
  obtain ⟨W₂, hW₂, hB⟩ := exists_unitary_mul_sqrt Bᴴ
  rw [Matrix.conjTranspose_conjTranspose] at hA hB
  rw [← h] at hB
  set S := CFC.sqrt (A * Aᴴ) with hSdef
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg (A * Aᴴ)).posSemidef.1
  have hA' : A = S * W₁ᴴ := by
    have := congrArg Matrix.conjTranspose hA
    simpa [Matrix.conjTranspose_mul, hSh] using this
  have hB' : B = S * W₂ᴴ := by
    have := congrArg Matrix.conjTranspose hB
    simpa [Matrix.conjTranspose_mul, hSh] using this
  have hW₂star : (W₂ᴴ : Matrix n n ℂ) * W₂ = 1 := Matrix.mem_unitaryGroup_iff'.mp hW₂
  refine ⟨W₂ * W₁ᴴ, Submonoid.mul_mem _ hW₂ (Unitary.star_mem hW₁), ?_⟩
  rw [hB', hA']
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc W₂ᴴ W₂, hW₂star, Matrix.one_mul]

/-- Duality bound: `|tr (M U)| ≤ tr √(Mᴴ M)` for every unitary `U`. -/

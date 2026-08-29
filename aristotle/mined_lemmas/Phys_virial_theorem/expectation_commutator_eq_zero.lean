import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Phys

open Complex MeasureTheory Filter Topology

/-- The expectation value `⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

theorem expectation_commutator_eq_zero (H A : E →ₗ[ℂ] E) (psi : E) (E₀ : ℂ)
    (hsymm : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y))
    (hpsi : psi ≠ 0) (heig : H psi = E₀ • psi) :
    inner ℂ psi (H (A psi) - A (H psi)) = (0 : ℂ) := by
  have hreal : (starRingEnd ℂ) E₀ = E₀ := eigenvalue_isReal H psi E₀ hsymm hpsi heig
  rw [inner_sub_right, ← hsymm psi (A psi), heig, map_smul, inner_smul_left, inner_smul_right,
    hreal, sub_self]

/-- **Quantum virial theorem.**

Let `H` be a (symmetric) Hamiltonian, `psi` a normalized bound stationary state, i.e. a unit
eigenvector of `H`, and let `A` be the generator of dilations `A = r · p`.  The defining
algebraic property of `A` is the commutator identity `[H, A] = i (2 T - W)`, where `T` is the
kinetic energy operator and `W = r · ∇V` the virial operator.  Then
`2 ⟨T⟩ = ⟨r · ∇V⟩`. -/

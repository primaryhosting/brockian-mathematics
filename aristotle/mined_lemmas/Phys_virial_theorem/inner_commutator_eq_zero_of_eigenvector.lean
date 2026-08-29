import Mathlib
-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the requested header comment follows the import.)

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped ComplexConjugate InnerProductSpace

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

/-- The quantum-mechanical expectation value `⟨Op⟩ = ⟪ψ, Op ψ⟫` of an operator `Op`
in the (normalized) state `ψ`. -/

theorem inner_commutator_eq_zero_of_eigenvector
    {H A : 𝓗 →ₗ[ℂ] 𝓗} {ψ : 𝓗} {E : ℝ}
    (hsym : ∀ x y : 𝓗, ⟪H x, y⟫_ℂ = ⟪x, H y⟫_ℂ)
    (heig : H ψ = (E : ℂ) • ψ) :
    ⟪ψ, H (A ψ) - A (H ψ)⟫_ℂ = 0 := by
  rw [inner_sub_right, ← hsym ψ (A ψ), heig, map_smul, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- **Quantum virial theorem.**

Let `H = T + V` be a symmetric Hamiltonian on a complex inner product space, let `A` be the
generator of dilations (`A = r · p`), and let `W` be the operator `r · ∇V`.  The canonical
commutation relations give the operator identity `[H, A] = i (2T - r·∇V)` (hypothesis `hcomm`,
needed only at the state `ψ`).  Then for a bound stationary state `ψ`, i.e. a normalized
eigenvector of `H` with real energy `E`, one has

`2 ⟨T⟩ = ⟨r · ∇V⟩`.

The normalization hypothesis `hnorm` records that `ψ` is a bound (normalizable) state, as in the
physical statement; the algebraic identity itself does not need it. -/

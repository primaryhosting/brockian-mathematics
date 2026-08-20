import RequestProject.LSM.Ground

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line, because Lean 4 requires the
`import` commands to be the very first commands of a file.)

## Statement

A half-integer-spin translation-invariant chain is gapless or degenerate.

We formalise this for the spin-`1/2` XY chain with `L` sites and periodic boundary
conditions, whose Hilbert space is `Phys.Chain L = EuclideanSpace ℂ (Fin L → Bool)` and
whose Hamiltonian `Phys.hamOp L` is the translation invariant nearest neighbour exchange
Hamiltonian `-∑ⱼ (S⁺ⱼ S⁻ⱼ₊₁ + S⁻ⱼ S⁺ⱼ₊₁)`.

The theorem `Phys.lieb_schultz_mattis` states the LSM dichotomy in finite volume: either
the ground state is degenerate (there are two orthogonal ground states), or there is a
state orthogonal to the ground state whose energy exceeds the ground state energy by at
most `2π²/L`.  Since this bound tends to `0` as `L → ∞`
(`Phys.lieb_schultz_mattis_bound_tendsto_zero`), the chain is gapless or degenerate.

The proof is the Lieb-Schultz-Mattis twist argument: the twist operator
`U = exp (i (2π/L) ∑ⱼ j Sᶻⱼ)` produces a variational state of energy `cos (2π/L) E₀`,
and it satisfies the *anomalous* commutation relation `T U = -e^{-i(2π/L)Sᶻ} U T` with the
translation `T`.  The crucial sign `-1` is `exp (2π i Sᶻ)` for the half-integer spin `Sᶻ`
carried by the site that wraps around the chain; it forces the twisted state to be
orthogonal to any non-degenerate (hence translation invariant) ground state.
-/

namespace Phys

open scoped ComplexConjugate

instance instNontrivialChain (L : ℕ) : Nontrivial (Chain L) := by
  have : Nonempty (Conf L) := ⟨fun _ => true⟩
  infer_instance

/-- **Lieb-Schultz-Mattis theorem** for the translation invariant spin-`1/2` (half-integer
spin) XY chain with `L ≥ 2` sites and periodic boundary conditions:

either the ground state is degenerate, or there is an excited state whose energy lies
within `2π²/L` of the ground state energy.  As `L → ∞` this bound tends to zero: the chain
is gapless or degenerate. -/

theorem eigen_of_commuting {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {ψ : E}
    (hψ : IsGroundState H ψ) (hnd : ∀ φ : E, IsGroundState H φ → ∃ a : ℂ, φ = a • ψ)
    (A : E →L[ℂ] E) (hA : ∀ x, A (H x) = H (A x)) (hAψ : A ψ ≠ 0) :
    ∃ a : ℂ, A ψ = a • ψ := by
  set c : ℝ := ‖A ψ‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hAψ
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  set φ : E := (c⁻¹ : ℂ) • A ψ with hφdef
  have hφnorm : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul]
    simp [hc]
    field_simp
  have hHφ : H φ = (energy H ψ : ℂ) • φ := by
    have h1 : H (A ψ) = A (H ψ) := (hA ψ).symm
    rw [hφdef, ContinuousLinearMap.map_smul, h1, hψ.eigen hH, ContinuousLinearMap.map_smul,
      smul_comm]
  obtain ⟨a, ha⟩ := hnd φ (isGroundState_of_eigen hψ hφnorm hHφ)
  refine ⟨(c : ℂ) * a, ?_⟩
  have h2 : A ψ = (c : ℂ) • φ := by
    rw [hφdef, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  rw [h2, ha, smul_smul]

/-- If some ground state is not a multiple of `ψ`, then the ground state is degenerate. -/

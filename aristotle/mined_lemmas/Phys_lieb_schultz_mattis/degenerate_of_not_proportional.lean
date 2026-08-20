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

theorem degenerate_of_not_proportional {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) {ψ φ : E}
    (hψ : IsGroundState H ψ) (hφ : IsGroundState H φ) (h : ∀ a : ℂ, φ ≠ a • ψ) :
    Degenerate H := by
  set E₀ : ℝ := energy H ψ with hE₀
  have hEφ : energy H φ = E₀ := le_antisymm (by
      have h1 := hψ.2 φ hφ.1
      have h2 := hφ.2 ψ hψ.1
      linarith) (hψ.2 φ hφ.1)
  set v : E := φ - (inner ℂ ψ φ) • ψ with hv
  have hvne : v ≠ 0 := by
    intro h0
    exact h (inner ℂ ψ φ) (by rw [hv, sub_eq_zero] at h0; exact h0)
  have hvnorm : ‖(‖v‖⁻¹ : ℂ) • v‖ = 1 := by
    rw [norm_smul]
    simp [norm_ne_zero_iff.mpr hvne]
  have hHv : H ((‖v‖⁻¹ : ℂ) • v) = (E₀ : ℂ) • ((‖v‖⁻¹ : ℂ) • v) := by
    have h1 : H v = (E₀ : ℂ) • v := by
      rw [hv, map_sub, ContinuousLinearMap.map_smul, hψ.eigen hH,
        show H φ = (E₀ : ℂ) • φ from by rw [← hEφ]; exact hφ.eigen hH]
      rw [smul_sub, smul_comm]
    rw [ContinuousLinearMap.map_smul, h1, smul_comm]
  refine ⟨ψ, (‖v‖⁻¹ : ℂ) • v, hψ, isGroundState_of_eigen hψ hvnorm hHv, ?_⟩
  rw [inner_smul_right, hv, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hψ.1]
  simp

omit [FiniteDimensional ℂ E] in
/-- **The core Lieb-Schultz-Mattis mechanism.**
If the ground state `ψ` is non-degenerate, `T` is a symmetry of `H` preserving the inner
product, and `U` preserves norms and satisfies the anomalous relation `T (U ψ) = c • U (T ψ)`
with `c ≠ 1`, then the twisted state `U ψ` is orthogonal to `ψ`; if moreover its energy
exceeds the ground state energy by at most `ε`, the system has an excitation of energy
at most `ε`. -/

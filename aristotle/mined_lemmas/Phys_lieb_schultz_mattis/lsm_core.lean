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

theorem lsm_core {H T U : E →L[ℂ] E} {ψ : E} {c : ℂ} {ε : ℝ}
    (hψ : IsGroundState H ψ)
    (hnd : ∀ φ : E, IsGroundState H φ → ∃ a : ℂ, φ = a • ψ)
    (hT : ∀ x y : E, inner ℂ (T x) (T y) = inner ℂ x y)
    (hTH : ∀ x, H (T x) = T (H x))
    (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (hanom : T (U ψ) = c • U (T ψ)) (hc : c ≠ 1)
    (henergy : energy H (U ψ) ≤ energy H ψ + ε) :
    HasLowExcitation H ε := by
  have hTnorm : ∀ x : E, ‖T x‖ = ‖x‖ := by
    intro x
    have h0 := hT x x
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
    have h1 : (‖T x‖ : ℝ) ^ 2 = (‖x‖ : ℝ) ^ 2 := by exact_mod_cast h0
    nlinarith [norm_nonneg (T x), norm_nonneg x]
  have hTgs : IsGroundState H (T ψ) := by
    refine ⟨by rw [hTnorm, hψ.1], ?_⟩
    have h2 : energy H (T ψ) = energy H ψ := by rw [energy, hTH, hT, ← energy]
    rw [h2]; exact hψ.2
  obtain ⟨a, ha⟩ := hnd (T ψ) hTgs
  have hanorm : ‖a‖ = 1 := by
    have h1 : ‖T ψ‖ = 1 := by rw [hTnorm, hψ.1]
    rw [ha, norm_smul, hψ.1, mul_one] at h1
    exact h1
  have haa : (starRingEnd ℂ) a * a = 1 := by
    rw [mul_comm, Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, hanorm]
  have hortho : inner ℂ ψ (U ψ) = (0 : ℂ) := by
    have key : inner ℂ ψ (U ψ) = c * inner ℂ ψ (U ψ) := by
      calc inner ℂ ψ (U ψ) = inner ℂ (T ψ) (T (U ψ)) := (hT _ _).symm
      _ = inner ℂ (a • ψ) (c • U (a • ψ)) := by rw [hanom, ha]
      _ = (starRingEnd ℂ) a * (c * (a * inner ℂ ψ (U ψ))) := by
            rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right,
              inner_smul_right]
      _ = ((starRingEnd ℂ) a * a) * (c * inner ℂ ψ (U ψ)) := by ring
      _ = c * inner ℂ ψ (U ψ) := by rw [haa, one_mul]
    have h3 : (1 - c) * inner ℂ ψ (U ψ) = 0 := by rw [sub_mul, one_mul, ← key]; ring
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hc
    · exact h
  exact ⟨ψ, U ψ, hψ, by rw [hU, hψ.1], hortho, henergy⟩

end

end Phys

import RequestProject.LSM.Chain

/-!
# Operator properties of the spin-1/2 XY chain

Self-adjointness of the Hamiltonian, unitarity of the translation operator, the
commutation relations of the Hamiltonian with the translation and with the magnetization
sector projections, complex conjugation, and elementary bounds on the energy.
-/

namespace Phys

open scoped ComplexConjugate
open Complex Finset

variable {L : ℕ} [NeZero L]

omit [NeZero L] in
/-- The inner product of `Chain L` in coordinates. -/

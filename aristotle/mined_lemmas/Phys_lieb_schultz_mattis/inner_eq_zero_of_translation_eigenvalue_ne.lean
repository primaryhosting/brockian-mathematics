/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Momentum selection rule.**  If `T` preserves the inner product (a translation
operator is unitary) and two states are `T`-eigenvectors with *different* eigenvalues,
the first one being a unit vector, then the two states are orthogonal.

This is the step of the Lieb–Schultz–Mattis argument which guarantees that the twisted
state, carrying a different lattice momentum, is orthogonal to the ground state. -/

theorem inner_eq_zero_of_translation_eigenvalue_ne
    {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    {ψ φ : E} {t s : ℂ} (ht : ‖ψ‖ = 1)
    (hψ : T ψ = t • ψ) (hφ : T φ = s • φ) (hne : s ≠ t) :
    ⟪ψ, φ⟫_ℂ = 0 := by
  -- `|t| = 1`, i.e. `conj t * t = 1`
  have hnorm : (starRingEnd ℂ) t * t = 1 := by
    have h := hT ψ ψ
    rw [hψ, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), ht] at h
    simpa using h
  have key : (starRingEnd ℂ) t * s * ⟪ψ, φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
    have h := hT ψ φ
    rw [hψ, hφ, inner_smul_left, inner_smul_right, ← mul_assoc] at h
    exact h
  have key' : ((starRingEnd ℂ) t * s - 1) * ⟪ψ, φ⟫_ℂ = 0 := by linear_combination key
  rcases mul_eq_zero.1 key' with h | h
  · -- `conj t * s = 1` together with `conj t * t = 1` forces `s = t`, a contradiction
    exact absurd (by linear_combination t * h - s * hnorm : s = t) hne
  · exact h

/-- **Lieb–Schultz–Mattis theorem (operator core).**

A translation-invariant spin chain whose sites carry *half-integer* spin
`S = twoS / 2` (with `twoS` odd) cannot have a unique ground state separated by a gap
larger than the twist energy `ε`: it is either degenerate or gapless.

Formal setting.  `E` is the complex Hilbert space of the chain, `H` its Hamiltonian,
`T` the translation operator (unitary, as encoded by `hT`), and `ψ₀` a normalized
ground state of energy `E₀` (minimality of the energy is `hmin`, and `hground` says
that `ψ₀` realizes it) which, by translation invariance, carries a definite momentum
eigenvalue `t` (`hTψ`).  The Lieb–Schultz–Mattis twist operator `U` produces the
variational state `U ψ₀`, which is normalized (`hUnorm`), has energy at most `E₀ + ε`
(`hEnergy`; on a chain of `L` sites the twist estimate gives `ε = O(1/L)`), and whose
momentum is shifted by the factor `(-1) ^ twoS` relative to the ground state (`hTU`).
For half-integer spin, `twoS` is odd and this factor is `-1`, i.e. a momentum shift
by `π`.

Conclusion: there is a normalized state orthogonal to the ground state whose energy
either equals the ground-state energy (ground-state **degeneracy**) or exceeds it by
at most `ε` (**gaplessness**: the spectral gap above `ψ₀` is bounded by the twist
energy, which tends to `0` in the thermodynamic limit). -/

/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Setting

We formalise the Lieb–Schultz–Mattis (LSM) theorem in its finite-volume, variational form
(Lieb–Schultz–Mattis 1961, Affleck–Lieb 1986, Oshikawa 2000).

For each system size `L` we have a finite dimensional complex Hilbert space `E L`
(the state space of a chain of `L` sites), a self-adjoint Hamiltonian `Ham L`, and a
unitary translation operator `Tr L`.  The two physical inputs of LSM are:

* the ground state `ψ₀ L` is a translation eigenstate, `Tr L ψ₀ = ω • ψ₀` with `‖ω‖ = 1`
  (its momentum);
* for a chain with **half-integer spin per unit cell** the Lieb–Schultz–Mattis twist
  `ψ₁ L = U_twist ψ₀ L` is a normalised state whose momentum is shifted by exactly `π`,
  i.e. `Tr L ψ₁ = (-ω) • ψ₁`, and whose energy exceeds the ground energy by at most
  `C / L` (the twist is a low-energy variational state).

The theorem proved below is that these inputs are incompatible with the chain having,
for every size, a *unique* ground state separated from the rest of the spectrum by a
gap `γ > 0` that does not shrink with `L`.  In other words the chain is gapless or its
ground state is degenerate.
-/

namespace Phys

open Module

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The energy (expectation value of the Hamiltonian `H`) of a state `ψ`. -/

theorem gap_le_of_twisted_state {H : E →ₗ[ℂ] E} {U : E ≃ₗᵢ[ℂ] E} {ψ₀ ψ₁ : E}
    {E₀ γ ε : ℝ} {w : ℂ} (hw : ‖w‖ = 1)
    (h : GappedGroundState H ψ₀ E₀ γ)
    (h0 : U ψ₀ = w • ψ₀) (h1 : U ψ₁ = (-w) • ψ₁) (hnorm : ‖ψ₁‖ = 1)
    (hvar : energy H ψ₁ ≤ E₀ + ε) : γ ≤ ε := by
  have horth : inner ℂ ψ₀ ψ₁ = 0 := inner_eq_zero_of_momentum_shift hw h0 h1
  have hge : (E₀ + γ) * ‖ψ₁‖ ^ 2 ≤ energy H ψ₁ := h.energy_ge_of_orthogonal horth
  rw [hnorm] at hge
  simp only [one_pow, mul_one] at hge
  linarith

end Spectral

section LSM

variable {E : ℕ → Type*} [∀ L, NormedAddCommGroup (E L)] [∀ L, InnerProductSpace ℂ (E L)]
  [∀ L, FiniteDimensional ℂ (E L)]

/-- **Lieb–Schultz–Mattis theorem** (finite-volume variational form).

A translation-invariant chain with half-integer spin per unit cell is gapless or has a
degenerate ground state.

Hypotheses (for every system size `L`):
* `Tr L` is a unitary translation operator;
* the ground state `ψ₀ L` has translation eigenvalue `ω L` of modulus one;
* **half-integer spin**: the Lieb–Schultz–Mattis twisted state `ψ₁ L` is normalised, has
  translation eigenvalue `-(ω L)` (momentum shifted by `π`) and energy at most `E₀ L + C / L`.

Conclusion: there is *no* `γ > 0` such that at every system size the chain has a unique
ground state `ψ₀ L` of energy `E₀ L` with spectral gap `γ`.  Equivalently: either the gap
closes as `L → ∞` (gapless), or for some sizes the ground state is degenerate. -/

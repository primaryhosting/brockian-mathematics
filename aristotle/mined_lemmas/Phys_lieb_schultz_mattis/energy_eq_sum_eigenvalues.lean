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

theorem energy_eq_sum_eigenvalues {H : E →ₗ[ℂ] E} (hT : H.IsSymmetric) {n : ℕ}
    (hn : finrank ℂ E = n) (ψ : E) :
    energy H ψ = ∑ i, hT.eigenvalues hn i * ‖inner ℂ (hT.eigenvectorBasis hn i) ψ‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn with hb
  have h := b.sum_inner_mul_inner ψ (H ψ)
  have key : ∀ i : Fin n, inner ℂ ψ (b i) * inner ℂ (b i) (H ψ)
      = ((hT.eigenvalues hn i : ℂ)) * ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2 := by
    intro i
    have e1 : inner ℂ (b i) (H ψ) = ((hT.eigenvalues hn i : ℂ)) * inner ℂ (b i) ψ := by
      rw [← hT (b i) ψ, hT.apply_eigenvectorBasis hn i, ← hb, inner_smul_left]
      simp
    have e2 : inner ℂ ψ (b i) = (starRingEnd ℂ) (inner ℂ (b i) ψ) := (inner_conj_symm ψ (b i)).symm
    have e3 : (starRingEnd ℂ) (inner ℂ (b i) ψ) * inner ℂ (b i) ψ
        = ((‖inner ℂ (b i) ψ‖ : ℂ)) ^ 2 := RCLike.conj_mul _
    rw [e1, e2]
    linear_combination ((hT.eigenvalues hn i : ℂ)) * e3
  have h3 : (∑ i, inner ℂ ψ (b i) * inner ℂ (b i) (H ψ))
      = ((∑ i, hT.eigenvalues hn i * ‖inner ℂ (b i) ψ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun i _ => key i)
  rw [energy, ← h, h3, Complex.ofReal_re]

/-- **Variational form of the spectral gap.**  If `H` has a unique ground state `ψ₀` of energy
`E₀` and a spectral gap `γ`, then every state orthogonal to `ψ₀` has energy at least
`(E₀ + γ) ‖ψ‖²`.  This is the Courant–Fischer / Rayleigh-quotient input to LSM. -/

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

theorem GappedGroundState.energy_ge_of_orthogonal {H : E →ₗ[ℂ] E} {ψ₀ : E} {E₀ γ : ℝ}
    (h : GappedGroundState H ψ₀ E₀ γ) {ψ : E} (horth : inner ℂ ψ₀ ψ = 0) :
    (E₀ + γ) * ‖ψ‖ ^ 2 ≤ energy H ψ := by
  obtain ⟨hsym, _, _, hsimple, hgap⟩ := h
  have hn : finrank ℂ E = finrank ℂ E := rfl
  have hcoef : ∀ i, inner ℂ (hsym.eigenvectorBasis hn i) ψ ≠ 0 → E₀ + γ ≤ hsym.eigenvalues hn i := by
    intro i hne
    have hbnorm : ‖hsym.eigenvectorBasis hn i‖ = 1 := (hsym.eigenvectorBasis hn).orthonormal.1 i
    have hbne : hsym.eigenvectorBasis hn i ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hbnorm
      norm_num at hbnorm
    rcases hgap _ _ hbne (hsym.apply_eigenvectorBasis hn i) with heq | hle
    · exfalso
      apply hne
      have heq' : hsym.eigenvalues hn i = E₀ := by simpa using heq
      obtain ⟨c, hc⟩ := hsimple (hsym.eigenvectorBasis hn i)
        (by rw [hsym.apply_eigenvectorBasis hn i, heq']; rfl)
      rw [hc, inner_smul_left, horth, mul_zero]
    · exact hle
  rw [energy_eq_sum_eigenvalues hsym hn ψ,
    norm_sq_eq_sum_inner_sq (hsym.eigenvectorBasis hn) ψ, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  by_cases hc : inner ℂ (hsym.eigenvectorBasis hn i) ψ = 0
  · simp [hc]
  · exact mul_le_mul_of_nonneg_right (hcoef i hc) (sq_nonneg _)

omit [FiniteDimensional ℂ E] in
/-- **Momentum-`π` orthogonality.**  Two eigenstates of a unitary (here: the translation
operator) whose eigenvalues differ by a sign are orthogonal.  For a half-integer-spin chain
the Lieb–Schultz–Mattis twist shifts the momentum by exactly `π`, so the twisted state is
orthogonal to the ground state. -/

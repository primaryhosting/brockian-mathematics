import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped InnerProductSpace

/-! ## The abstract twist argument

The Lieb–Schultz–Mattis theorem states that a translation invariant spin chain with
half-integer spin per site cannot have a unique ground state separated by a spectral gap:
it is either gapless (in the thermodynamic limit) or has a degenerate ground state.

The mechanism, discovered by Lieb, Schultz and Mattis, is the *twist* (or *large gauge
transformation*) operator `U = exp (2πi/L ∑ j Sᶻⱼ)`.  Applied to the ground state it
produces a variational state whose energy exceeds the ground state energy by `O(1/L)`,
and whose momentum is shifted by exactly `π` relative to the ground state precisely
because the spin per site is half-integer.  The momentum shift forces the twisted state
to be orthogonal to the ground state, so it is a genuine low lying excitation.

`Phys.lieb_schultz_mattis` below is the general form of this argument in an arbitrary
complex inner product space: `T` is the (isometric) translation operator, `psi` a
ground state of momentum `c`, `U` the twist operator, and the hypothesis `hshift`
records the half-integer-spin momentum shift `T (U psi) = -c • (U psi)`.  The
conclusion says that the spectral gap above `psi` is at most `eps`: there is a unit
state orthogonal to `psi` whose energy is within `eps` of the ground state energy
(degeneracy when `eps = 0`, gaplessness in the thermodynamic limit when `eps = O(1/L)`).

In `Phys.SpinChain` the momentum shift hypothesis is *derived* for the concrete
spin-`1/2` chain of `L` sites in the zero magnetization sector, see
`Phys.SpinChain.trans_twist_anticomm` and
`Phys.SpinChain.lieb_schultz_mattis_spin_half_chain`.
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The energy expectation value `⟪x, A x⟫` of a state `x` for the Hamiltonian `A`. -/

theorem lieb_schultz_mattis_spin_half_chain (n : ℕ) (A : ChainSpace n →L[ℂ] ChainSpace n)
    (psi : ChainSpace n) (hpsi : ‖psi‖ = 1)
    (hsector : ∀ s, mag s ≠ 0 → psi s = 0)
    (c : ℂ) (hmom : transOp n psi = c • psi)
    (eps : ℝ) (hvar : energy A (twistOp n psi) ≤ energy A psi + eps) :
    ∃ phi : ChainSpace n, ‖phi‖ = 1 ∧ ⟪psi, phi⟫_ℂ = 0 ∧
      energy A phi ≤ energy A psi + eps := by
  refine lieb_schultz_mattis A (transOp n) (twistOp n) (transOp_inner n) psi hpsi c hmom ?_ ?_
    eps hvar
  · rw [trans_twist_anticomm n psi hsector, hmom, map_smul]
  · rw [norm_twistOp, hpsi]

end SpinChain

/-! ## Non-vacuity

A two-level realisation of the hypotheses of `Phys.lieb_schultz_mattis`
(the Pauli matrices `X` and `Z`, which anticommute, in the role of translation and
twist), showing that the hypothesis set is consistent and the theorem is not vacuous. -/

section NonVacuous

open Op

private noncomputable def pauliX : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  permOp (fun i => Equiv.swap 0 1 i)

private noncomputable def pauliZ : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  diagOp (fun i => if i = 0 then 1 else -1)

private noncomputable def plusState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun _ => ((Real.sqrt 2)⁻¹ : ℝ))


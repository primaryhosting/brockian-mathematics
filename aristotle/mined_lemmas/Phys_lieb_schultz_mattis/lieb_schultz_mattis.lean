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

theorem lieb_schultz_mattis
    (A T U : V →L[ℂ] V)
    (hT : ∀ x y : V, ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ)
    (psi : V) (hpsi : ‖psi‖ = 1)
    (c : ℂ) (hTpsi : T psi = c • psi)
    (hshift : T (U psi) = -(c • U psi))
    (hUnorm : ‖U psi‖ = 1)
    (eps : ℝ)
    (hvar : energy A (U psi) ≤ energy A psi + eps) :
    ∃ phi : V, ‖phi‖ = 1 ∧ ⟪psi, phi⟫_ℂ = 0 ∧ energy A phi ≤ energy A psi + eps := by
  refine ⟨U psi, hUnorm, ?_, hvar⟩
  have hc : (starRingEnd ℂ) c * c = 1 := by
    have h1 : ⟪T psi, T psi⟫_ℂ = ⟪psi, psi⟫_ℂ := hT psi psi
    rw [hTpsi, inner_smul_left, inner_smul_right] at h1
    have h2 : ⟪psi, psi⟫_ℂ = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hpsi]
    rw [h2] at h1
    simpa using h1
  have key : ⟪psi, U psi⟫_ℂ = -⟪psi, U psi⟫_ℂ := by
    have h1 : ⟪T psi, T (U psi)⟫_ℂ = ⟪psi, U psi⟫_ℂ := hT psi (U psi)
    rw [hTpsi, hshift, inner_neg_right, inner_smul_left, inner_smul_right,
      ← mul_assoc, hc, one_mul] at h1
    exact h1.symm
  linear_combination key / 2

/-! ## Operators on a finite configuration space -/

namespace Op

variable {ι : Type*} [Fintype ι]

/-- The diagonal (multiplication) operator with symbol `w` on `EuclideanSpace ℂ ι`. -/

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

lemma wmag_shift {n : ℕ} (s : SpinConfig (n + 1)) :
    wmag (shift s) = wmag s - mag s + (n + 1) * twoSz (s 0) := by
  simp only [wmag, mag, shift]
  rw [Fin.sum_univ_castSucc (f := fun j : Fin (n + 1) => (j.val : ℤ) * twoSz (s (j + 1))),
    Fin.sum_univ_succ (f := fun k : Fin (n + 1) => (k.val : ℤ) * twoSz (s k)),
    Fin.sum_univ_succ (f := fun k : Fin (n + 1) => twoSz (s k))]
  have h2 : (Fin.last n : Fin (n + 1)) + 1 = 0 := by simp
  simp only [Fin.coeSucc_eq_succ, h2, Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero,
    Nat.cast_add, Nat.cast_one, add_mul, one_mul, Finset.sum_add_distrib]
  ring

/-- The phase `2π/L * ∑ⱼ j Sᶻⱼ = π/L * ∑ⱼ j (2Sᶻⱼ)` of the twist operator. -/

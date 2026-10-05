import Mathlib

/-!
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting

Landauer's principle states that erasing one bit of information in contact with a
heat bath at absolute temperature `T` dissipates at least `k T log 2` of heat,
where `k` is Boltzmann's constant.

The model below is the standard thermodynamic one.  A classical bit is a two-state
system whose state is described by the probability `p` of being in the state `1`.
Its Gibbs/Shannon entropy is `k * H(p)` where `H` is the binary entropy function
(`Real.binEntropy` in Mathlib).  An erasure is a process that leaves the bit in a
*deterministic* state (`p = 0` or `p = 1`), releasing an amount of heat `heat` into
the bath.  The only physical input is the second law of thermodynamics in Clausius
form: the total entropy change (system plus bath, the bath gaining `heat / T`) is
nonnegative.

From these hypotheses we derive the Landauer bound `k * T * log 2 ≤ heat` for the
erasure of an initially unbiased (`p = 1/2`) bit.  The key Mathlib inputs are
`Real.binEntropy_two_inv : Real.binEntropy 2⁻¹ = Real.log 2` and
`Real.binEntropy_eq_zero : Real.binEntropy p = 0 ↔ p = 0 ∨ p = 1`.
-/

namespace Phys

open Real

/-- Thermodynamic (Gibbs) entropy of a classical bit which is in state `1` with
probability `p`, for a Boltzmann constant `k`. -/

theorem heat_ge_temperature_mul_entropy :
    E.k * E.T * Real.binEntropy E.pInit ≤ E.heat := by
  have hT := E.T_pos
  have h := E.second_law
  rw [bitEntropy_of_deterministic E.k E.erases, zero_sub, bitEntropy] at h
  have h' : E.k * Real.binEntropy E.pInit ≤ E.heat / E.T := by linarith
  have h2 := (le_div_iff₀ hT).1 h'
  calc E.k * E.T * Real.binEntropy E.pInit
      = E.k * Real.binEntropy E.pInit * E.T := by ring
    _ ≤ E.heat := h2

end BitErasure

/-- **Landauer's principle.**  Erasing one bit of information — i.e. driving an
unbiased (`pInit = 1/2`) classical bit into a deterministic state, in contact with a
heat bath at absolute temperature `T`, in a way consistent with the second law of
thermodynamics — dissipates at least `k T log 2` of heat into the bath. -/

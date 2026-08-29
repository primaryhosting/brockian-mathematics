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

lemma bitEntropy_of_deterministic {p : ℝ} (k : ℝ) (hp : p = 0 ∨ p = 1) :
    bitEntropy k p = 0 := by
  rw [bitEntropy, Real.binEntropy_eq_zero.2 hp, mul_zero]

/-- The entropy of a bit never exceeds `k * log 2`, attained exactly by the
unbiased bit; this is why one bit of erased information costs `k T log 2`. -/

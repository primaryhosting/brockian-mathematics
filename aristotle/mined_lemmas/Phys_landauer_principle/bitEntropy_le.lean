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

lemma bitEntropy_le {k : ℝ} (hk : 0 ≤ k) (p : ℝ) : bitEntropy k p ≤ k * Real.log 2 :=
  mul_le_mul_of_nonneg_left (Real.binEntropy_le_log_two) hk

/-- An erasure process for a classical bit in contact with a heat bath.

* `k` is Boltzmann's constant and `T > 0` the absolute temperature of the bath;
* `pInit` is the probability that the bit is in state `1` before the process;
* the process is an *erasure*: it leaves the bit in a deterministic state `pFinal`;
* `heat` is the heat released by the system into the bath, so the bath's entropy
  increases by `heat / T`;
* `second_law` is the Clausius inequality: the total entropy change of system plus
  bath is nonnegative.
-/
structure BitErasure where
  /-- Boltzmann constant. -/
  k : ℝ
  /-- Absolute temperature of the heat bath. -/
  T : ℝ
  /-- Probability that the bit is in state `1` before the erasure. -/
  pInit : ℝ
  /-- Probability that the bit is in state `1` after the erasure. -/
  pFinal : ℝ
  /-- Heat released into the bath during the process. -/
  heat : ℝ
  /-- Boltzmann's constant is positive. -/
  k_pos : 0 < k
  /-- The bath has positive absolute temperature. -/
  T_pos : 0 < T
  /-- The process erases the bit: the final state is deterministic. -/
  erases : pFinal = 0 ∨ pFinal = 1
  /-- Second law of thermodynamics (Clausius form): the entropy change of the bit
  plus the entropy `heat / T` gained by the bath is nonnegative. -/
  second_law : 0 ≤ (bitEntropy k pFinal - bitEntropy k pInit) + heat / T

namespace BitErasure

variable (E : BitErasure)

/-- General Landauer bound: erasing a bit whose initial entropy is `k * H(pInit)`
dissipates at least `k * T * H(pInit)` of heat. -/

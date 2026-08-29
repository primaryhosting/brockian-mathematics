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
noncomputable def bitEntropy (k p : ℝ) : ℝ := k * Real.binEntropy p

@[simp] lemma bitEntropy_two_inv (k : ℝ) : bitEntropy k (1 / 2) = k * Real.log 2 := by
  rw [bitEntropy, one_div, Real.binEntropy_two_inv]

/-- A deterministic bit carries no entropy. -/
lemma bitEntropy_of_deterministic {p : ℝ} (k : ℝ) (hp : p = 0 ∨ p = 1) :
    bitEntropy k p = 0 := by
  rw [bitEntropy, Real.binEntropy_eq_zero.2 hp, mul_zero]

/-- The entropy of a bit never exceeds `k * log 2`, attained exactly by the
unbiased bit; this is why one bit of erased information costs `k T log 2`. -/
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
theorem landauer_principle (E : BitErasure) (hInit : E.pInit = 1 / 2) :
    E.k * E.T * Real.log 2 ≤ E.heat := by
  have := E.heat_ge_temperature_mul_entropy
  rw [hInit, one_div, Real.binEntropy_two_inv] at this
  exact this

/-- Erasure always dissipates a strictly positive amount of heat. -/
theorem landauer_heat_pos (E : BitErasure) (hInit : E.pInit = 1 / 2) : 0 < E.heat :=
  lt_of_lt_of_le
    (mul_pos (mul_pos E.k_pos E.T_pos) (Real.log_pos (by norm_num)))
    (landauer_principle E hInit)

end Phys

import Mathlib

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


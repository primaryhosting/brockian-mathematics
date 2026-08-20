/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

set_option grind.warning false

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

theorem sampling_failure_prob {n : ℕ} (s : BV n) :
    ((badSamples s (2 * n)).card : ℝ) / ((allSamples s (2 * n)).card : ℝ) ≤ 1 / 2 ^ n := by
  have hb := sampling_failure_bound s (2 * n)
  have hpos : 0 < (allSamples s (2 * n)).card := by
    rw [card_allSamples]
    exact pow_pos (card_Orth_pos s) _
  have hposR : (0:ℝ) < ((allSamples s (2 * n)).card : ℝ) := by exact_mod_cast hpos
  rw [div_le_div_iff₀ hposR (by positivity)]
  have hbR : ((badSamples s (2*n)).card : ℝ) * 2 ^ (2 * n) ≤ 2 ^ n * ((allSamples s (2*n)).card : ℝ) := by
    exact_mod_cast hb
  have hsplit : (2:ℝ) ^ (2 * n) = 2 ^ n * 2 ^ n := by
    rw [← pow_add]; ring_nf
  nlinarith [hbR, hposR, pow_pos (show (0:ℝ) < 2 by norm_num) n]

end QI

import RequestProject.Simon.Defs

/-!
# The quantum part of Simon's algorithm

We describe the quantum circuit of Simon's algorithm on `2n` qubits explicitly, at the level of
amplitudes: a state is a function `BV n → BV n → ℂ` assigning an amplitude to every computational
basis state `|x⟩|v⟩`.

The circuit is:

* start in `|0⟩|0⟩`;
* apply a Hadamard transform to the first register;
* apply the (single) oracle query `|x⟩|v⟩ ↦ |x⟩|v + f x⟩`;
* apply a Hadamard transform to the first register;
* measure the first register.

The main result, `QI.simonProb_eq`, states that the outcome distribution of the measurement is
uniform on the hyperplane `{y | dot y s = 0}`; in particular a single query already yields a
uniformly random vector orthogonal to the hidden period `s`.
-/

namespace QI

open Finset

/-- The real character `(-1)^a` of `ZMod 2`. -/

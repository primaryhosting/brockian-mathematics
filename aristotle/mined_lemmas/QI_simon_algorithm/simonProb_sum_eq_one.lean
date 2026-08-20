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

theorem simonProb_sum_eq_one {n : ℕ} {f : BV n → BV n} {s : BV n} (h : SimonPromise f s) :
    ∑ y : BV n, simonProb f y = 1 := by
  classical
  have hcong : ∀ y : BV n, simonProb f y = if y ∈ Orth s then (2 : ℝ) / 2 ^ n else 0 := by
    intro y
    rw [simonProb_eq h y]
    by_cases hy : dot y s = 0
    · rw [if_pos (by rw [dot_comm]; exact hy), if_pos (mem_Orth s y |>.mpr hy)]
    · rw [if_neg (by rw [dot_comm]; exact hy), if_neg (fun hc => hy ((mem_Orth s y).mp hc))]
  simp only [hcong]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : 2 * (Orth s).card = 2 ^ n := card_Orth s h.ne_zero
  have hcardR : ((Orth s).card : ℝ) * 2 = 2 ^ n := by
    have : ((2 * (Orth s).card : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) := by rw [hcard]
    push_cast at this
    linarith
  have hpos : ((2 : ℝ) ^ n) ≠ 0 := by positivity
  field_simp
  linarith [hcardR]

/-- The samples pin down the period uniquely among nonzero vectors. -/

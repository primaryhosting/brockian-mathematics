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

lemma bruteForce_transcript {n : ℕ} (f : BV n → BV n) (k : ℕ) :
    transcript (bruteForce n) f k = (List.range k).map (fun i => (enumBV n i, f (enumBV n i))) := by
  induction k with
  | zero => simp [transcript]
  | succ k ih =>
      have hlen : ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))).length = k := by
        simp
      have hquery : (bruteForce n).query
          ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))) = enumBV n k := by
        show enumBV n ((List.range k).map (fun i => (enumBV n i, f (enumBV n i)))).length = _
        rw [hlen]
      rw [transcript, ih, hquery, List.range_succ]
      simp

/-- The brute-force algorithm solves Simon's problem with `2ⁿ` queries. -/

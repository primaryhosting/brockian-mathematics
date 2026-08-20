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

lemma exists_enumBV (n : ℕ) (v : BV n) : ∃ i < 2 ^ n, enumBV n i = v := by
  classical
  have hmem : v ∈ (Finset.univ : Finset (BV n)).toList := by simp
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlen : ((Finset.univ : Finset (BV n)).toList).length = 2 ^ n := by
    rw [Finset.length_toList, Finset.card_univ]
    simp
  refine ⟨i, by omega, ?_⟩
  rw [enumBV, List.getD_eq_getElem _ _ hi, hget]

open Classical in
/-- The brute-force classical algorithm: query all points, then output the unique nonzero
difference of two points with equal values. -/

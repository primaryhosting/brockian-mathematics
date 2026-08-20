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

lemma card_Orth_inter {n : ℕ} (s t : BV n) (ht : t ≠ 0) (hst : s ≠ t) :
    2 * (Orth s ∩ Orth t).card = (Orth s).card := by
  classical
  obtain ⟨v, hvs, hvt⟩ := exists_dot_zero_one s t hst ht
  have hinv : ∀ y : BV n, y + v ∈ Orth s ↔ y ∈ Orth s := by
    intro y
    simp only [mem_Orth, dot_add_left, hvs, add_zero]
  have hfilter : (Orth s).filter (fun y => dot y t = 0) = Orth s ∩ Orth t := by
    ext y
    simp [Finset.mem_filter, Finset.mem_inter]
  have := card_filter_dot_eq_zero (Orth s) v t hinv hvt
  rwa [hfilter] at this

/-- The samples `y` determine the period `s`: the only vectors orthogonal to all of them are
`0` and `s`. -/

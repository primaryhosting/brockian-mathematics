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

lemma card_filter_dot_eq_zero {n : ℕ} (A : Finset (BV n)) (w u : BV n)
    (hA : ∀ y : BV n, y + w ∈ A ↔ y ∈ A) (hw : dot w u = 1) :
    2 * (A.filter (fun y => dot y u = 0)).card = A.card := by
  classical
  set A0 := A.filter (fun y => dot y u = 0) with hA0
  set A1 := A.filter (fun y => dot y u = 1) with hA1
  have hbij : A0.card = A1.card := by
    refine Finset.card_bij (fun y _ => y + w) ?_ ?_ ?_
    · intro y hy
      simp only [hA1, hA0, Finset.mem_filter] at hy ⊢
      refine ⟨(hA y).2 hy.1, ?_⟩
      rw [dot_add_left, hy.2, hw, zero_add]
    · intro y hy z hz hyz
      exact add_right_cancel hyz
    · intro z hz
      simp only [hA1, Finset.mem_filter] at hz
      refine ⟨z + w, ?_, ?_⟩
      · simp only [hA0, Finset.mem_filter]
        refine ⟨(hA z).2 hz.1, ?_⟩
        rw [dot_add_left, hz.2, hw]
        decide
      · show z + w + w = z
        rw [add_assoc]
        simp
  have hfe : A.filter (fun y => ¬ (dot y u = 0)) = A1 := by
    refine Finset.filter_congr ?_
    intro y _
    rcases zmod2_cases (dot y u) with h | h <;> simp [h]
  have hunion : A0.card + A1.card = A.card := by
    rw [hA0, ← hfe]
    exact Finset.card_filter_add_card_filter_not (fun y => dot y u = 0)
  omega

/-- For `s ≠ 0`, exactly half of all bit strings are orthogonal to `s`. -/

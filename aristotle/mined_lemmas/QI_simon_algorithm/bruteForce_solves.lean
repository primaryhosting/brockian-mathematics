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

theorem bruteForce_solves (n : ℕ) : (bruteForce n).Solves (2 ^ n) := by
  classical
  intro f s hf
  set h := transcript (bruteForce n) f (2 ^ n) with hh
  have hmem : ∀ p ∈ h, p = (p.1, f p.1) := by
    intro p hp
    rw [hh, bruteForce_transcript] at hp
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨i, _, hi⟩ := hp
    rw [← hi]
  have hq : ∀ v : BV n, (v, f v) ∈ h := by
    intro v
    obtain ⟨i, hi, hv⟩ := exists_enumBV n v
    rw [hh, bruteForce_transcript]
    simp only [List.mem_map, List.mem_range]
    exact ⟨i, hi, by rw [hv]⟩
  have hfilter : (Finset.univ : Finset (BV n)).filter
      (fun t => t ≠ 0 ∧ ∃ p ∈ h, ∃ q ∈ h, p.2 = q.2 ∧ p.1 + q.1 = t) = {s} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨ht0, p, hp, q, hqm, hpq, hsum⟩
      have hp' := hmem p hp
      have hq' := hmem q hqm
      have hval : f p.1 = f q.1 := by
        have h1 : p.2 = f p.1 := by rw [hp']
        have h2 : q.2 = f q.1 := by rw [hq']
        rw [← h1, ← h2, hpq]
      rcases (hf.fibre p.1 q.1).1 hval with hc | hc
      · exfalso
        apply ht0
        rw [← hsum, hc]
        simp
      · rw [← hsum, hc, ← add_assoc]
        simp
    · intro hts
      rw [hts]
      refine ⟨hf.ne_zero, (0, f 0), hq 0, (0 + s, f (0 + s)), hq _, ?_, ?_⟩
      · exact (hf.period 0).symm
      · simp
  show (bruteForce n).output h = s
  rw [bruteForce]
  simp only
  rw [hfilter, Finset.sum_singleton]

/-- There is a deterministic classical algorithm solving Simon's problem (with `2ⁿ` queries), so
the lower bound `QI.classical_query_lower_bound` is not vacuous. -/

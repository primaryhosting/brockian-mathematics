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

theorem sampling_failure_bound {n : ℕ} (s : BV n) (m : ℕ) :
    (badSamples s m).card * 2 ^ m ≤ 2 ^ n * (allSamples s m).card := by
  classical
  set S : Finset (BV n) := Finset.univ \ {0, s} with hS
  have hsub : badSamples s m ⊆
      S.biUnion (fun t => Fintype.piFinset (fun _ : Fin m => Orth s ∩ Orth t)) := by
    intro y hy
    simp only [badSamples, Finset.mem_filter] at hy
    obtain ⟨hyall, hybad⟩ := hy
    rw [Determines] at hybad
    push_neg at hybad
    obtain ⟨t, hto, ht0, hts⟩ := hybad
    refine Finset.mem_biUnion.mpr ⟨t, ?_, ?_⟩
    · simp [hS, ht0, hts]
    · refine Fintype.mem_piFinset.mpr (fun i => ?_)
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact (Fintype.mem_piFinset.mp hyall) i
      · exact mem_Orth _ _ |>.mpr (hto i)
  have hcard : (badSamples s m).card
      ≤ ∑ t ∈ S, (Orth s ∩ Orth t).card ^ m := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [Fintype.card_piFinset]
    simp
  have hterm : ∀ t ∈ S, (Orth s ∩ Orth t).card ^ m * 2 ^ m = (Orth s).card ^ m := by
    intro t htS
    have ht0 : t ≠ 0 := by
      intro h; rw [hS] at htS; simp [h] at htS
    have hts : s ≠ t := by
      intro h; rw [hS] at htS; simp [← h] at htS
    have h2 := card_Orth_inter s t ht0 hts
    calc (Orth s ∩ Orth t).card ^ m * 2 ^ m
        = (2 * (Orth s ∩ Orth t).card) ^ m := by rw [mul_pow]; ring
      _ = (Orth s).card ^ m := by rw [h2]
  calc (badSamples s m).card * 2 ^ m
      ≤ (∑ t ∈ S, (Orth s ∩ Orth t).card ^ m) * 2 ^ m := Nat.mul_le_mul_right _ hcard
    _ = ∑ t ∈ S, (Orth s ∩ Orth t).card ^ m * 2 ^ m := by rw [Finset.sum_mul]
    _ = ∑ _t ∈ S, (Orth s).card ^ m := Finset.sum_congr rfl hterm
    _ = S.card * (Orth s).card ^ m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (Orth s).card ^ m := by
        refine Nat.mul_le_mul_right _ ?_
        calc S.card ≤ (Finset.univ : Finset (BV n)).card := Finset.card_le_card (by simp [hS])
          _ = 2 ^ n := by simp [Finset.card_univ]
    _ = 2 ^ n * (allSamples s m).card := by rw [card_allSamples]


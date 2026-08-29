import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set


private lemma exists_colour_mem (U : Ultrafilter ℕ) (f : ℕ → Fin 2) :
    ∃ j : Fin 2, {n | f n = j} ∈ U := by
  by_cases h : {n | f n = 0} ∈ U
  · exact ⟨0, h⟩
  · refine ⟨1, ?_⟩
    have hset : {n | f n = 1} = {n | f n = 0}ᶜ := by
      ext n
      simp only [mem_setOf_eq, mem_compl_iff, fin2_eq_one_iff, ne_eq]
    rw [hset]
    exact Ultrafilter.compl_mem_iff_notMem.2 h

/-- Choose an element of a set (junk value `0` if empty). -/
private noncomputable def pick (T : Set ℕ) : ℕ :=
  open Classical in if h : T.Nonempty then h.choose else 0


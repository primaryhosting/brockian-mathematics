/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-- The (classical) pumping property of a language `L`: there is a pumping length `p > 0`
such that every word `w ∈ L` of length at least `p` can be split as `w = x ++ y ++ z`
with `|x ++ y| ≤ p`, `y ≠ []`, and `x ++ yⁿ ++ z ∈ L` for every `n : ℕ`. -/
def PumpingProperty {α : Type*} (L : Language α) : Prop :=
  ∃ p : ℕ, 0 < p ∧ ∀ w ∈ L, p ≤ w.length →
    ∃ x y z : List α, w = x ++ y ++ z ∧ (x ++ y).length ≤ p ∧ y ≠ [] ∧
      ∀ n : ℕ, x ++ (List.replicate n y).flatten ++ z ∈ L

/-- Auxiliary: any finite concatenation of copies of `b` lies in the Kleene star `{b}∗`. -/
theorem replicate_flatten_mem_kstar {α : Type*} (b : List α) (n : ℕ) :
    (List.replicate n b).flatten ∈ ({b} : Language α)∗ := by
  rw [Language.mem_kstar]
  refine ⟨List.replicate n b, rfl, ?_⟩
  intro y hy
  rw [List.eq_of_mem_replicate hy]
  exact Set.mem_singleton _

/-- **Pumping lemma.** Every regular language satisfies the pumping property. -/
theorem pumping_regular {α : Type} (L : Language α) (hL : L.IsRegular) :
    PumpingProperty L := by
  obtain ⟨σ, hσ, M, hM⟩ := hL
  refine ⟨Fintype.card σ + 1, Nat.succ_pos _, ?_⟩
  intro w hw hlen
  have hwM : w ∈ M.accepts := by rw [hM]; exact hw
  obtain ⟨x, y, z, hsplit, hxy, hy, hsub⟩ :=
    M.pumping_lemma hwM (le_trans (Nat.le_succ _) hlen)
  refine ⟨x, y, z, hsplit, ?_, hy, ?_⟩
  · simpa [List.length_append] using Nat.le_succ_of_le hxy
  · intro n
    have hmem : x ++ (List.replicate n y).flatten ++ z ∈ M.accepts := by
      apply hsub
      refine ⟨x ++ (List.replicate n y).flatten, ?_, z, Set.mem_singleton _, rfl⟩
      exact ⟨x, Set.mem_singleton _, (List.replicate n y).flatten,
        replicate_flatten_mem_kstar y n, rfl⟩
    rwa [hM] at hmem

end CS


/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kraft's inequality for prefix-free binary codes

A finite set `S` of binary codewords (lists of booleans) is *prefix-free* if no codeword
is a prefix of a different codeword.  The main result, `CS.pcp_pigeon_bound`, states
Kraft's inequality: `∑ w ∈ S, (1/2) ^ w.length ≤ 1`.
-/

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of
another codeword. -/

lemma mem_tailsOf {b : Bool} {S : Finset (List Bool)} (h0 : [] ∉ S) {v : List Bool} :
    v ∈ tailsOf b S ↔ (b :: v) ∈ S := by
  classical
  constructor
  · intro hv
    simp only [tailsOf, Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨w, ⟨hwS, hwb⟩, rfl⟩ := hv
    have hne : w ≠ [] := by rintro rfl; exact h0 hwS
    have : w.headI :: w.tail = w := List.cons_head!_tail hne
    rw [hwb] at this
    rwa [this]
  · intro hv
    simp only [tailsOf, Finset.mem_image, Finset.mem_filter]
    exact ⟨b :: v, ⟨hv, rfl⟩, rfl⟩


import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Ramsey44

variable {V : Type*}

/-- `Arr G s p q` says that inside the vertex set `s` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G` (i.e. an independent set of size `q`). -/

lemma arr_33 {G : SimpleGraph V} {s : Finset V} (hs : 6 ≤ s.card) : Arr G s 3 3 := by
  obtain ⟨v, hv⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  set A := s.filter (fun u => G.Adj v u) with hAdef
  set B := s.filter (fun u => Gᶜ.Adj v u) with hBdef
  have hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u := by intro u; rw [hAdef, Finset.mem_filter]
  have hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u := by intro u; rw [hBdef, Finset.mem_filter]
  have hcard := card_split hv hA hB
  rcases le_or_gt 3 A.card with h | h
  · exact arr_step_left hv hA (arr_two_left (q := 3) h)
  · exact arr_step_right hv hB (arr_two_right (p := 3) (by omega))

/-- `R(3,4) ≤ 9`, the key parity argument. -/

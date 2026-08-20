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

lemma arr_34_eq {G : SimpleGraph V} {s : Finset V} (hs : s.card = 9) : Arr G s 3 4 := by
  by_contra hcon
  have key : ∀ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 3 := by
    intro v hv
    set A := s.filter (fun u => G.Adj v u) with hAdef
    set B := s.filter (fun u => Gᶜ.Adj v u) with hBdef
    have hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u := by intro u; rw [hAdef, Finset.mem_filter]
    have hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u := by intro u; rw [hBdef, Finset.mem_filter]
    have hcard := card_split hv hA hB
    have hA3 : A.card ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      exact hcon (arr_step_left hv hA (arr_two_left (q := 4) (by omega)))
    have hB5 : B.card ≤ 5 := by
      by_contra hlt
      push_neg at hlt
      exact hcon (arr_step_right hv hB (arr_33 (by omega)))
    omega
  have hsum : ∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card = 27 := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, hs]
    rfl
  have heven := even_sum_adj G s
  rw [hsum] at heven
  exact (by decide : ¬ Even 27) heven


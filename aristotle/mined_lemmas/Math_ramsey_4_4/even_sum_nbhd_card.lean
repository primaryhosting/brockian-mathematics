/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem even_sum_nbhd_card (T : Finset V) :
    Even (∑ v ∈ T, (nbhd G T v).card) := by
  rw [sum_nbhd_eq]
  set P := (T ×ˢ T).filter (fun p => G.Adj p.1 p.2) with hP
  have hbij : (P.filter fun p => p.1 < p.2).card = (P.filter fun p => ¬ p.1 < p.2).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, asymm hp.2⟩
    · intro p hp q hq h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [hP, Finset.mem_filter, Finset.mem_product] at hq ⊢
      refine ⟨⟨⟨hq.1.1.2, hq.1.1.1⟩, hq.1.2.symm⟩, ?_⟩
      exact lt_of_le_of_ne (not_lt.1 hq.2) hq.1.2.ne'
  have h2 := Finset.card_filter_add_card_filter_not (s := P) (fun p => p.1 < p.2)
  exact ⟨(P.filter fun p => p.1 < p.2).card, by omega⟩

/-- If some vertex `v ∈ T` has at least `q` neighbours in `T`, then inside `T` there is
either a triangle of `G` or a `q`-clique of the complement. -/

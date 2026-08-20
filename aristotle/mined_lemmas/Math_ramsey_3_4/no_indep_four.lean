/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a 3-clique) or an independent set of size 4 (a 4-clique in the complement). -/

theorem no_indep_four {a b c d : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nad : ¬ G.Adj a d)
    (nbc : ¬ G.Adj b c) (nbd : ¬ G.Adj b d) (ncd : ¬ G.Adj c d) : False := by
  refine h4 {a, b, c, d} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [coe_insert, Set.mem_insert_iff, coe_singleton, Set.mem_singleton_iff] at hx hy
    refine ⟨hxy, ?_⟩
    have hs : ∀ {u w : Fin 9}, ¬ G.Adj u w → ¬ G.Adj w u := fun h hw => h hw.symm
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | assumption
        | exact hs (by assumption)
  · rw [card_insert_of_notMem (by simp [hab, hac, had]),
      card_insert_of_notMem (by simp [hbc, hbd]),
      card_insert_of_notMem (by simp [hcd]), card_singleton]

include h3 h4 in
/-- In a triangle-free graph on 9 vertices with no independent 4-set, every degree is at most 3. -/

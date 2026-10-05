/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math

/-- `RamseyProp r s N` says: every simple graph on `N` vertices contains either a clique of
size `r` or an independent set of size `s` (i.e. an `s`-clique in the complement).
Equivalently: every 2-colouring of the edges of `K_N` has a red `K_r` or a blue `K_s`. -/

theorem no_indep (h4 : ∀ B : Finset (Fin 9), ¬ Gᶜ.IsNClique 4 B)
    {a b c d : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (n1 : ¬ G.Adj a b) (n2 : ¬ G.Adj a c) (n3 : ¬ G.Adj a d)
    (n4 : ¬ G.Adj b c) (n5 : ¬ G.Adj b d) (n6 : ¬ G.Adj c d) : False := by
  refine h4 {a, b, c, d} ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hx hy
    have s1 : ¬ G.Adj b a := fun h => n1 h.symm
    have s2 : ¬ G.Adj c a := fun h => n2 h.symm
    have s3 : ¬ G.Adj d a := fun h => n3 h.symm
    have s4 : ¬ G.Adj c b := fun h => n4 h.symm
    have s5 : ¬ G.Adj d b := fun h => n5 h.symm
    have s6 : ¬ G.Adj d c := fun h => n6 h.symm
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp_all [SimpleGraph.compl_adj]
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]

/-- If `T` is a set of three vertices, all non-adjacent to `v` and pairwise non-adjacent,
then `insert v T` is an independent set of size four. -/

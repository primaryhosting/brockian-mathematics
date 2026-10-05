/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-- The `(3,4)`-Ramsey property for `n`: every simple graph on `n` vertices contains
either a triangle (a `3`-clique) or an independent set of size `4`. -/

lemma isNIndepSet_three {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nbc : ¬ G.Adj b c) :
    G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy
        | exact nab | exact nac | exact nbc
        | exact fun h => nab h.symm | exact fun h => nac h.symm | exact fun h => nbc h.symm
  · exact Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩

/-- `R(3,3) ≤ 6`, in the form: among any 6 vertices of a graph there is either a triangle or
an independent set of size 3. -/

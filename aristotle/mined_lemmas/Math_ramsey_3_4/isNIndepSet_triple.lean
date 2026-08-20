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

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem isNIndepSet_triple {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (nab : ¬ G.Adj a b) (nac : ¬ G.Adj a c) (nbc : ¬ G.Adj b c) :
    G.IsNIndepSet 3 ({a, b, c} : Finset V) := by
  refine ⟨?_, by simp [hab, hac, hbc]⟩
  intro x hx y hy hxy
  simp only [coe_insert, Set.mem_insert_iff, coe_singleton, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hxy
      | exact nab
      | exact nac
      | exact nbc
      | exact fun h => nab h.symm
      | exact fun h => nac h.symm
      | exact fun h => nbc h.symm


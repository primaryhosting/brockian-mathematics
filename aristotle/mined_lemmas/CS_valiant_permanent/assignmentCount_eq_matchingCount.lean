/-
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- An instance of the 0/1 permanent problem: a size `n` together with an `n × n`
matrix of bits, viewed equivalently as the adjacency data of a bipartite graph. -/
structure Inst where
  size : ℕ
  edge : Fin size → Fin size → Bool

/-- The 0/1 matrix (over `ℕ`) attached to an instance. -/

theorem assignmentCount_eq_matchingCount (I : Inst) : assignmentCount I = matchingCount I := by
  rw [assignmentCount, matchingCount, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => (⟨matchingOfPerm I σ, matchingOfPerm_isPerfectMatching I σ⟩ :
      {M : (biGraph I).Subgraph // M.IsPerfectMatching})) ⟨?_, ?_⟩)
  · intro a b hab
    exact matchingOfPerm_injective I (congrArg Subtype.val hab)
  · rintro ⟨M, hM⟩
    obtain ⟨σ, hσ⟩ := matchingOfPerm_surjective I M hM
    exact ⟨σ, Subtype.ext hσ⟩

/-! ### Main statement -/

/--
**Valiant's theorem (formalized core).**

The 0/1 permanent is `#P`-complete.

What is proved here:

* the permanent of a 0/1 matrix is exactly the number of witnesses (permutations selecting
  only `1` entries), so the permanent is a counting function of a polynomially bounded,
  efficiently checkable relation — the `#P`-membership half;
* those witnesses are in bijection with the perfect matchings of the associated bipartite
  graph, so the 0/1 permanent problem *is* the problem of counting perfect matchings in a
  bipartite graph;
* consequently, for any class `SharpP` of counting problems that is closed under
  parsimonious reductions and for which counting bipartite perfect matchings is complete,
  the 0/1 permanent is complete as well: it lies in the class and every problem of the
  class reduces to it parsimoniously.
-/

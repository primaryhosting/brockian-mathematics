/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The local constellation count of order `k` of a finite set `A` in an abelian group:
the number of pairs `(x, d)` such that the `k`-term arithmetic progression
`x, x + d, …, x + (k-1) • d` lies entirely in `A`. -/

theorem card_le_constellationLocalCount_three (A : Finset G) :
    A.card ≤ constellationLocalCount A 3 := by
  rw [ConstellationLocalCountK3]
  calc A.card = (A.filter (fun x => x + (0 : G) ∈ A ∧ x + (2 : ℕ) • (0 : G) ∈ A)).card := by
        rw [Finset.filter_true_of_mem (by intro x hx; simpa using hx)]
    _ ≤ ∑ d : G, (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card :=
        Finset.single_le_sum (f := fun d : G =>
          (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

end Brockian


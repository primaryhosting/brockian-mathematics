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

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The set of base points `x` of a translate of the shift `d` landing inside `S`,
i.e. `{x | x + d ∈ S}`. -/
def shiftPreimage (S : Finset G) (d : G) : Finset G :=
  Finset.univ.filter (fun x => x + d ∈ S)

/-- The **local constellation count**: the number of base points `x` in the ambient group
such that the whole constellation `x + d 0, …, x + d (k-1)` lies inside `S`. -/
def constellationLocalCount {k : ℕ} (S : Finset G) (d : Fin k → G) : ℕ :=
  (Finset.univ.filter (fun x => ∀ i : Fin k, x + d i ∈ S)).card

/-- Translation is a bijection, so a shifted preimage has the same cardinality as `S`. -/
theorem card_shiftPreimage (S : Finset G) (d : G) :
    (shiftPreimage S d).card = S.card := by
  unfold shiftPreimage
  apply Finset.card_bij (fun x _ => x + d)
  · intro a ha; simpa [shiftPreimage] using ha
  · intro a _ b _ h; exact add_right_cancel h
  · intro b hb; exact ⟨b - d, by simp [hb], by simp⟩

omit [AddCommGroup G] in
/-- A two-set intersection bound: `|A ∩ B| + |G| ≥ |A| + |B|`. -/
theorem card_inter_add_card_univ_ge (A B : Finset G) :
    A.card + B.card ≤ (A ∩ B).card + Fintype.card G := by
  have h := Finset.card_inter_add_card_union A B
  have h2 : (A ∪ B).card ≤ Fintype.card G := by
    simpa using Finset.card_le_card (Finset.subset_univ (A ∪ B))
  omega

/-- For `k = 3`, the local constellation count is the cardinality of the intersection of the
three shifted preimages of `S`. -/
theorem constellationLocalCount_three_eq (S : Finset G) (d : Fin 3 → G) :
    constellationLocalCount S d =
      (shiftPreimage S (d 0) ∩ shiftPreimage S (d 1) ∩ shiftPreimage S (d 2)).card := by
  unfold constellationLocalCount
  congr 1
  ext x
  simp [shiftPreimage, Fin.forall_fin_succ]

/-- **Constellation local count, `k = 3`.**

In a finite abelian group `G`, for any finite set `S` and any triple of shifts
`d : Fin 3 → G`, the number of base points `x` with `x + d 0, x + d 1, x + d 2` all in `S`
satisfies the Bonferroni-type lower bound
`3 * |S| ≤ count + 2 * |G|`.

This extends the (trivial) `k = 1` count `|S|` and the `k = 2` count
`|S| + |S| ≤ count + |G|` to triples. -/
theorem ConstellationLocalCountK3 (S : Finset G) (d : Fin 3 → G) :
    3 * S.card ≤ constellationLocalCount S d + 2 * Fintype.card G := by
  rw [constellationLocalCount_three_eq]
  have h01 := card_inter_add_card_univ_ge (shiftPreimage S (d 0)) (shiftPreimage S (d 1))
  have h2 := card_inter_add_card_univ_ge
    (shiftPreimage S (d 0) ∩ shiftPreimage S (d 1)) (shiftPreimage S (d 2))
  have e0 := card_shiftPreimage S (d 0)
  have e1 := card_shiftPreimage S (d 1)
  have e2 := card_shiftPreimage S (d 2)
  omega

end Brockian

#print axioms Brockian.ConstellationLocalCountK3


/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma subterms_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) :
    subterms (subst c σ) ⊆
      (subterms c).image (fun t => subst t σ) ∪
        Finset.univ.biUnion (fun i : Fin k => subterms (σ i)) := by
  induction c with
  | var i =>
      intro t ht
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩)
  | const b =>
      intro t ht
      refine Finset.mem_union_left _ ?_
      simp only [subst, subterms, Finset.mem_singleton] at ht
      subst ht
      exact Finset.mem_image.2 ⟨const b, by simp [subterms], rfl⟩
  | not c ih =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert] at ht
      rcases ht with ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨not c, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (ih ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
  | and a b iha ihb =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert, Finset.mem_union] at ht
      rcases ht with ht | ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨and a b, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (iha ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.1 (ihb ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
  | or a b iha ihb =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert, Finset.mem_union] at ht
      rcases ht with ht | ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨or a b, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (iha ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.1 (ihb ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h

/-- Substitution costs at most the sum of the sizes: this is where the DAG size measure
(with sharing) is essential. -/

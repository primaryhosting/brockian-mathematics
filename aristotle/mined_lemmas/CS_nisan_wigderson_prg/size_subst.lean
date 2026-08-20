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

lemma size_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) :
    size (subst c σ) ≤ size c + ∑ i : Fin k, size (σ i) := by
  have h := Finset.card_le_card (subterms_subst c σ)
  have h2 : ((subterms c).image (fun t => subst t σ) ∪
      Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card
      ≤ ((subterms c).image (fun t => subst t σ)).card
        + (Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card :=
    Finset.card_union_le _ _
  have h3 : ((subterms c).image (fun t => subst t σ)).card ≤ (subterms c).card :=
    Finset.card_image_le
  have h4 : (Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card
      ≤ ∑ i : Fin k, (subterms (σ i)).card := Finset.card_biUnion_le
  simp only [size]
  omega

/-- The canonical circuit computing a function of the coordinates in the list `L`
(the other coordinates being fixed by `ρ`): a full binary decision tree. -/

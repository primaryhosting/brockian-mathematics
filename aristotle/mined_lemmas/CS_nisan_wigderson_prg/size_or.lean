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

lemma size_or {n : ℕ} (a b : Circ n) : size (or a b) ≤ 1 + size a + size b := by
  have h1 : (insert (or a b) (subterms a ∪ subterms b)).card
      ≤ (subterms a ∪ subterms b).card + 1 := Finset.card_insert_le _ _
  have h2 : (subterms a ∪ subterms b).card ≤ (subterms a).card + (subterms b).card :=
    Finset.card_union_le _ _
  simp only [size, subterms]
  omega

/-- Substitution of circuits for the input variables of a circuit. -/

/-
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
This file formalizes the statement that a (strongly) inaccessible cardinal `κ` yields a model of
`ZFC`, namely the rank-initial segment `V κ = {x : ZFSet | rank x < κ.ord}` of the von Neumann
hierarchy, and deduces the semantic consistency statement `Con(ZFC)` (i.e. satisfiability of the
first-order theory `ZFCTheory`) from the existence of an inaccessible cardinal.
-/

universe u

namespace Frontier

open FirstOrder Language Cardinal Ordinal ZFSet

/-! ## The first-order language of set theory -/

/-- The relations of the language of set theory: a single binary relation `∈`. -/
inductive memRel : ℕ → Type
  | mem : memRel 2

/-- The first-order language of set theory: one binary relation symbol, no functions. -/

theorem val_lemma3 (xs : Fin n → M) (a b x y : M) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) x) y : Fin (n + 4) → M) ∘
      (fun i : Fin (n + 2) => if (i : ℕ) < n then Fin.castAdd 2 i else Fin.addNat i 2)
      = Fin.snoc (Fin.snoc xs x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
  · simp
  · have h : (((Fin.last n).castSucc).addNat 2 : Fin (n + 4)) = (Fin.last (n + 2)).castSucc :=
      Fin.ext (by simp)
    simp [h]
  · have h : (Fin.castAdd 2 (Fin.castSucc (Fin.castSucc k)) : Fin (n + 4))
        = (((k.castSucc).castSucc).castSucc).castSucc := Fin.ext (by simp)
    simp [h]

end Snoc

/-! ### What the axioms say in an arbitrary structure

These lemmas make the content of each axiom explicit, independently of any particular model. -/

section Faithful

variable {M : Type*} [setLang.Structure M] {n : ℕ}

/-- The interpretation of the membership symbol in an arbitrary structure. -/
abbrev MemR (x y : M) : Prop := Structure.RelMap (M := M) memSymb ![x, y]


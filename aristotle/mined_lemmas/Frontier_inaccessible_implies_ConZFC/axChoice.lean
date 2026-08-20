import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order

/-! ## The first-order language of set theory -/

/-- The relation symbols of the language of set theory: a single binary symbol `∈`. -/
inductive memRelSym : ℕ → Type
  | mem : memRelSym 2

/-- The first-order language of set theory: no function symbols, one binary relation `∈`. -/

def axChoice : setLang.Sentence :=
  ∀' (((∀' ((memF (&1) (&0)) ⟹ ∃' (memF (&2) (&1)))) ⊓
       (∀' ((memF (&1) (&0)) ⟹ ∀' ((memF (&2) (&0)) ⟹
         ((&1 =' &2) ⊔ ∀' ∼((memF (&3) (&1)) ⊓ (memF (&3) (&2)))))))) ⟹
    ∃' (∀' ((memF (&2) (&0)) ⟹
      ∃' (((memF (&3) (&2)) ⊓ (memF (&3) (&1))) ⊓
        ∀' (((memF (&4) (&2)) ⊓ (memF (&4) (&1))) ⟹ (&4 =' &3))))))

/-- The separation schema. For a formula `φ` whose free variables are `n` parameters together
with two bound variables, standing for the ambient set `x` and the element `z`, this is the
sentence `∀ params, ∀ x, ∃ y, ∀ z, (z ∈ y ↔ z ∈ x ∧ φ)`. -/

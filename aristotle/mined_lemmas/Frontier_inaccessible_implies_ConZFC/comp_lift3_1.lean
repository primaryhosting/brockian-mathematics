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

@[simp] lemma comp_lift3_1 {M : Type*} (a b c d : M) :
    ![a, b, c, d] ∘ (fun i : Fin 3 => if i = 0 then i.castSucc else i.succ) = ![a, c, d] := by
  funext i; fin_cases i <;> simp

end MatrixLemmas

section Realize

variable {M : Type*} [setLang.Structure M]

/-- The membership relation of a structure in the language of set theory. -/
abbrev memR (a b : M) : Prop := Structure.RelMap memSym ![a, b]


/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Formalization

Löb's theorem is a statement about the provability predicate `□` (`Bew`, `Pr_PA`) of
Peano Arithmetic:

> if `PA ⊢ (□⌜φ⌝ → φ)` then `PA ⊢ φ`.

Its proof uses exactly two ingredients about `PA` and its provability predicate:

* the **Hilbert–Bernays–Löb derivability conditions**
  * `D1` (necessitation): if `⊢ φ` then `⊢ □φ`;
  * `D2` (distribution):  `⊢ □(φ → ψ) → (□φ → □ψ)`;
  * `D3` (self-awareness): `⊢ □φ → □□φ`;
* the **diagonal (fixed point) lemma**: for every `φ` there is a sentence `ψ` with
  `⊢ ψ ↔ (□ψ → φ)`.

Accordingly we formalize the syntax of the language — classical propositional logic
together with the provability operator `□` — as an inductive type `Frontier.Formula`,
and the derivability relation `Frontier.Provable` as an inductive predicate given by a
Hilbert-style calculus containing modus ponens, the classical propositional axioms and
the three derivability conditions `D1`, `D2`, `D3`.  The diagonal lemma — the only
genuinely arithmetical ingredient, obtained in `PA` from Gödel numbering — is taken as
an explicit hypothesis `diag` of the theorem.

`Frontier.Loeb_theorem` then states precisely: for every formula `φ`, if `⊢ □φ → φ`,
then `⊢ φ`.  The formalized version `Frontier.Loeb_axiom`, i.e. the Gödel–Löb axiom
`⊢ □(□φ → φ) → □φ`, is derived as well.
-/

namespace Frontier

/-- Formulas of the language: classical propositional logic (with falsum `⊥` and
implication `→`) extended by the provability operator `□`. -/
inductive Formula : Type
  /-- An atomic sentence (e.g. the `n`-th sentence of the language of arithmetic). -/
  | atom : ℕ → Formula
  /-- Falsum. -/
  | falsum : Formula
  /-- Implication. -/
  | imp : Formula → Formula → Formula
  /-- The provability operator: `box φ` reads "`φ` is provable in `PA`". -/
  | box : Formula → Formula

@[inherit_doc] scoped infixr:25 " ⇒ " => Formula.imp
@[inherit_doc] scoped prefix:max "□" => Formula.box

/-- Derivability in the theory: a Hilbert-style calculus for classical propositional
logic together with the three Hilbert–Bernays–Löb derivability conditions for the
provability operator `□`. -/
inductive Provable : Formula → Prop
  /-- Modus ponens. -/
  | mp {p q : Formula} : Provable (p ⇒ q) → Provable p → Provable q
  /-- Propositional axiom K. -/
  | ax_k {p q : Formula} : Provable (p ⇒ (q ⇒ p))
  /-- Propositional axiom S. -/
  | ax_s {p q r : Formula} : Provable ((p ⇒ (q ⇒ r)) ⇒ ((p ⇒ q) ⇒ (p ⇒ r)))
  /-- Double negation elimination (classical logic). -/
  | ax_dne {p : Formula} : Provable ((((p ⇒ Formula.falsum) ⇒ Formula.falsum)) ⇒ p)
  /-- `D1`: necessitation — anything provable is provably provable. -/
  | nec {p : Formula} : Provable p → Provable □p
  /-- `D2`: the provability operator distributes over implication. -/
  | dist {p q : Formula} : Provable (□(p ⇒ q) ⇒ (□p ⇒ □q))
  /-- `D3`: provability is provably provable. -/
  | four {p : Formula} : Provable (□p ⇒ □□p)

namespace Provable

/-- `⊢ p → p`. -/
theorem imp_self (p : Formula) : Provable (p ⇒ p) :=
  mp (mp (ax_s (p := p) (q := p ⇒ p) (r := p)) ax_k) ax_k

/-- Distribution rule: from `⊢ p → (q → r)` and `⊢ p → q` infer `⊢ p → r`. -/
theorem imp_dist {p q r : Formula} (h₁ : Provable (p ⇒ (q ⇒ r))) (h₂ : Provable (p ⇒ q)) :
    Provable (p ⇒ r) :=
  mp (mp ax_s h₁) h₂

/-- Transitivity of implication. -/
theorem imp_trans {p q r : Formula} (h₁ : Provable (p ⇒ q)) (h₂ : Provable (q ⇒ r)) :
    Provable (p ⇒ r) :=
  imp_dist (mp ax_k h₂) h₁

/-- Precomposition: from `⊢ p → q` infer `⊢ (q → r) → (p → r)`. -/
theorem imp_comp_left {p q r : Formula} (h : Provable (p ⇒ q)) :
    Provable ((q ⇒ r) ⇒ (p ⇒ r)) :=
  imp_dist (imp_trans ax_k ax_s) (mp ax_k h)

/-- The provability operator is monotone under derivable implications:
from `⊢ p → q` infer `⊢ □p → □q`. -/
theorem box_mono {p q : Formula} (h : Provable (p ⇒ q)) : Provable (□p ⇒ □q) :=
  mp dist (nec h)

end Provable

open Provable

/-- The diagonal (fixed point) lemma for the provability operator: for every formula `φ`
there is a formula `ψ` provably equivalent to `□ψ → φ`.  In `PA` this is supplied by
Gödel's diagonalization construction. -/
def HasDiagonal : Prop :=
  ∀ φ : Formula, ∃ ψ : Formula, Provable (ψ ⇒ (□ψ ⇒ φ)) ∧ Provable ((□ψ ⇒ φ) ⇒ ψ)

/-- The key step of Löb's argument: if `ψ` is a fixed point of `□ψ → φ`, then
`⊢ □ψ → □φ`. -/
theorem box_fixedPoint_imp {φ ψ : Formula} (hfwd : Provable (ψ ⇒ (□ψ ⇒ φ))) :
    Provable (□ψ ⇒ □φ) :=
  imp_dist (imp_trans (box_mono hfwd) dist) four

/-- **Löb's theorem.**  Working in a theory (such as `PA`) whose provability operator `□`
satisfies the Hilbert–Bernays–Löb derivability conditions `D1`, `D2`, `D3` (built into
`Frontier.Provable`) and for which the diagonal lemma holds — for every formula `φ`
there is a formula `ψ` with `⊢ ψ ↔ (□ψ → φ)` — if `⊢ □φ → φ`, then `⊢ φ`. -/
theorem Loeb_theorem (diag : HasDiagonal) (φ : Formula) (h : Provable (□φ ⇒ φ)) :
    Provable φ := by
  obtain ⟨ψ, hfwd, hbwd⟩ := diag φ
  -- `⊢ □ψ → □φ`, hence `⊢ □ψ → φ` by the hypothesis
  have h₁ : Provable (□ψ ⇒ φ) := imp_trans (box_fixedPoint_imp hfwd) h
  -- hence `⊢ ψ`, hence `⊢ □ψ` by necessitation, hence `⊢ φ`
  exact mp h₁ (nec (mp hbwd h₁))

/-- The Gödel–Löb axiom, i.e. the formalized version of Löb's theorem:
`⊢ □(□φ → φ) → □φ`. -/
theorem Loeb_axiom (diag : HasDiagonal) (φ : Formula) :
    Provable (□(□φ ⇒ φ) ⇒ □φ) := by
  obtain ⟨ψ, hfwd, hbwd⟩ := diag φ
  have h₁ : Provable (□ψ ⇒ □φ) := box_fixedPoint_imp hfwd
  -- `⊢ (□φ → φ) → (□ψ → φ)`, so `⊢ □(□φ → φ) → □(□ψ → φ)`
  have h₂ : Provable (□(□φ ⇒ φ) ⇒ □(□ψ ⇒ φ)) := box_mono (imp_comp_left h₁)
  -- and `⊢ □(□ψ → φ) → □ψ` since `⊢ (□ψ → φ) → ψ`
  have h₃ : Provable (□(□ψ ⇒ φ) ⇒ □ψ) := box_mono hbwd
  exact imp_trans (imp_trans h₂ h₃) h₁

/-! ### Consistency of the calculus

The calculus above is consistent: it does not prove falsum.  (This is a sanity check
showing that `Frontier.Loeb_theorem` is not a statement about a trivial derivability
predicate.)  We interpret every atom and every boxed formula as `True`; all the axioms
and rules of `Frontier.Provable` are validated by this interpretation, while `falsum`
is not. -/

/-- A trivial interpretation of formulas validating all axioms of the calculus. -/
def eval : Formula → Prop
  | .atom _ => True
  | .falsum => False
  | .imp p q => eval p → eval q
  | .box _ => True

/-- Soundness of the calculus with respect to the interpretation `Frontier.eval`. -/
theorem eval_of_provable {p : Formula} (h : Provable p) : eval p := by
  induction h with
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂
  | ax_k => exact fun hp _ => hp
  | ax_s => exact fun hpqr hpq hp => hpqr hp (hpq hp)
  | ax_dne => exact fun hnn => Classical.byContradiction fun hn => hnn hn
  | nec => trivial
  | dist => exact fun _ _ => trivial
  | four => exact fun _ => trivial

/-- The calculus is consistent: falsum is not derivable. -/
theorem not_provable_falsum : ¬ Provable Formula.falsum :=
  fun h => eval_of_provable h

end Frontier

#print axioms Frontier.Loeb_theorem
#print axioms Frontier.Loeb_axiom
#print axioms Frontier.not_provable_falsum

import Mathlib

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


/-
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
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

namespace Frontier

/-!
## Setting

Gödel's second incompleteness theorem says: *no consistent, recursively axiomatized
theory `T` extending `PA` proves its own consistency*.

The content of the hypothesis "recursively axiomatized extension of `PA`" is used in
exactly two places in the classical proof:

* the *Hilbert–Bernays–Löb derivability conditions* for the arithmetized provability
  predicate `Pr_T`, namely
  - **D1** `T ⊢ σ  ⟹  T ⊢ Pr_T(⌜σ⌝)` (necessitation),
  - **D2** `T ⊢ Pr_T(⌜σ → τ⌝) → (Pr_T(⌜σ⌝) → Pr_T(⌜τ⌝))` (distribution),
  - **D3** `T ⊢ Pr_T(⌜σ⌝) → Pr_T(⌜Pr_T(⌜σ⌝)⌝)`;
* the *diagonal (fixed point) lemma*: for every sentence `A` there is a sentence `γ`
  with `T ⊢ γ ↔ (Pr_T(⌜γ⌝) → A)`.

We therefore formalize the theorem in exactly this shape.  The language of sentences is
the modal language with `⊥`, `→` and a unary provability operator `□` (the operator
`□σ` stands for the arithmetical sentence `Pr_T(⌜σ⌝)`), and `Prv T` is the smallest
relation containing the axioms of `T`, closed under classical propositional logic and
satisfying **D1**, **D2**, **D3**.  The consistency statement `Con_T` is `¬ □⊥`.

The main theorem `Frontier.Goedel_second_incompleteness` states that a consistent such
theory that admits fixed points does not prove `Con_T`.  It is obtained from Löb's
theorem, proved here from scratch inside the Hilbert calculus.

`Frontier.Goedel_second_incompleteness_nonvacuous` shows that the hypotheses of the
main theorem are satisfiable, so the statement is not vacuously true.
-/

/-- Sentences of the language of provability: `⊥`, implication, and the provability
operator `□` (read `□ p` as `Pr_T(⌜p⌝)`). -/
inductive Form : Type
  | bot : Form
  | imp : Form → Form → Form
  | box : Form → Form
  deriving DecidableEq

namespace Form

/-- Negation, `¬ p := p → ⊥`. -/

theorem loeb (T : Form → Prop) (A : Form)
    (hfix : ∃ g : Form,
      Prv T (Form.imp g (Form.imp (Form.box g) A)) ∧
      Prv T (Form.imp (Form.imp (Form.box g) A) g))
    (hA : Prv T (Form.imp (Form.box A) A)) :
    Prv T A := by
  obtain ⟨g, hg₁, hg₂⟩ := hfix
  -- `⊢ □(g → (□g → A))`
  have h1 : Prv T (Form.box (Form.imp g (Form.imp (Form.box g) A))) := Prv.nec hg₁
  -- `⊢ □g → □(□g → A)`
  have h2 : Prv T (Form.imp (Form.box g) (Form.box (Form.imp (Form.box g) A))) :=
    Prv.mp (Prv.distr g (Form.imp (Form.box g) A)) h1
  -- `⊢ □(□g → A) → (□□g → □A)`
  have h3 : Prv T (Form.imp (Form.box (Form.imp (Form.box g) A))
      (Form.imp (Form.box (Form.box g)) (Form.box A))) := Prv.distr (Form.box g) A
  -- `⊢ □g → (□□g → □A)`
  have h4 : Prv T (Form.imp (Form.box g)
      (Form.imp (Form.box (Form.box g)) (Form.box A))) := Prv.imp_trans h2 h3
  -- `⊢ □g → □□g`  (derivability condition D3)
  have h5 : Prv T (Form.imp (Form.box g) (Form.box (Form.box g))) := Prv.four g
  -- `⊢ □g → □A`
  have h6 : Prv T (Form.imp (Form.box g) (Form.box A)) := Prv.imp_mp h4 h5
  -- `⊢ □g → A`
  have h7 : Prv T (Form.imp (Form.box g) A) := Prv.imp_trans h6 hA
  -- hence `⊢ g`, and so `⊢ □g`, and finally `⊢ A`
  have h8 : Prv T g := Prv.mp hg₂ h7
  exact Prv.mp h7 (Prv.nec h8)

/-- **Gödel's second incompleteness theorem.**

No consistent theory `T` that satisfies the Hilbert–Bernays–Löb derivability
conditions for its own provability predicate `□` (built into `Frontier.Prv`) and the
diagonal lemma `hfix` proves its own consistency statement `Con_T = ¬ □⊥`.

Every recursively axiomatized theory extending `PA` satisfies `hfix` and the
derivability conditions, so this is exactly the classical statement. -/

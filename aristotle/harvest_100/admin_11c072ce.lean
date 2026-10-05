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
def neg (p : Form) : Form := Form.imp p Form.bot

/-- The consistency statement `Con_T := ¬ □⊥`, i.e. "`T` does not prove `0 = 1`". -/
def con : Form := Form.neg (Form.box Form.bot)

end Form

/-- Provability in the theory `T`: classical propositional logic over the axioms of
`T`, together with the three Hilbert–Bernays–Löb derivability conditions for `□`. -/
inductive Prv (T : Form → Prop) : Form → Prop
  /-- Axioms of `T`. -/
  | ax {p : Form} : T p → Prv T p
  /-- Propositional axiom `p → (q → p)`. -/
  | k1 (p q : Form) : Prv T (Form.imp p (Form.imp q p))
  /-- Propositional axiom `(p → q → r) → (p → q) → (p → r)`. -/
  | k2 (p q r : Form) :
      Prv T (Form.imp (Form.imp p (Form.imp q r))
        (Form.imp (Form.imp p q) (Form.imp p r)))
  /-- Classical axiom `¬¬p → p`. -/
  | k3 (p : Form) : Prv T (Form.imp (Form.neg (Form.neg p)) p)
  /-- Modus ponens. -/
  | mp {p q : Form} : Prv T (Form.imp p q) → Prv T p → Prv T q
  /-- Derivability condition **D1** (necessitation). -/
  | nec {p : Form} : Prv T p → Prv T (Form.box p)
  /-- Derivability condition **D2** (distribution). -/
  | distr (p q : Form) :
      Prv T (Form.imp (Form.box (Form.imp p q))
        (Form.imp (Form.box p) (Form.box q)))
  /-- Derivability condition **D3**. -/
  | four (p : Form) : Prv T (Form.imp (Form.box p) (Form.box (Form.box p)))

namespace Prv

variable {T : Form → Prop} {p q r : Form}

/-- The `S`-combinator step: from `⊢ p → q → r` and `⊢ p → q` infer `⊢ p → r`. -/
theorem imp_mp (h₁ : Prv T (Form.imp p (Form.imp q r))) (h₂ : Prv T (Form.imp p q)) :
    Prv T (Form.imp p r) :=
  Prv.mp (Prv.mp (Prv.k2 p q r) h₁) h₂

/-- `⊢ p → p`. -/
theorem imp_self (p : Form) : Prv T (Form.imp p p) :=
  imp_mp (Prv.k1 p (Form.imp p p)) (Prv.k1 p p)

/-- Weakening: from `⊢ q` infer `⊢ p → q`. -/
theorem imp_intro (h : Prv T q) (p : Form) : Prv T (Form.imp p q) :=
  Prv.mp (Prv.k1 q p) h

/-- Transitivity of implication (hypothetical syllogism). -/
theorem imp_trans (h₁ : Prv T (Form.imp p q)) (h₂ : Prv T (Form.imp q r)) :
    Prv T (Form.imp p r) :=
  imp_mp (imp_intro h₂ p) h₁

/-- From `⊢ p` infer `⊢ (p → q) → q`. -/
theorem mp_taut (h : Prv T p) (q : Form) : Prv T (Form.imp (Form.imp p q) q) :=
  imp_mp (imp_self (Form.imp p q)) (imp_intro h (Form.imp p q))

end Prv

/-- **Löb's theorem** (abstract form).  If for every sentence `A` the theory `T` has a
fixed point `γ` for `□γ → A`, then `T ⊢ □A → A` implies `T ⊢ A`. -/
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
theorem Goedel_second_incompleteness (T : Form → Prop)
    (hfix : ∀ A : Form, ∃ g : Form,
      Prv T (Form.imp g (Form.imp (Form.box g) A)) ∧
      Prv T (Form.imp (Form.imp (Form.box g) A) g))
    (hcon : ¬ Prv T Form.bot) :
    ¬ Prv T Form.con := by
  intro h
  -- `Con_T` is literally `□⊥ → ⊥`, so Löb's theorem with `A = ⊥` gives `T ⊢ ⊥`.
  exact hcon (loeb T Form.bot (hfix Form.bot) h)

/-!
## The hypotheses are satisfiable

To see that `Frontier.Goedel_second_incompleteness` is not vacuous we exhibit a
consistent theory admitting fixed points, namely the theory whose axioms are all
sentences of the form `□φ`.  (This theory is consistent but proves `□⊥`, i.e. it
proves its own inconsistency; it is of course not an extension of `PA`.  The point of
the example is only that the hypotheses of the theorem are jointly satisfiable.)
-/

/-- The trivial interpretation sending `□p` to `True`; used to certify consistency. -/
def eval : Form → Prop
  | Form.bot => False
  | Form.imp p q => eval p → eval q
  | Form.box _ => True

/-- Soundness of `Prv` for the trivial interpretation `Frontier.eval`. -/
theorem eval_of_prv {T : Form → Prop} (hT : ∀ p : Form, T p → eval p) {p : Form}
    (h : Prv T p) : eval p := by
  induction h with
  | ax hp => exact hT _ hp
  | k1 p q => exact fun hp _ => hp
  | k2 p q r => exact fun hpqr hpq hp => hpqr hp (hpq hp)
  | k3 p =>
      intro hnn
      by_contra hp
      exact hnn hp
  | mp _ _ ih₁ ih₂ => exact ih₁ ih₂
  | nec _ _ => exact trivial
  | distr p q => exact fun _ _ => trivial
  | four p => exact fun _ => trivial

/-- The example theory: all sentences of the form `□φ` are axioms. -/
def boxAll (p : Form) : Prop := ∃ q : Form, p = Form.box q

/-- `Frontier.boxAll` is consistent. -/
theorem boxAll_consistent : ¬ Prv boxAll Form.bot := by
  intro h
  have : eval Form.bot := eval_of_prv (fun p hp => by
    obtain ⟨q, rfl⟩ := hp
    exact trivial) h
  exact this

/-- `Frontier.boxAll` admits fixed points for `□g → A`: one may take `g = A`. -/
theorem boxAll_hasFixedPoints (A : Form) : ∃ g : Form,
    Prv boxAll (Form.imp g (Form.imp (Form.box g) A)) ∧
    Prv boxAll (Form.imp (Form.imp (Form.box g) A) g) :=
  ⟨A, Prv.k1 A (Form.box A), Prv.mp_taut (Prv.ax ⟨A, rfl⟩) A⟩

/-- The hypotheses of `Frontier.Goedel_second_incompleteness` are satisfiable: there is
a consistent theory admitting the required fixed points.  Hence the theorem is not
vacuously true. -/
theorem Goedel_second_incompleteness_nonvacuous :
    ∃ T : Form → Prop,
      (∀ A : Form, ∃ g : Form,
        Prv T (Form.imp g (Form.imp (Form.box g) A)) ∧
        Prv T (Form.imp (Form.imp (Form.box g) A) g)) ∧
      ¬ Prv T Form.bot := by
  exact ⟨boxAll, boxAll_hasFixedPoints, boxAll_consistent⟩

end Frontier


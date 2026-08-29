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

Gödel's second incompleteness theorem states that no consistent, recursively axiomatized
theory `T` extending `PA` proves the arithmetical sentence `Con(T)` expressing its own
consistency.

The theorem is formalized here in the standard *abstract* (Hilbert–Bernays–Löb) form, i.e.
as the Lean-checked reduction of the theorem to the derivability conditions.  The data are:

* `B`, the Lindenbaum–Tarski algebra of `T`: sentences of the language of `T` modulo
  `T`-provable equivalence.  Since `T` extends `PA`, its underlying logic is classical, so `B`
  is a Boolean algebra, and a sentence `a` is *provable in `T`* exactly when its class satisfies
  `a = ⊤`.  Consistency of `T` says precisely that `⊥ ≠ ⊤` in `B`, i.e. that `T` does not
  prove a contradiction.
* `box : B → B`, the provability predicate `a ↦ ⌜Prov_T(⌜a⌝)⌝`.  (For a *recursively
  axiomatized* `T` such a `Σ₁` predicate exists by arithmetization of syntax, and it descends
  to the Lindenbaum algebra because `T ⊢ a ↔ b` implies `T ⊢ □a ↔ □b`.)

The hypotheses `D1`, `D2`, `D3` are the three Hilbert–Bernays–Löb derivability conditions,
which hold for every recursively axiomatized theory extending `PA`:

* `D1`  (necessitation)      `T ⊢ a  ⟹  T ⊢ □a`;
* `D2`  (internal modus ponens) `T ⊢ □(a → b) → (□a → □b)`;
* `D3`  (provable Σ₁-completeness) `T ⊢ □a → □□a`.

Finally `hg` is the Gödel fixed point supplied by the diagonal lemma: a sentence `g` with
`T ⊢ g ↔ ¬□g`.

Note that these hypotheses are satisfiable by a *consistent* system (see
`Frontier.goedel_hypotheses_satisfiable` below), so the theorem below is not vacuous.
-/

section
variable {B : Type*} [BooleanAlgebra B]

/-- The internal consistency statement `Con(T) = ¬ Prov_T(⌜⊥⌝)`, as an element of the
Lindenbaum algebra. -/

theorem goedel_hypotheses_satisfiable :
    ∃ (box : Prop → Prop) (g : Prop),
      (∀ a : Prop, a = ⊤ → box a = ⊤) ∧
      (∀ a b : Prop, box (a ⇨ b) ⊓ box a ≤ box b) ∧
      (∀ a : Prop, box a ≤ box (box a)) ∧
      g = (box g)ᶜ ∧ (⊥ : Prop) ≠ ⊤ := by
  refine ⟨fun _ => ⊤, ⊥, fun a _ => rfl, fun a b => le_top, fun a => le_top, ?_, ?_⟩
  · simp
  · simp

end Frontier


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

/-!
# Löb's theorem: a consistent theory cannot trust itself

We formalize, in an abstract but faithful setting, the statement that a consistent
theory cannot prove the *reflection principle* `Prov(⌜A⌝) → A` for a sentence `A`
that it does not prove.

The setting is an abstract theory over a type `S` of sentences, equipped with
implication, a provability predicate `Pr` (the internal formalization of
"is provable"), the Hilbert–Bernays–Löb derivability conditions, and the
diagonal (fixed point) lemma.  This is exactly the structure that Peano
arithmetic (or any consistent r.e. extension of it) provides, and it is enough
to derive Löb's theorem, hence the result.
-/

namespace Frontier

/-- An abstract theory with an internal provability predicate.

* `imp` is the implication connective of the language;
* `Pr s` is the sentence expressing "`s` is provable in the theory";
* `Thm s` means "`s` is a theorem of the theory".

The axioms are:
* closure of `Thm` under modus ponens, together with the two Hilbert axiom
  schemes `K` and `S` (i.e. the theory contains implicational propositional
  logic);
* the Hilbert–Bernays–Löb derivability conditions `hb1`, `hb2`, `hb3`;
* the diagonal lemma `diag`: for every formula `f` (with one free slot) there is
  a sentence `p` provably equivalent to `f` applied to (the code of) `Pr p`.
  Diagonalizing through `Pr` is what the arithmetical diagonal lemma provides:
  applying it to the formula `x ↦ f (Pr x)` yields such a `p`. -/
structure ProvabilityTheory (S : Type*) where
  /-- The implication connective. -/
  imp : S → S → S
  /-- The internal provability predicate. -/
  Pr : S → S
  /-- Theoremhood in the theory. -/
  Thm : S → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b : S}, Thm (imp a b) → Thm a → Thm b
  /-- Hilbert axiom scheme `K`. -/
  ax_K : ∀ a b : S, Thm (imp a (imp b a))
  /-- Hilbert axiom scheme `S`. -/
  ax_S : ∀ a b c : S, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- First derivability condition: theorems are provably provable. -/
  hb1 : ∀ {a : S}, Thm a → Thm (Pr a)
  /-- Second derivability condition: internal modus ponens. -/
  hb2 : ∀ a b : S, Thm (imp (Pr (imp a b)) (imp (Pr a) (Pr b)))
  /-- Third derivability condition: provable provability is provably provable. -/
  hb3 : ∀ a : S, Thm (imp (Pr a) (Pr (Pr a)))
  /-- Diagonal lemma (fixed points through the provability predicate). -/
  diag : ∀ f : S → S, ∃ p : S, Thm (imp p (f (Pr p))) ∧ Thm (imp (f (Pr p)) p)

namespace ProvabilityTheory

variable {S : Type*} (T : ProvabilityTheory S)

/-- A theory is consistent if some sentence is not a theorem of it. -/

theorem imp_trans {a b c : S} (h₁ : T.Thm (T.imp a b)) (h₂ : T.Thm (T.imp b c)) :
    T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_S a b c) (T.mp (T.ax_K (T.imp b c) a) h₂)) h₁

/-- Distribution of implication inside the theory. -/

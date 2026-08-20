/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of the pinned revision) contains no development of provability logic,
Gödel's incompleteness theorems, or Löb's theorem: a search for `Loeb`, `Provable`,
`reflection` turns up nothing applicable, so nothing in the library closes or nearly
closes the goal.  We therefore build the standard abstract setting (a theory together
with a provability predicate satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma) from scratch.
-/

namespace Frontier

universe u

/-- An abstract *provability frame*: a type `S` of sentences equipped with

* an implication connective `imp`,
* a falsity constant `bot`,
* an internal provability operator `box` (`box a` is the sentence "`a` is provable"),
* the external predicate `Pr a`, meaning "the theory proves `a`",

subject to the usual closure conditions of a theory containing enough arithmetic:
modus ponens, the propositional laws used below, *ex falso*, the three
Hilbert–Bernays–Löb derivability conditions, and the diagonal (fixed point) lemma. -/
structure ProvabilityFrame (S : Type u) where
  /-- The implication connective. -/
  imp : S → S → S
  /-- The falsity constant. -/
  bot : S
  /-- The internal provability operator: `box a` says "`a` is provable". -/
  box : S → S
  /-- `Pr a` means: the theory proves the sentence `a`. -/
  Pr : S → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b}, Pr (imp a b) → Pr a → Pr b
  /-- Derivability condition D1 (necessitation): what is provable is provably provable. -/
  nec : ∀ {a}, Pr a → Pr (box a)
  /-- Provable implications compose. -/
  imp_trans : ∀ {a b c}, Pr (imp a b) → Pr (imp b c) → Pr (imp a c)
  /-- The propositional law `(a → b → c) → (a → b) → (a → c)`, in rule form. -/
  distrib : ∀ {a b c}, Pr (imp a (imp b c)) → Pr (imp a b) → Pr (imp a c)
  /-- Derivability condition D2: the provability operator distributes over implication. -/
  boxK : ∀ a b, Pr (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: provability is provably transitive. -/
  box4 : ∀ a, Pr (imp (box a) (box (box a)))
  /-- *Ex falso quodlibet*. -/
  efq : ∀ a, Pr (imp bot a)
  /-- The diagonal lemma: every `a` has a fixed point `l` provably equivalent to
  the sentence "if `l` is provable then `a`". -/
  diag : ∀ a, ∃ l, Pr (imp l (imp (box l) a)) ∧ Pr (imp (imp (box l) a) l)

namespace ProvabilityFrame

variable {S : Type u} (F : ProvabilityFrame S)

/-- The theory is *consistent* if it does not prove falsity. -/

theorem goedel_second {S : Type u} (F : ProvabilityFrame S) (hcon : F.Consistent) :
    ¬ F.Pr (F.reflection F.bot) :=
  (loeb_no_self_trust F hcon).2

/-- The axioms of `ProvabilityFrame` are satisfiable together with the existence of an
unprovable sentence, so `loeb_no_self_trust` is not vacuous: take sentences to be
Lean propositions, `Pr` to be truth, and `box` the constant `True`. -/

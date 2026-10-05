/-!
# Loeb No Self Trust
Category: Frontier Mind
Target: Frontier.loeb_no_self_trust
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- An abstract formal theory equipped with a provability predicate satisfying the
Hilbert–Bernays–Löb derivability conditions, together with the diagonal (fixed point)
lemma.  This is exactly the amount of structure that arithmetized metamathematics
(e.g. Peano Arithmetic with its standard proof predicate) provides.

* `Sentence` : the type of sentences of the theory;
* `imp a b`  : the (object level) implication `a → b`;
* `bot`      : the (object level) falsum;
* `Thm a`    : the (meta level) assertion that the theory proves `a`;
* `Pr a`     : the sentence "`a` is provable in the theory" (the arithmetized
  provability statement, i.e. `Prov(⌈a⌉)`).
-/
structure Theory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Object level implication. -/
  imp : Sentence → Sentence → Sentence
  /-- Object level falsum. -/
  bot : Sentence
  /-- `Thm a` means: the theory proves the sentence `a`. -/
  Thm : Sentence → Prop
  /-- `Pr a` is the sentence expressing "`a` is provable in the theory". -/
  Pr : Sentence → Sentence
  /-- Propositional axiom scheme K. -/
  ax_k : ∀ a b : Sentence, Thm (imp a (imp b a))
  /-- Propositional axiom scheme S. -/
  ax_s : ∀ a b c : Sentence,
    Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Ex falso quodlibet. -/
  ax_bot : ∀ a : Sentence, Thm (imp bot a)
  /-- Closure of the theory under modus ponens. -/
  mp : ∀ {a b : Sentence}, Thm (imp a b) → Thm a → Thm b
  /-- First derivability condition: the theory proves its own proofs. -/
  D1 : ∀ {a : Sentence}, Thm a → Thm (Pr a)
  /-- Second derivability condition: internal closure of provability under modus ponens. -/
  D2 : ∀ a b : Sentence, Thm (imp (Pr (imp a b)) (imp (Pr a) (Pr b)))
  /-- Third derivability condition: provable sentences are provably provable. -/
  D3 : ∀ a : Sentence, Thm (imp (Pr a) (Pr (Pr a)))
  /-- Diagonal lemma: every sentence `a` has a fixed point `p` provably equivalent to
  `Pr p → a`. -/
  diag : ∀ a : Sentence, ∃ p : Sentence,
    Thm (imp p (imp (Pr p) a)) ∧ Thm (imp (imp (Pr p) a) p)

namespace Theory

variable (T : Theory)

/-- A theory is consistent when it does not prove falsum. -/

theorem imp_distrib {a b c : T.Sentence} (h1 : T.Thm (T.imp a (T.imp b c)))
    (h2 : T.Thm (T.imp a b)) : T.Thm (T.imp a c) :=
  T.mp (T.mp (T.ax_s a b c) h1) h2

/-- Transitivity (syllogism) of object level implication. -/

/-
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- An abstract axiomatization of a formal theory (think: Peano Arithmetic) together with
its provability predicate `□`.

* `Sentence` is the type of sentences of the theory;
* `imp` is the implication connective;
* `box φ` is the (internalized) sentence "`φ` is provable in the theory";
* `Thm φ` says that `φ` is a theorem of the theory (`PA ⊢ φ`).

The axioms are the standard ones needed for Löb's theorem:

* closure of `Thm` under modus ponens, and the implicational axioms `K` and `S`
  (so the theory proves all tautologies of implicational propositional logic);
* the Hilbert–Bernays–Löb derivability conditions:
  `D1` (necessitation), `D2` (distribution of `□` over `→`), `D3` (`□φ → □□φ`);
* the diagonal (fixed point) lemma, which in arithmetic is provided by Gödel's
  self-reference construction. -/
structure ProvabilityTheory where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability operator: `box φ` is the sentence "`φ` is provable". -/
  box : Sentence → Sentence
  /-- `Thm φ` means the theory proves `φ`. -/
  Thm : Sentence → Prop
  /-- The theory is closed under modus ponens. -/
  mp : ∀ {a b}, Thm (imp a b) → Thm a → Thm b
  /-- Axiom scheme `K` of implicational logic. -/
  ax_K : ∀ a b, Thm (imp a (imp b a))
  /-- Axiom scheme `S` of implicational logic. -/
  ax_S : ∀ a b c, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- First derivability condition: necessitation. -/
  D1 : ∀ {a}, Thm a → Thm (box a)
  /-- Second derivability condition: `□(a → b) → (□a → □b)`. -/
  D2 : ∀ a b, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: `□a → □□a`. -/
  D3 : ∀ a, Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma: for every `a` there is a sentence `d` which the theory proves
  equivalent to `□d → a`. -/
  diagonal : ∀ a, ∃ d, Thm (imp d (imp (box d) a)) ∧ Thm (imp (imp (box d) a) d)

namespace ProvabilityTheory

variable (T : ProvabilityTheory)

/-- Every sentence implies itself. -/

theorem imp_of (a : T.Sentence) {b : T.Sentence} (hb : T.Thm b) : T.Thm (T.imp a b) :=
  T.mp (T.ax_K b a) hb

/-- Hypothetical syllogism: chaining of provable implications. -/

import Mathlib
/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Löb's theorem: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`.

The statement is formalized for an arbitrary formal system satisfying the
Hilbert–Bernays–Löb derivability conditions together with the diagonal
(fixed-point) lemma, all of which hold for Peano Arithmetic with `□` the
standard provability predicate.  This is packaged in the structure
`Frontier.ProvabilitySystem` below, whose fields are:

* a type `Sent` of sentences, with an implication connective `imp` and a
  provability-predicate former `box` (`box φ` is the arithmetized sentence
  "`φ` is provable");
* a predicate `Prv` on sentences (`Prv φ` means "PA ⊢ φ");
* the propositional axiom schemes `K` and `S` for implication, plus modus
  ponens — i.e. `Prv` is closed under implicational propositional logic;
* the three derivability conditions: necessitation (D1), distribution (D2),
  and the formalized D1 (D3);
* the diagonal lemma, in the form needed for Löb's theorem: for every `φ`
  there is a sentence `ψ` for which PA proves `ψ ↔ (□ψ → φ)`.
-/

namespace Frontier

/-- An abstract formal system (think: Peano Arithmetic) equipped with a
provability predicate `box` satisfying the Hilbert–Bernays–Löb derivability
conditions and the diagonal lemma. -/
structure ProvabilitySystem where
  /-- The type of sentences of the system. -/
  Sent : Type
  /-- Implication connective. -/
  imp : Sent → Sent → Sent
  /-- Arithmetized provability: `box φ` is the sentence "`φ` is provable". -/
  box : Sent → Sent
  /-- `Prv φ` means "the system proves `φ`". -/
  Prv : Sent → Prop
  /-- Axiom scheme K of propositional logic. -/
  axK : ∀ a b, Prv (imp a (imp b a))
  /-- Axiom scheme S of propositional logic. -/
  axS : ∀ a b c, Prv (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens: provability is closed under detachment. -/
  mp : ∀ {a b}, Prv (imp a b) → Prv a → Prv b
  /-- Derivability condition D1 (necessitation): if `⊢ φ` then `⊢ □φ`. -/
  D1 : ∀ {a}, Prv a → Prv (box a)
  /-- Derivability condition D2 (distribution): `⊢ □(φ → ψ) → (□φ → □ψ)`. -/
  D2 : ∀ a b, Prv (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Derivability condition D3: `⊢ □φ → □□φ`. -/
  D3 : ∀ a, Prv (imp (box a) (box (box a)))
  /-- Diagonal lemma: for each `φ` there is `ψ` with `⊢ ψ ↔ (□ψ → φ)`. -/
  diag : ∀ a, ∃ p, Prv (imp p (imp (box p) a)) ∧ Prv (imp (imp (box p) a) p)

namespace ProvabilitySystem

variable (S : ProvabilitySystem)

/-- `⊢ φ → φ`. -/

theorem imp_intro {b : S.Sent} (a : S.Sent) (h : S.Prv b) : S.Prv (S.imp a b) :=
  S.mp (S.axK b a) h

/-- Syllogism: from `⊢ a → b` and `⊢ b → c` infer `⊢ a → c`. -/

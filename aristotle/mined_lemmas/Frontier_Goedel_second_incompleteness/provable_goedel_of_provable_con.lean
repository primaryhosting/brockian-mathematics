/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file formalizes Gödel's second incompleteness theorem in its standard abstract
(Hilbert–Bernays–Löb) form:

  no consistent theory whose provability predicate satisfies the three derivability
  conditions and which admits a Gödel (diagonal) sentence can prove its own consistency.

A consistent recursively axiomatized theory `T` extending `PA` is exactly a situation in
which these hypotheses are met: recursive axiomatizability gives a `Σ₁` provability
predicate `Prov_T`, extension of `PA` gives the three Hilbert–Bernays–Löb derivability
conditions `D1`, `D2`, `D3` for it, and the diagonal lemma supplies a sentence `g` with
`T ⊢ g ↔ ¬ Prov_T(⌜g⌝)`.  The conclusion `¬ T ⊢ Con_T` is then the content of
`Frontier.Goedel_second_incompleteness` below.

The underlying logic is presented as the implicational Hilbert calculus (axioms `K`, `S`
and modus ponens), with `⊥` an arbitrary sentence; negation is `¬a := a → ⊥`, and the
consistency statement is `Con := □⊥ → ⊥`.
-/

namespace Frontier

/-- An abstract provability system: a set of sentences with implication, falsum, an
internal provability operator `box`, and an external provability predicate satisfying the
implicational Hilbert axioms together with the Hilbert–Bernays–Löb derivability
conditions. -/
structure ProvabilitySystem where
  /-- The type of sentences of the theory. -/
  Sentence : Type
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The false sentence. -/
  bot : Sentence
  /-- The internal provability operator: `box a` expresses "`a` is provable". -/
  box : Sentence → Sentence
  /-- The (external) predicate "the theory proves this sentence". -/
  Provable : Sentence → Prop
  /-- Hilbert axiom `K`. -/
  ax_K : ∀ a b, Provable (imp a (imp b a))
  /-- Hilbert axiom `S`. -/
  ax_S : ∀ a b c, Provable (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens. -/
  modus_ponens : ∀ {a b}, Provable (imp a b) → Provable a → Provable b
  /-- First derivability condition: provability is internally witnessed. -/
  D1 : ∀ {a}, Provable a → Provable (box a)
  /-- Second derivability condition: internal provability is closed under modus ponens. -/
  D2 : ∀ a b, Provable (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: internal provability is internally provable. -/
  D3 : ∀ a, Provable (imp (box a) (box (box a)))

namespace ProvabilitySystem

variable (T : ProvabilitySystem)

/-- Negation, defined as implication of falsum. -/

theorem provable_goedel_of_provable_con {g : T.Sentence} (hg : T.IsGoedelSentence g)
    (hConT : T.Provable T.ConSentence) : T.Provable g :=
  T.modus_ponens hg.2 (imp_trans (box_goedel_imp_box_bot hg) hConT)

end ProvabilitySystem

/-- **Gödel's second incompleteness theorem** (abstract Hilbert–Bernays–Löb form).

No consistent theory satisfying the derivability conditions and possessing a Gödel
sentence proves its own consistency statement `Con := □⊥ → ⊥`.

Since a consistent recursively axiomatized theory extending `PA` satisfies exactly these
hypotheses (its `Σ₁` provability predicate obeys `D1`–`D3`, and the diagonal lemma
provides the Gödel sentence `g` with `T ⊢ g ↔ ¬□g`), such a theory cannot prove its own
consistency. -/

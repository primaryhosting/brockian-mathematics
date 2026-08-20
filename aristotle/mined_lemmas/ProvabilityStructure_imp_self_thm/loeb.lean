/-!
# Goedel Second Incompleteness
Category: Frontier — Set Theory
Target: Frontier.Goedel_second_incompleteness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Gödel's second incompleteness theorem: *no consistent recursively axiomatized theory
`T` extending `PA` proves its own consistency statement `Con(T)`.*

Mathlib contains no arithmetization of syntax, so the full theorem cannot be quoted.
What is formalized and proved here is the standard **Hilbert–Bernays–Löb reduction**,
which is the mathematical content of the theorem once the arithmetization is in place:

* A `ProvabilityStructure` packages a theory's sentences, its provability relation
  `Thm`, a formalized provability operator `Box` (in the intended reading,
  `Box p` is the arithmetic sentence `Prov_T(⌜p⌝)`), and the hypotheses that hold for
  every recursively axiomatized `T ⊇ PA`:
  - closure of `Thm` under modus ponens and the implicational Hilbert axioms `K`, `S`
    (available since `T` extends `PA`, hence classical predicate logic);
  - the three **derivability conditions**
    `D1 : Thm p → Thm (Box p)`,
    `D2 : Thm (Box (p → q) → (Box p → Box q))`,
    `D3 : Thm (Box p → Box (Box p))`;
  - the **diagonal (fixed point) lemma**, in the single instance needed:
    for each sentence `A` there is a sentence `ψ` with `T ⊢ ψ ↔ (Box ψ → A)`.

* `ProvabilityStructure.loeb` is Löb's theorem in this setting, and
  `Frontier.Goedel_second_incompleteness` is the second incompleteness theorem:
  if `Thm` is consistent then `Con := Box ⊥ → ⊥` is not a theorem.

* `Frontier.provabilityStructure_nonvacuous` exhibits a structure satisfying **all**
  the hypotheses whose `Thm` is consistent, so the theorem is not vacuous: the
  hypotheses do not secretly entail inconsistency.
-/

universe u

/-- An abstract provability structure: the Hilbert–Bernays–Löb data attached to a
recursively axiomatized theory `T` extending `PA`.

`Sentence` are the sentences of `T`, `imp` and `bot` are implication and falsum,
`Thm p` means `T ⊢ p`, and `Box p` is the arithmetic sentence formalizing
"`p` is provable in `T`". -/
structure ProvabilityStructure where
  /-- The sentences of the theory. -/
  Sentence : Type u
  /-- Implication between sentences. -/
  imp : Sentence → Sentence → Sentence
  /-- The falsum sentence. -/
  bot : Sentence
  /-- The formalized provability operator: `Box p` says "`p` is provable". -/
  Box : Sentence → Sentence
  /-- `Thm p` means that `p` is a theorem of the theory. -/
  Thm : Sentence → Prop
  /-- Theorems are closed under modus ponens. -/
  mp : ∀ {p q}, Thm (imp p q) → Thm p → Thm q
  /-- The Hilbert axiom `K`. -/
  ax_k : ∀ p q, Thm (imp p (imp q p))
  /-- The Hilbert axiom `S`. -/
  ax_s : ∀ p q r, Thm (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- First derivability condition: provable sentences are provably provable. -/
  D1 : ∀ {p}, Thm p → Thm (Box p)
  /-- Second derivability condition: formalized modus ponens. -/
  D2 : ∀ p q, Thm (imp (Box (imp p q)) (imp (Box p) (Box q)))
  /-- Third derivability condition: formalized `D1`. -/
  D3 : ∀ p, Thm (imp (Box p) (Box (Box p)))
  /-- The diagonal lemma, in the instance needed for Löb's theorem: for every `A`
  there is a sentence `ψ` provably equivalent to `Box ψ → A`. -/
  fix : ∀ A, ∃ psi, Thm (imp psi (imp (Box psi) A)) ∧ Thm (imp (imp (Box psi) A) psi)

namespace ProvabilityStructure

variable (T : ProvabilityStructure)

/-- The consistency statement `Con(T) := ¬ Prov_T(⌜⊥⌝)`, written with `→ ⊥`. -/

theorem loeb (A : T.Sentence) (h : T.Thm (T.imp (T.Box A) A)) : T.Thm A := by
  obtain ⟨psi, hp1, hp2⟩ := T.fix A
  -- `T ⊢ Box ψ → Box (Box ψ → A)`
  have b2 : T.Thm (T.imp (T.Box psi) (T.Box (T.imp (T.Box psi) A))) :=
    T.mp (T.D2 _ _) (T.D1 hp1)
  -- `T ⊢ Box ψ → (Box (Box ψ) → Box A)`
  have b4 : T.Thm (T.imp (T.Box psi) (T.imp (T.Box (T.Box psi)) (T.Box A))) :=
    imp_trans b2 (T.D2 _ _)
  -- `T ⊢ Box ψ → Box A`
  have b6 : T.Thm (T.imp (T.Box psi) (T.Box A)) := imp_s b4 (T.D3 psi)
  -- `T ⊢ Box ψ → A`
  have b7 : T.Thm (T.imp (T.Box psi) A) := imp_trans b6 h
  exact T.mp b7 (T.D1 (T.mp hp2 b7))

end ProvabilityStructure

namespace Frontier

open ProvabilityStructure

/-- **Gödel's second incompleteness theorem** (Hilbert–Bernays–Löb form).

For any theory satisfying the derivability conditions and the diagonal lemma — in
particular any recursively axiomatized theory extending `PA` — consistency implies
that the consistency statement `Con := Box ⊥ → ⊥` is *not* provable. -/

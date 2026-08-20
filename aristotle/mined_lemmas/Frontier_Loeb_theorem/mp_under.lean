/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Löb's theorem states: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`, where `□` is the standard
provability predicate `Prov_PA(⌜·⌝)` of Peano arithmetic.

The proof of Löb's theorem uses only the following well-known facts about `PA` and its
provability predicate (the *Hilbert–Bernays–Löb derivability conditions* together with the
*diagonal lemma*):

* the theorems of `PA` are closed under *modus ponens*, and contain the propositional
  axioms `K : φ → (ψ → φ)` and `S : (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`;
* **D1** (necessitation): if `⊢ φ` then `⊢ □φ`;
* **D2** (distribution): `⊢ □(φ → ψ) → (□φ → □ψ)`;
* **D3**: `⊢ □φ → □□φ`;
* **Diagonal lemma**: for every `φ` there is a sentence `ψ` with `⊢ ψ ↔ (□ψ → φ)`.

We package exactly these data as `Frontier.ProvabilityCalculus` and prove Löb's theorem
in that generality (`Frontier.ProvabilityCalculus.loeb`), which is then the statement
`Frontier.Loeb_theorem`. Peano arithmetic with its usual provability predicate is an
instance of this structure; nothing else about `PA` is used in the argument.

Mathlib does not contain a provability predicate for `PA`, nor provability logic, nor
Löb's theorem (a search of the library for `Loeb`/`Löb`/provability turns up nothing that
applies), so the development below is self-contained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Frontier

universe u

/-- An abstract *provability calculus*: a language of sentences with implication and a
provability (`□`) operator, together with a set of theorems satisfying the propositional
axioms `K` and `S`, closure under modus ponens, and the three Hilbert–Bernays–Löb
derivability conditions.

Peano arithmetic, with `Sentence` the set of arithmetical sentences, `imp` material
implication, `box φ` the formalized statement `Prov_PA(⌜φ⌝)`, and `Thm` provability in
`PA`, is an instance. -/
structure ProvabilityCalculus where
  /-- The type of sentences of the language. -/
  Sentence : Type u
  /-- Material implication of the language. -/
  imp : Sentence → Sentence → Sentence
  /-- The provability operator `□`. -/
  box : Sentence → Sentence
  /-- `Thm φ` says that `φ` is a theorem of the theory. -/
  Thm : Sentence → Prop
  /-- The propositional axiom `K : φ → (ψ → φ)`. -/
  axiomK : ∀ p q, Thm (imp p (imp q p))
  /-- The propositional axiom `S : (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  axiomS : ∀ p q r, Thm (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  /-- Closure of the theorems under modus ponens. -/
  modusPonens : ∀ {p q}, Thm (imp p q) → Thm p → Thm q
  /-- Derivability condition **D1** (necessitation). -/
  D1 : ∀ {p}, Thm p → Thm (box p)
  /-- Derivability condition **D2** (distribution of `□` over implication). -/
  D2 : ∀ p q, Thm (imp (box (imp p q)) (imp (box p) (box q)))
  /-- Derivability condition **D3**. -/
  D3 : ∀ p, Thm (imp (box p) (box (box p)))

namespace ProvabilityCalculus

variable (T : ProvabilityCalculus)

local infixr:25 " ⟶ " => T.imp
local prefix:75 "□" => T.box

/-- The identity implication `φ → φ` is a theorem (the standard `K`,`S` derivation). -/

theorem mp_under {p q r : T.Sentence} (h₁ : T.Thm (p ⟶ (q ⟶ r))) (h₂ : T.Thm (p ⟶ q)) :
    T.Thm (p ⟶ r) :=
  T.modusPonens (T.modusPonens (T.axiomS p q r) h₁) h₂

/-- Transitivity of implication in the calculus. -/

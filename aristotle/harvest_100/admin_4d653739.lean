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
theorem imp_self (p : T.Sentence) : T.Thm (p ⟶ p) :=
  T.modusPonens (T.modusPonens (T.axiomS p (p ⟶ p) p) (T.axiomK p (p ⟶ p)))
    (T.axiomK p p)

variable {T}

/-- Modus ponens under a hypothesis: from `⊢ p → (q → r)` and `⊢ p → q` infer `⊢ p → r`. -/
theorem mp_under {p q r : T.Sentence} (h₁ : T.Thm (p ⟶ (q ⟶ r))) (h₂ : T.Thm (p ⟶ q)) :
    T.Thm (p ⟶ r) :=
  T.modusPonens (T.modusPonens (T.axiomS p q r) h₁) h₂

/-- Transitivity of implication in the calculus. -/
theorem imp_trans {p q r : T.Sentence} (h₁ : T.Thm (p ⟶ q)) (h₂ : T.Thm (q ⟶ r)) :
    T.Thm (p ⟶ r) :=
  mp_under (T.modusPonens (T.axiomK (q ⟶ r) p) h₂) h₁

/-- A derived form of **D2**: from `⊢ p → q` infer `⊢ □p → □q`. -/
theorem box_mono {p q : T.Sentence} (h : T.Thm (p ⟶ q)) : T.Thm (□p ⟶ □q) :=
  T.modusPonens (T.D2 p q) (T.D1 h)

/-- **Löb's theorem**, abstract form. If `ψ` is a Gödel fixed point of `□· → φ`, i.e.
`⊢ ψ → (□ψ → φ)` and `⊢ (□ψ → φ) → ψ`, and if `⊢ □φ → φ`, then `⊢ φ`. -/
theorem loeb_of_fixedPoint {p psi : T.Sentence}
    (hfix₁ : T.Thm (psi ⟶ (□psi ⟶ p))) (hfix₂ : T.Thm ((□psi ⟶ p) ⟶ psi))
    (h : T.Thm (□p ⟶ p)) : T.Thm p := by
  -- `⊢ □ψ → □(□ψ → φ)`
  have h1 : T.Thm (□psi ⟶ □(□psi ⟶ p)) := box_mono hfix₁
  -- `⊢ □ψ → (□□ψ → □φ)`
  have h2 : T.Thm (□psi ⟶ (□(□psi) ⟶ □p)) := imp_trans h1 (T.D2 (□psi) p)
  -- `⊢ □ψ → □φ`, using **D3**
  have h3 : T.Thm (□psi ⟶ □p) := mp_under h2 (T.D3 psi)
  -- `⊢ □ψ → φ`
  have h4 : T.Thm (□psi ⟶ p) := imp_trans h3 h
  -- hence `⊢ ψ`, and so `⊢ □ψ`
  have h5 : T.Thm psi := T.modusPonens hfix₂ h4
  have h6 : T.Thm (□psi) := T.D1 h5
  exact T.modusPonens h4 h6

/-- `T` *has Gödel fixed points* (the diagonal lemma) if every `φ` admits a sentence `ψ`
provably equivalent to `□ψ → φ`. This holds for `PA` by the diagonal lemma. -/
def HasFixedPoints (T : ProvabilityCalculus) : Prop :=
  ∀ p : T.Sentence, ∃ psi : T.Sentence,
    T.Thm (T.imp psi (T.imp (T.box psi) p)) ∧ T.Thm (T.imp (T.imp (T.box psi) p) psi)

/-- **Löb's theorem**: in any provability calculus with Gödel fixed points (in particular
in `PA` with its provability predicate), if `⊢ □φ → φ` then `⊢ φ`. -/
theorem loeb (hfp : HasFixedPoints T) {p : T.Sentence} (h : T.Thm (T.imp (T.box p) p)) :
    T.Thm p :=
  let ⟨_psi, h₁, h₂⟩ := hfp p
  loeb_of_fixedPoint h₁ h₂ h

end ProvabilityCalculus

/-- **Löb's theorem for Peano arithmetic.**

If `T` is a theory whose provability predicate `□` satisfies the Hilbert–Bernays–Löb
derivability conditions and for which the diagonal lemma holds — as is the case for `PA`
with `□φ := Prov_PA(⌜φ⌝)` — then `T ⊢ (□φ → φ)` implies `T ⊢ φ`. -/
theorem Loeb_theorem (T : ProvabilityCalculus) (hfp : T.HasFixedPoints) (p : T.Sentence)
    (h : T.Thm (T.imp (T.box p) p)) : T.Thm p :=
  T.loeb hfp h

/-- **Gödel's second incompleteness theorem**, as a corollary of Löb's theorem: taking
`φ = ⊥`, the consistency statement `Con := □⊥ → ⊥` is provable only if the theory is
inconsistent. -/
theorem not_provable_consistency (T : ProvabilityCalculus) (hfp : T.HasFixedPoints)
    (bot : T.Sentence) (hcon : ¬ T.Thm bot) :
    ¬ T.Thm (T.imp (T.box bot) bot) :=
  fun h => hcon (Loeb_theorem T hfp bot h)

/-! ### Non-vacuity

The axioms of `ProvabilityCalculus` together with `HasFixedPoints` are satisfiable, so the
statements above are not vacuous. (Of course the intended model is `PA`; the following
trivial model merely certifies consistency of the assumptions.) -/

/-- The inconsistent calculus: every sentence is a theorem. -/
def trivialCalculus : ProvabilityCalculus where
  Sentence := Unit
  imp _ _ := ()
  box _ := ()
  Thm _ := True
  axiomK _ _ := trivial
  axiomS _ _ _ := trivial
  modusPonens _ _ := trivial
  D1 _ := trivial
  D2 _ _ := trivial
  D3 _ := trivial

theorem trivialCalculus_hasFixedPoints : trivialCalculus.HasFixedPoints :=
  fun _ => ⟨(), trivial, trivial⟩

end Frontier

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


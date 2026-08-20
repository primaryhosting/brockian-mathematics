/-!
# Loeb Theorem
Category: Frontier — Set Theory
Target: Frontier.Loeb_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (v4.28.0) contains no formalization of a provability predicate for Peano
arithmetic, of the Hilbert–Bernays–Löb derivability conditions, or of the diagonal
(fixed-point) lemma: a search of the library turns up no relevant declarations, so
`exact?`/`apply?` have nothing to offer here.  We therefore give the standard
abstract formalization of Löb's theorem: it is proved for an arbitrary system of
sentences equipped with implication, a provability operator `box` and a theoremhood
predicate `Thm` satisfying

* the minimal-logic axioms `K` and `S` together with modus ponens,
* the three derivability conditions of Hilbert–Bernays–Löb,
* the instance of the diagonal lemma producing a sentence `q` with
  `⊢ q ↔ (□q → p)`.

Peano arithmetic together with its usual provability predicate is such a system,
so this yields Löb's theorem for PA: if `PA ⊢ (□φ → φ)` then `PA ⊢ φ`.
-/

universe u

namespace Frontier

/-- An abstract system of sentences with a provability operator satisfying the
Hilbert–Bernays–Löb derivability conditions and the relevant instance of the
diagonal lemma.  `imp a b` is the (formal) implication `a → b`, `box a` is the
formalized statement "`a` is provable", and `Thm a` means "`a` is a theorem of
the system" (for Peano arithmetic: `PA ⊢ a`). -/
structure ProvabilitySystem (S : Type u) where
  /-- Formal implication between sentences. -/
  imp : S → S → S
  /-- The provability operator `□`: `box a` is the sentence "`a` is provable". -/
  box : S → S
  /-- Theoremhood: `Thm a` says that `a` is provable in the system. -/
  Thm : S → Prop
  /-- Propositional axiom `K`: `⊢ a → (b → a)`. -/
  ax_k : ∀ a b, Thm (imp a (imp b a))
  /-- Propositional axiom `S`: `⊢ (a → (b → c)) → ((a → b) → (a → c))`. -/
  ax_s : ∀ a b c, Thm (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  /-- Modus ponens. -/
  mp : ∀ {a b}, Thm (imp a b) → Thm a → Thm b
  /-- First derivability condition (necessitation): if `⊢ a` then `⊢ □a`. -/
  hbl1 : ∀ {a}, Thm a → Thm (box a)
  /-- Second derivability condition: `⊢ □(a → b) → (□a → □b)`. -/
  hbl2 : ∀ a b, Thm (imp (box (imp a b)) (imp (box a) (box b)))
  /-- Third derivability condition: `⊢ □a → □□a`. -/
  hbl3 : ∀ a, Thm (imp (box a) (box (box a)))
  /-- The diagonal lemma, in the instance needed for Löb's theorem: for every
  sentence `p` there is a sentence `q` with `⊢ q ↔ (□q → p)`. -/
  diagonal : ∀ p, ∃ q, Thm (imp q (imp (box q) p)) ∧ Thm (imp (imp (box q) p) q)

namespace ProvabilitySystem

variable {S : Type u} (P : ProvabilitySystem S)

/-- Weakening: from `⊢ b` infer `⊢ a → b`. -/
theorem weaken {a b : S} (h : P.Thm b) : P.Thm (P.imp a b) :=
  P.mp (P.ax_k b a) h

/-- Hypothetical syllogism: from `⊢ a → b` and `⊢ b → c` infer `⊢ a → c`. -/
theorem syllogism {a b c : S} (h₁ : P.Thm (P.imp a b)) (h₂ : P.Thm (P.imp b c)) :
    P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_s a b c) (P.weaken h₂)) h₁

/-- Distribution of an implication under a common antecedent: from `⊢ a → (b → c)`
and `⊢ a → b` infer `⊢ a → c`. -/
theorem distrib {a b c : S} (h₁ : P.Thm (P.imp a (P.imp b c))) (h₂ : P.Thm (P.imp a b)) :
    P.Thm (P.imp a c) :=
  P.mp (P.mp (P.ax_s a b c) h₁) h₂

/-- Boxed modus ponens: from `⊢ a → b` infer `⊢ □a → □b`. -/
theorem box_mono {a b : S} (h : P.Thm (P.imp a b)) : P.Thm (P.imp (P.box a) (P.box b)) :=
  P.mp (P.hbl2 a b) (P.hbl1 h)

end ProvabilitySystem

/-- **Löb's theorem.**  In any system satisfying the Hilbert–Bernays–Löb
derivability conditions and the diagonal lemma — in particular in Peano
arithmetic with its standard provability predicate — if `⊢ □φ → φ` then `⊢ φ`. -/
theorem Loeb_theorem {S : Type u} (P : ProvabilitySystem S) (φ : S)
    (h : P.Thm (P.imp (P.box φ) φ)) : P.Thm φ := by
  obtain ⟨q, hq₁, hq₂⟩ := P.diagonal φ
  -- `⊢ □q → □(□q → φ)`
  have step1 : P.Thm (P.imp (P.box q) (P.box (P.imp (P.box q) φ))) := P.box_mono hq₁
  -- `⊢ □q → (□□q → □φ)`
  have step2 : P.Thm (P.imp (P.box q) (P.imp (P.box (P.box q)) (P.box φ))) :=
    P.syllogism step1 (P.hbl2 (P.box q) φ)
  -- `⊢ □q → □φ`, using the third derivability condition `⊢ □q → □□q`
  have step3 : P.Thm (P.imp (P.box q) (P.box φ)) := P.distrib step2 (P.hbl3 q)
  -- `⊢ □q → φ`
  have step4 : P.Thm (P.imp (P.box q) φ) := P.syllogism step3 h
  -- hence `⊢ q`, so `⊢ □q`, so `⊢ φ`
  have step5 : P.Thm q := P.mp hq₂ step4
  exact P.mp step4 (P.hbl1 step5)

/-- The hypotheses of `Frontier.Loeb_theorem` are consistent: they are satisfied by
the (degenerate) one-sentence system, so the theorem is not vacuous. -/
theorem loeb_hypotheses_satisfiable : ∃ P : ProvabilitySystem Unit, ∀ a, P.Thm a :=
  ⟨{ imp := fun _ _ => ()
     box := id
     Thm := fun _ => True
     ax_k := fun _ _ => trivial
     ax_s := fun _ _ _ => trivial
     mp := fun _ _ => trivial
     hbl1 := fun _ => trivial
     hbl2 := fun _ _ => trivial
     hbl3 := fun _ => trivial
     diagonal := fun _ => ⟨(), trivial, trivial⟩ }, fun _ => trivial⟩

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


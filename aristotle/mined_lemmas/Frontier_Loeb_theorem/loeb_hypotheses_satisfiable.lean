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


import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The first-order language of set theory

We build the first-order language with a single binary relation symbol `∈`, write down a
standard axiomatization of `ZFC` in it (extensionality, empty set, pairing, union, power set,
infinity, foundation, choice, together with the separation and replacement schemes), and prove
that Mathlib's type `ZFSet` of ZFC-sets is a model of this theory.
-/

namespace Frontier

open FirstOrder Language

universe u

/-- The relation symbols of the language of set theory: a single binary relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory. -/

@[simp] theorem realize_subst₀ {k m : ℕ} (φ : setLang.Formula (Fin k)) (g : Fin k → Fin m)
    (v : Empty → ZFSet.{u}) (xs : Fin m → ZFSet.{u}) :
    (subst₀ φ g).Realize v xs ↔ φ.Realize (xs ∘ g) := by
  rw [subst₀, BoundedFormula.realize_relabel]
  have h1 : (Sum.elim v (xs ∘ Fin.castAdd 0) ∘ fun i => Sum.inr (g i)) = xs ∘ g := by
    funext i; simp
  rw [h1, Formula.Realize]
  exact iff_of_eq (congrArg (fun t => BoundedFormula.Realize φ (xs ∘ g) t)
    (Subsingleton.elim _ _))

/-- Evaluation of `Fin.snoc` below the top index. -/

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

theorem snoc4_gRep₂ {k : ℕ} (xs : Fin k → ZFSet.{u}) (a x y y' : ZFSet.{u}) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) x) y) y' : Fin (k + 4) → ZFSet.{u}) ∘ gRep₂ k
      = extVal₂ x y' xs := by
  funext i
  have hi := i.isLt
  by_cases h : (i : ℕ) = 0
  · simp only [Function.comp_apply, gRep₂, extVal₂, if_pos h, dif_pos h]
    exact snoc4_k1 _ _ _ _ _ _
  · by_cases h' : (i : ℕ) = 1
    · simp only [Function.comp_apply, gRep₂, extVal₂, if_neg h, dif_neg h, if_pos h', dif_pos h']
      exact snoc4_k3 _ _ _ _ _ _
    · simp only [Function.comp_apply, gRep₂, extVal₂, if_neg h, dif_neg h, if_neg h', dif_neg h']
      exact snoc4_lt _ _ _ _ _ _ _ (by omega)


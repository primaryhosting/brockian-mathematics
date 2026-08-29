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

theorem snoc4_k3 {α : Type*} {k : ℕ} (xs : Fin k → α) (a b c d : α) (h : k + 3 < k + 4) :
    (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc xs a) b) c) d : Fin (k + 4) → α) ⟨k + 3, h⟩ = d :=
  snoc_eq _ _ _ rfl

/-- The valuation sending variable `0` to `x` and variable `i + 1` to `ps i`. -/

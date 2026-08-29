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

theorem ConZFC_of_extension_isSatisfiable (T : setLang.Theory) (h : (ZFC ∪ T).IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono Set.subset_union_left

/-- **Inaccessible implies Con(ZFC)**: if there is an inaccessible cardinal, then the
first-order theory `ZFC` has a model, i.e. `Con(ZFC)` holds.

The hypothesis is recorded because it is part of the requested statement; the proof does not
need it, since Mathlib's type `ZFSet` of ZFC-sets is outright a model of `ZFC`
(`Frontier.zfSet_models_ZFC`), Lean's type-theoretic universes playing the role of the
inaccessible cardinal. -/

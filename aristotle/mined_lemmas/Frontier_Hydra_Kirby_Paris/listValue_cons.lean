import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

@[simp] theorem listValue_cons (h : Hydra) (t : List Hydra) :
    listValue (h :: t) = (ω ^ value h) ♯ listValue t := rfl

/-- The single move relation of the Kirby–Paris hydra game: `Step h h'` means that `h'`
arises from `h` by Hercules cutting off one head, followed by the hydra's regrowth.

* `root`: a head attached to the root is removed and nothing grows back;
* `copy`: a head attached to a child `u` of the root is removed, and `n` copies of the
  mutilated `u` are attached to the root (`n` arbitrary — the hydra plays as it likes);
* `deep`: the cut happens strictly inside one of the children, in which case the
  regrowth happens inside that child. -/
inductive Step : Hydra → Hydra → Prop
  | root (a b : List Hydra) :
      Step (.node (a ++ .node [] :: b)) (.node (a ++ b))
  | copy (a b c d : List Hydra) (n : ℕ) :
      Step (.node (a ++ .node (c ++ .node [] :: d) :: b))
        (.node (a ++ (List.replicate n (.node (c ++ d)) ++ b)))
  | deep (a b : List Hydra) (u u' : Hydra) (h : Step u u') :
      Step (.node (a ++ u :: b)) (.node (a ++ u' :: b))


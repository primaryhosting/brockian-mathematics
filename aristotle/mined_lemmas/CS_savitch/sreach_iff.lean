/-
The configuration graph of a space bounded nondeterministic machine, and the
deterministic middle-first search run on it.
-/
import RequestProject.NTM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000

namespace CS
namespace Sim

variable (M : NTM) (s : ℕ) (x : List Bool)

/-- Vertices of the configuration graph: the configurations of `M`, plus a sink
`none` which is entered from every accepting configuration. -/
abbrev Node : Type := Option (Conf M x.length s)

/-- Edges of the configuration graph.  A single edge query only inspects the
local transition table of `M` at the scanned symbols. -/

theorem sreach_iff (E : V → V → Bool) (all : List V) (hall : ∀ v : V, v ∈ all)
    (k : ℕ) (u v : V) :
    sreach E all k u v = true ↔ reachLe (fun a b => E a b = true) (2 ^ k) u v := by
  induction k generalizing u v with
  | zero =>
      simp only [sreach, Bool.or_eq_true, decide_eq_true_eq, pow_zero]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr ⟨u, rfl, h⟩
      · rintro (h | ⟨w, hw, hwv⟩)
        · exact Or.inl h
        · cases hw; exact Or.inr hwv
  | succ k ih =>
      rw [reachLe_two_pow_succ]
      simp only [sreach, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨m, _, h1, h2⟩
        exact ⟨m, (ih u m).1 h1, (ih m v).1 h2⟩
      · rintro ⟨m, h1, h2⟩
        exact ⟨m, hall m, (ih u m).2 h1, (ih m v).2 h2⟩

end Spec

end CS

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


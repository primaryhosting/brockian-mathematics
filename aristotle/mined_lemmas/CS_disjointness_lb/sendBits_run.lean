/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not permit a module docstring `/-! ... -/` before `import`;
-- the header is repeated verbatim as a module docstring just below the imports.)

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
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

namespace CS

/-! ## A model of two-party communication protocols

A deterministic protocol is a binary protocol tree.  At an `alice` node the first
player sends one bit determined by her input `x : X`; at a `bob` node the second
player sends one bit determined by his input `y : Y`; at a `leaf` the output is
produced (we allow the output at a leaf to depend on Bob's input, which makes the
model *stronger* than the usual one and hence the lower bound stronger; in
particular one-way protocols, where Bob never speaks, are covered).

The cost of a protocol is the depth of the tree, i.e. the worst-case number of
bits exchanged.
-/

/-- A deterministic two-party communication protocol. -/
inductive Prot (X Y : Type) : Type
  | leaf : (Y → Bool) → Prot X Y
  | alice : (X → Bool) → (Bool → Prot X Y) → Prot X Y
  | bob : (Y → Bool) → (Bool → Prot X Y) → Prot X Y

namespace Prot

variable {X Y : Type}

/-- The output of a protocol on a pair of inputs. -/

theorem sendBits_run {n : ℕ} (x y : Fin n → Bool) :
    ∀ (l : List (Fin n)) (acc : Fin n → Bool), (∀ j, j ∉ l → acc j = x j) →
      (sendBits l acc).run x y = disj n x y := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      have : acc = x := funext fun j => hacc j (by simp)
      simp [sendBits, Prot.run, this]
  | cons i l ih =>
      intro acc hacc
      refine (ih (Function.update acc i (x i)) ?_)
      intro j hj
      by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact hacc j (by simp [hji, hj])

/-- **Upper bound.**  There is a deterministic protocol of cost `n` computing set
disjointness on `n`-element ground sets.  Together with
`CS.disjointness_lb_deterministic` this shows the deterministic communication
complexity of set disjointness is exactly `n`. -/

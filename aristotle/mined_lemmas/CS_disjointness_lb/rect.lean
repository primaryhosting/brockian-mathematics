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

theorem rect (P : Prot X Y) : ∀ (x y x' y' : _), P.tr x y = P.tr x' y' →
    P.tr x y' = P.tr x' y' ∧ P.run x y' = P.run x' y' := by
  induction P with
  | leaf g => intro x y x' y' _; exact ⟨rfl, rfl⟩
  | alice f k ih =>
      intro x y x' y' h
      simp only [tr] at h
      obtain ⟨h1, h2⟩ := List.cons.injEq .. ▸ h
      have h2' : (k (f x)).tr x y = (k (f x)).tr x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (f x) x y x' y' h2'
      refine ⟨?_, ?_⟩
      · simp only [tr, h1]
        rw [← h1, ha, h1]
      · simp only [run, h1]
        rw [← h1, hb, h1]
  | bob f k ih =>
      intro x y x' y' h
      simp only [tr] at h
      obtain ⟨h1, h2⟩ := List.cons.injEq .. ▸ h
      have h2' : (k (f y)).tr x y = (k (f y)).tr x' y' := by rw [h2, h1]
      obtain ⟨ha, hb⟩ := ih (f y) x y x' y' h2'
      refine ⟨?_, ?_⟩
      · simp only [tr, ← h1]
        rw [ha]
      · simp only [run, ← h1]
        exact hb

end Prot

/-! ## Set disjointness -/

/-- The set-disjointness predicate on `n`-element ground sets: `true` iff the
sets (given by their indicator vectors) are disjoint. -/

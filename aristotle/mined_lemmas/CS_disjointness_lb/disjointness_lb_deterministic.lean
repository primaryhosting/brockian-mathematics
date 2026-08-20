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

/-
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

universe u v

/-- A deterministic two-party communication protocol tree over inputs `X` (Alice) and `Y` (Bob).
`alice m k` means Alice sends the bit `m x` and the protocol continues with `k (m x)`;
`bob m k` means Bob sends the bit `m y`. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → (Bool → Protocol X Y) → Protocol X Y
  | bob : (Y → Bool) → (Bool → Protocol X Y) → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on a given pair of inputs. -/

theorem disjointness_lb_deterministic {n : ℕ}
    (P : Protocol (Finset (Fin n) × Unit) (Finset (Fin n) × Unit))
    (hP : ∀ (a b : Finset (Fin n)) (ra rb : Unit),
      run P (a, ra) (b, rb) = decide (Disjoint a b)) :
    n ≤ depth P := by
  refine disjointness_lb P (fun a b ra rb h => ?_) (fun a b h => ⟨(), (), ?_⟩)
  · rw [hP]; simp [h]
  · rw [hP]; simp [h]

/-- Randomized corollary: if the protocol never accepts an intersecting pair, and accepts each
disjoint pair with probability at least `1 - ε` for some `ε < 1` (over uniformly chosen private
random strings), then it must exchange at least `n` bits. -/

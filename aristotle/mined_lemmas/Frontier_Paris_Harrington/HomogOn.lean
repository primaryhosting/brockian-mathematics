/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 rejects a `/-!` module docstring before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring
-- immediately after the imports.)
import RequestProject.Ramsey

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

namespace Frontier

/-- A finite set of natural numbers is *relatively large* (in the sense of
Paris–Harrington) if it is nonempty and its cardinality is at least its least
element. -/

def HomogOn (n : ℕ) {k : ℕ} (c : Finset ℕ → Fin k) (A : Set ℕ) : Prop :=
  ∀ s t : Finset ℕ, (↑s : Set ℕ) ⊆ A → (↑t : Set ℕ) ⊆ A → s.card = n → t.card = n → c s = c t

/-- One step of the construction in the proof of the infinite Ramsey theorem:
given an infinite set `T`, we find `a ∈ T` and an infinite `T' ⊆ T` consisting of
elements above `a` such that `c (insert a ·)` is constant on `n`-subsets of `T'`. -/

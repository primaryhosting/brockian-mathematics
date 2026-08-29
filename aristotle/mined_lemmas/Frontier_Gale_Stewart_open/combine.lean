/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
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

variable {A : Type*}

/-- The list of the first `n` moves of the infinite play `x`. -/

def combine (σ τ : List A → A) : List A → A :=
  fun p => if Even p.length then σ p else τ p

/-- `Iwin W p` : player I can force, from the position `p`, that the play ends up in the
open set `W`; the "base" case records that the position `p` already secures `W`. -/
inductive Iwin (W : Set (ℕ → A)) : List A → Prop
  | base (p : List A) : (∀ x : ℕ → A, prefixOf x p.length = p → x ∈ W) → Iwin W p
  | stepI (p : List A) (a : A) : Even p.length → Iwin W (p ++ [a]) → Iwin W p
  | stepII (p : List A) : ¬ Even p.length → (∀ a : A, Iwin W (p ++ [a])) → Iwin W p

section

variable [Nonempty A] (W : Set (ℕ → A))

/-- If `Iwin W p`, then player I has a strategy which, from position `p`, forces `W`. -/

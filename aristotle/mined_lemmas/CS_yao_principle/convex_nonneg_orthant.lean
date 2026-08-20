/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Overview

Mathlib has no minimax theorem, so the result is proved from scratch.  The only nontrivial
input from Mathlib is the separation theorem `geometric_hahn_banach_compact_closed`
(`Mathlib/Analysis/LocallyConvex/Separation.lean`), which is used to prove Ville's theorem of
the alternative (`CS.ville_alternative`).  Yao's principle then follows by applying the
alternative to the shifted cost matrix `cost a x - v`, where `v` is the randomized complexity,
together with weak duality (`CS.distCost_le_randCost`).
-/

namespace CS

section Orthant

variable {A : Type*}

/-- The nonnegative orthant in `A → ℝ` is convex. -/

lemma convex_nonneg_orthant : Convex ℝ {y : A → ℝ | ∀ a, 0 ≤ y a} := by
  intro y hy z hz s t hs ht _ a
  exact add_nonneg (mul_nonneg hs (hy a)) (mul_nonneg ht (hz a))

/-- The nonnegative orthant in `A → ℝ` is closed. -/

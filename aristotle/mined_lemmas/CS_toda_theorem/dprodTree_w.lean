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
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem dprodTree_w (n : ℕ) (D : ℕ → GapData) (w : ℕ) (hw : ∀ i, (D i).w ≤ w) :
    ∀ (d off : ℕ), (dprodTree n D d off).w ≤ 2 ^ d * w
  | 0, off => by simpa [dprodTree] using hw off
  | (d + 1), off => by
      have h1 := dprodTree_w n D w hw d off
      have h2 := dprodTree_w n D w hw d (off + 2 ^ d)
      show (dprodTree n D d off).w + (dprodTree n D d (off + 2 ^ d)).w ≤ _
      have : 2 ^ (d + 1) * w = 2 ^ d * w + 2 ^ d * w := by ring
      omega


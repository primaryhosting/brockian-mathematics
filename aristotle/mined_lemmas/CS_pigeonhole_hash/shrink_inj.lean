import Mathlib
import RequestProject.Main

/-!
# Pigeonhole Hash — generalisation to arbitrary finite types

A Mathlib-based restatement of `CS.pigeonhole_hash` for arbitrary finite key and value
types, derived from the core-library version proved in `RequestProject/Main.lean`.
-/

namespace CS

/-- Any hash function from a set of `n + 1` keys to a set of `n` hash values has a
collision. -/

private theorem shrink_inj {v x y : Nat} (hxv : x ≠ v) (hyv : y ≠ v)
    (h : shrink v x = shrink v y) : x = y := by
  unfold shrink at h; split at h <;> split at h <;> omega

/-- **Pigeonhole principle for hash functions.**

Any hash function `f` from an `(n+1)`-element set of keys, `Fin (n + 1)`, to an
`n`-element set of hash values, `Fin n`, has a collision: there are two distinct keys
`a ≠ b` with `f a = f b`.

The proof is by induction on `n`. For `n = 0` the codomain is empty, so no such `f` can be
applied to a key. For the step, if some key other than the last one already collides with
the last key we are done; otherwise no key is mapped to `f last`, so deleting that value
from the codomain turns `f` (restricted to the first `n + 1` keys) into a hash function
`Fin (n + 1) → Fin n`, and the induction hypothesis supplies a collision. -/

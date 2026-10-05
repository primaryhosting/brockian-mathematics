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

private theorem shrink_lt {n v x : Nat} (hv : v < n + 1) (hx : x < n + 1) (hne : x ≠ v) :
    shrink v x < n := by
  unfold shrink; split <;> omega

/-- `shrink v` is injective away from `v`. -/

import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

lemma pentN_injective : Function.Injective pentN := by
  intro a b hab
  have h1 := pentN_spec a
  have h2 := pentN_spec b
  rw [hab] at h1
  have h3 : a * (3 * a - 1) = b * (3 * b - 1) := by omega
  have h4 : (a - b) * (3 * (a + b) - 1) = 0 := by ring_nf; ring_nf at h3; linarith
  rcases mul_eq_zero.mp h4 with h | h
  · omega
  · omega


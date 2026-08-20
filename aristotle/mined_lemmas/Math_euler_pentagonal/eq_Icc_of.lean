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

lemma eq_Icc_of {s : Finset ℕ} (h : ∀ x, mn s ≤ x → x ≤ mx s → mx s - x < sl s) :
    s = Finset.Icc (mn s) (mx s) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨mn_le hx, le_mx hx⟩
  · intro hx
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hx
    have hmem := mem_of_lt_sl (h x h1 h2)
    rwa [show mx s - (mx s - x) = x by omega] at hmem


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

lemma mn_Icc {a b : ℕ} (h : a ≤ b) : mn (Finset.Icc a b) = a := by
  refine le_antisymm (mn_le (Finset.mem_Icc.mpr ⟨le_rfl, h⟩)) ?_
  have := mn_mem (s := Finset.Icc a b) ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, h⟩⟩
  exact (Finset.mem_Icc.mp this).1


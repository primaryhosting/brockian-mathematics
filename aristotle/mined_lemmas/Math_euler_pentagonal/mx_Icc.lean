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

lemma mx_Icc {a b : ℕ} (h : a ≤ b) : mx (Finset.Icc a b) = b := by
  refine le_antisymm (Finset.sup_le ?_) (le_mx (Finset.mem_Icc.mpr ⟨h, le_rfl⟩))
  intro x hx
  simp only [id_eq]
  exact (Finset.mem_Icc.mp hx).2


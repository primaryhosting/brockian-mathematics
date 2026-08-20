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

lemma mem_DP {n : ℕ} {s : Finset ℕ} : s ∈ DP n ↔ (0 ∉ s ∧ ∑ i ∈ s, i = n) := by
  simp only [DP, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h => h.2, ?_⟩
  rintro ⟨h0, hsum⟩
  refine ⟨?_, h0, hsum⟩
  intro x hx
  have hle : x ≤ ∑ i ∈ s, i :=
    Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
  exact Finset.mem_range.mpr (by omega)

/-- The signed count of partitions of `n` into distinct parts. -/

/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
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

set_option grind.warning false

namespace Math2

/-- The **Erdős–Ko–Rado theorem** for families of subsets of `[n] = {0, 1, ..., n-1}`.

If `𝒜` is a family of `k`-element subsets of `Finset.range n` that is intersecting (any two
members, including a member with itself, meet), and `n ≥ 2 * k`, then `#𝒜 ≤ (n-1).choose (k-1)`.

The proof transfers the statement to `Finset (Fin n)` and applies Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/

lemma card_star {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (star n k).card = (n - 1).choose (k - 1) := by
  classical
  have hbij : (star n k).card = ((Finset.Ico 1 n).powersetCard (k - 1)).card := by
    refine Finset.card_bij (fun A _ => A.erase 0) ?_ ?_ ?_
    · intro A hA
      rw [mem_star] at hA
      obtain ⟨⟨hsub, hcard⟩, hzero⟩ := hA
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, ?_⟩
      · have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
        have hxn : x < n := Finset.mem_range.1 (hsub (Finset.mem_of_mem_erase hx))
        exact Finset.mem_Ico.2 ⟨Nat.one_le_iff_ne_zero.2 hx0, hxn⟩
      · rw [Finset.card_erase_of_mem hzero, hcard]
    · intro A hA B hB hAB
      rw [mem_star] at hA hB
      have := congrArg (insert 0) hAB
      rwa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] at this
    · intro B hB
      rw [Finset.mem_powersetCard] at hB
      obtain ⟨hsub, hcard⟩ := hB
      have hzero : 0 ∉ B := fun h => by simpa using (Finset.mem_Ico.1 (hsub h)).1
      refine ⟨insert 0 B, ?_, ?_⟩
      · rw [mem_star]
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Finset.mem_range.2 hn
          · exact Finset.mem_range.2 (Finset.mem_Ico.1 (hsub hx)).2
        · rw [Finset.card_insert_of_notMem hzero, hcard]
          omega
      · show (insert 0 B).erase 0 = B
        exact Finset.erase_insert hzero
  rw [hbij, Finset.card_powersetCard, Nat.card_Ico]

/-- **Sharpness of Erdős–Ko–Rado**: for `1 ≤ k` the star family (all `k`-subsets of `[n]`
containing a fixed element) is an intersecting `k`-uniform family of subsets of `[n]`
attaining the bound `(n-1).choose (k-1)`. -/

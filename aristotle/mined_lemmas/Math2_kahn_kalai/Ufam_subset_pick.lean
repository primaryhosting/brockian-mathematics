/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma Ufam_subset_pick {H : Finset (Finset α)} {W U : Finset α} {m : ℕ}
    (hU : U ∈ Ufam H W m) : U ⊆ pick H (W ∪ U) := by
  obtain ⟨S, hS, _, hEq⟩ := mem_Ufam_iff.1 hU
  rw [← hEq]
  exact minFrag_subset_pick hS

/-- Reweighting: removing `U` from `W ∪ U` costs a factor at most `r ^ -|U|`. -/

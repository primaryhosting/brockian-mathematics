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

lemma Ufam_card {H : Finset (Finset α)} {W U : Finset α} {m : ℕ}
    (hU : U ∈ Ufam H W m) : m ≤ 2 * U.card := by
  obtain ⟨S, _, hbig, hEq⟩ := mem_Ufam_iff.1 hU
  rw [← hEq]; exact hbig

omit [Fintype α] in

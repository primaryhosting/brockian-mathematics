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

lemma mem_Ufam_iff {H : Finset (Finset α)} {W U : Finset α} {m : ℕ} :
    U ∈ Ufam H W m ↔ ∃ S ∈ H, m ≤ 2 * (minFrag H W S).card ∧ minFrag H W S = U := by
  simp only [Ufam, bigG, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S, ⟨hS, hbig⟩, hEq⟩; exact ⟨S, hS, hbig, hEq⟩
  · rintro ⟨S, hS, hbig, hEq⟩; exact ⟨S, ⟨hS, hbig⟩, hEq⟩

omit [Fintype α] in

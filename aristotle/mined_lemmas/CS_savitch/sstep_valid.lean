/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem sstep_valid {N K : ℕ} (edge : Bool → ℕ → ℕ → Prop) (b : Bool) {p : SState}
    (h : SValid N K p) : SValid N K (sstep N edge b p) := by
  obtain ⟨r, l⟩ := p
  cases l with
  | nil => exact h
  | cons F rest =>
    obtain ⟨hchain, hall⟩ := h
    have hrest : List.IsChain (fun a b : Frame => b.k = a.k + 1) rest :=
      (List.isChain_cons.1 hchain).2
    have hallrest : ∀ G ∈ rest, FrameOk N K G := fun G hG => hall G (List.mem_cons_of_mem _ hG)
    have hF : FrameOk N K F := hall F (by simp)
    have hFk := hF.hk
    have hFu := hF.hu
    have hFv := hF.hv
    have hFm := hF.hm
    have hpop : ∀ r' : Option Bool, SValid N K ((r', rest) : SState) :=
      fun _ => ⟨hrest, hallrest⟩
    have hpush : ∀ A B : Frame, B.k = F.k → A.k + 1 = B.k → FrameOk N K A → FrameOk N K B →
        SValid N K ((none, A :: B :: rest) : SState) := by
      intro A B hB hA hAok hBok
      refine ⟨isChain_push (by omega) (isChain_cons_replace hB hchain), ?_⟩
      intro G hG
      simp only [List.mem_cons] at hG
      rcases hG with rfl | rfl | hG
      · exact hAok
      · exact hBok
      · exact hallrest G hG
    have hrepl : ∀ C : Frame, C.k = F.k → FrameOk N K C →
        SValid N K ((none, C :: rest) : SState) := by
      intro C hC hCok
      refine ⟨isChain_cons_replace hC hchain, ?_⟩
      intro G hG
      simp only [List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact hCok
      · exact hallrest G hG
    cases r with
    | none =>
      by_cases hk : F.k = 0
      · rw [sstep_none_zero hk]
        exact hpop _
      · by_cases hm : F.m ≤ N
        · rw [sstep_none_push hk hm]
          exact hpush _ _ rfl (show F.k - 1 + 1 = F.k by omega)
            ⟨show F.k - 1 ≤ K by omega, hFu, hm, Nat.zero_le _⟩ ⟨hFk, hFu, hFv, hFm⟩
        · rw [sstep_none_fail hk hm]
          exact hpop _
    | some c =>
      by_cases hbad : F.k = 0 ∨ N < F.m
      · rw [sstep_some_bad hbad]
        exact hpop _
      · push_neg at hbad
        obtain ⟨hk, hm⟩ := hbad
        have hm' : ¬ N < F.m := by omega
        cases hph : F.ph
        · cases hc : c
          · rw [sstep_some_false_false hk hm' hph rfl]
            exact hrepl _ rfl ⟨hFk, hFu, hFv, show F.m + 1 ≤ N + 1 by omega⟩
          · rw [sstep_some_false_true hk hm' hph rfl]
            exact hpush _ _ rfl (show F.k - 1 + 1 = F.k by omega)
              ⟨show F.k - 1 ≤ K by omega, hm, hFv, Nat.zero_le _⟩ ⟨hFk, hFu, hFv, hFm⟩
        · cases hc : c
          · rw [sstep_some_true_false hk hm' hph rfl]
            exact hrepl _ rfl ⟨hFk, hFu, hFv, show F.m + 1 ≤ N + 1 by omega⟩
          · rw [sstep_some_true_true hk hm' hph rfl]
            exact hpop _

/-- The number of frames occurring in valid states. -/
abbrev FrameCode (N K : ℕ) : Type := Fin (N + 1) × Fin (N + 1) × Fin (K + 1) × Fin (N + 2) × Bool

/-- Encoding of a frame; injective on well formed frames. -/

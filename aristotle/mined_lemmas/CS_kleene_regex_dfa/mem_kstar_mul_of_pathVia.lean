import Mathlib

/-!
# From DFAs to regular expressions

This file implements Kleene's algorithm: given a DFA with finitely many states over a finite
alphabet, we construct a regular expression matching exactly the language it accepts.

The construction proceeds by recursion on a list `l` of "allowed intermediate states":
`kleeneRegex M l p q` matches exactly the words labelling a path from `p` to `q` all of whose
intermediate states belong to `l`.
-/

universe u v

open scoped Computability

namespace CS

variable {α : Type u} {σ : Type v}

/-! ### Paths with restricted intermediate states -/

/-- `PathVia M S p q w` means that reading `w` takes the DFA `M` from state `p` to state `q`,
in such a way that every *intermediate* state (i.e. every state visited strictly between the
start and the end of the run) lies in `S`. -/
inductive PathVia (M : DFA α σ) (S : Set σ) : σ → σ → List α → Prop
  | nil (p : σ) : PathVia M S p p []
  | cons {p q : σ} (a : α) {w : List α} (h : PathVia M S (M.step p a) q w)
      (hm : w ≠ [] → M.step p a ∈ S) : PathVia M S p q (a :: w)

/-- The language of words labelling paths from `p` to `q` with intermediate states in `S`. -/

theorem mem_kstar_mul_of_pathVia {M : DFA α σ} {S : Set σ} {s q : σ} :
    ∀ (w : List α), PathVia M (insert s S) s q w →
      w ∈ (pathLang M S s s)∗ * pathLang M S s q := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro h
    subst hn
    rcases PathVia.split_first h with hl | ⟨w₁, w₂, rfl, hw₁, hp, hq⟩
    · exact Language.append_mem_mul (Language.nil_mem_kstar _) hl
    · have hlt : w₂.length < (w₁ ++ w₂).length := by
        have : 0 < w₁.length := List.length_pos_iff.mpr hw₁
        simp only [List.length_append]
        omega
      obtain ⟨u, hu, v, hv, rfl⟩ :=
        Language.mem_mul.mp (ih w₂.length hlt w₂ rfl hq)
      refine ⟨w₁ ++ u, ?_, v, hv, by simp⟩
      rw [Language.mem_kstar] at hu ⊢
      obtain ⟨L, rfl, hL⟩ := hu
      refine ⟨w₁ :: L, by simp, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hp
      · exact hL z hz

/-- Kleene's decomposition: paths that may additionally pass through `s` are obtained from
paths avoiding `s` by splitting at the first and last visits to `s`. -/

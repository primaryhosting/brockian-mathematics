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

theorem leftQuotient_kstar (A : Language α) (a : α) :
    (A∗).leftQuotient [a] = A.leftQuotient [a] * A∗ := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_mul]
  constructor
  · intro h
    rw [Language.kstar_def_nonempty] at h
    obtain ⟨L, hL, hmem⟩ := h
    cases L with
    | nil => simp at hL
    | cons w L =>
        obtain ⟨hw, hwne⟩ := hmem w (by simp)
        cases w with
        | nil => exact absurd rfl hwne
        | cons b w =>
            simp only [List.flatten_cons, List.cons_append] at hL
            obtain ⟨rfl, hy⟩ : b = a ∧ w ++ L.flatten = y := by simpa using hL.symm
            refine ⟨w, by rw [Language.mem_leftQuotient]; exact hw, L.flatten, ?_, hy⟩
            exact Language.join_mem_kstar (fun z hz => (hmem z (by simp [hz])).1)
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_leftQuotient] at hu
    rw [Language.mem_kstar] at hv ⊢
    obtain ⟨L, rfl, hL⟩ := hv
    refine ⟨(a :: u) :: L, by simp, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hu
    · exact hL z hz

/-! ### Finite derivative families -/

/-- A family `F` of languages is *derivative closed* if it is closed under taking the left
quotient by a single letter. -/

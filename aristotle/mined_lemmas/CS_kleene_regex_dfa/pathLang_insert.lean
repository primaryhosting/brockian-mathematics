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

theorem pathLang_insert (M : DFA α σ) (S : Set σ) (s p q : σ) :
    pathLang M (insert s S) p q =
      pathLang M S p q + pathLang M S p s * (pathLang M S s s)∗ * pathLang M S s q := by
  ext w
  rw [Language.mem_add]
  constructor
  · intro h
    rcases PathVia.split_first (mem_pathLang.mp h) with hl | ⟨w₁, w₂, rfl, _, hp, hq⟩
    · exact Or.inl hl
    · right
      obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp (mem_kstar_mul_of_pathVia w₂ hq)
      rw [mul_assoc]
      exact Language.append_mem_mul hp (Language.append_mem_mul hu hv)
  · rintro (h | h)
    · exact (mem_pathLang.mp h).mono (Set.subset_insert s S)
    · rw [mul_assoc] at h
      obtain ⟨w₁, h₁, x, hx, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hx
      have h₁' : PathVia M (insert s S) p s w₁ :=
        (mem_pathLang.mp h₁).mono (Set.subset_insert s S)
      have hu' : PathVia M (insert s S) s s u := PathVia.of_mem_kstar hu
      have hv' : PathVia M (insert s S) s q v :=
        (mem_pathLang.mp hv).mono (Set.subset_insert s S)
      exact h₁'.append (Set.mem_insert s S) (hu'.append (Set.mem_insert s S) hv')


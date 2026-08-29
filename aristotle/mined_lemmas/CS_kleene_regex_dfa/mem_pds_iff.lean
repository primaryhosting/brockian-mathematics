/-
Antimirov partial derivatives: every language matched by a regular expression is regular
(i.e. accepted by a DFA with finitely many states).
-/
import Mathlib

namespace CS

open RegularExpression Language Computability

universe u
variable {α : Type u}

/-! ### Membership lemmas for languages -/


theorem mem_pds_iff (x : List α) (P : RegularExpression α) (y : List α) :
    (∃ p ∈ pds P x, y ∈ p.matches') ↔ x ++ y ∈ P.matches' := by
  induction x generalizing P with
  | nil =>
      constructor
      · rintro ⟨p, hp, hy⟩
        rw [pds_nil, Set.mem_singleton_iff] at hp
        subst hp
        simpa using hy
      · intro hy
        exact ⟨P, by simp, by simpa using hy⟩
  | cons a x ih =>
      rw [pds_cons]
      rw [show (a :: x) ++ y = a :: (x ++ y) from rfl, ← mem_pd_iff P a (x ++ y)]
      constructor
      · rintro ⟨p, hp, hy⟩
        rw [Set.mem_iUnion₂] at hp
        obtain ⟨q, hq, hp⟩ := hp
        exact ⟨q, hq, (ih q).1 ⟨p, hp, hy⟩⟩
      · rintro ⟨q, hq, hy⟩
        obtain ⟨p, hp, hy⟩ := (ih q).2 hy
        exact ⟨p, Set.mem_iUnion₂.2 ⟨q, hq, hp⟩, hy⟩

/-! ### Finiteness -/

/-- An over-approximation of the set of all partial derivatives of a regular expression. -/

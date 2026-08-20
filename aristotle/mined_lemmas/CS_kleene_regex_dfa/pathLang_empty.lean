import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/

theorem pathLang_empty [Fintype α] [DecidableEq σ] (i j : σ) :
    pathLang M ∅ i j =
      (if i = j then 1 else 0) +
        ∑ a ∈ Finset.univ.filter (fun a : α => M.step i a = j), ({[a]} : Language α) := by
  ext w
  rw [Language.mem_add, mem_finset_sum]
  constructor
  · rintro ⟨hw, hint⟩
    match w with
    | [] =>
      left
      simp only [DFA.evalFrom_nil] at hw
      rw [if_pos hw]
      rfl
    | [a] =>
      right
      exact ⟨a, by simpa using hw, rfl⟩
    | a :: b :: t =>
      exact absurd (hint [a] (b :: t) rfl (by simp) (by simp)) (by simp)
  · rintro (h | ⟨a, ha, rfl⟩)
    · by_cases hij : i = j
      · rw [if_pos hij] at h
        rw [Language.mem_one] at h
        subst h
        subst hij
        exact nil_mem_pathLang M ∅ i
      · rw [if_neg hij] at h
        exact absurd h (by simp)
    · simp only [Finset.mem_filter] at ha
      refine ⟨by simpa using ha.2, ?_⟩
      intro u v huv hu hv
      exfalso
      have hlen : u.length + v.length = 1 := by
        rw [← List.length_append, huv]; simp
      have hu1 : 0 < u.length := by
        cases u with
        | nil => exact absurd rfl hu
        | cons _ _ => simp
      have hv1 : 0 < v.length := by
        cases v with
        | nil => exact absurd rfl hv
        | cons _ _ => simp
      omega


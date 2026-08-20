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

theorem kstar_le_pathLang {T : Finset σ} {k : σ} (hk : k ∈ T) {L : Language α}
    (hL : L ≤ pathLang M T k k) : L∗ ≤ pathLang M T k k := by
  rintro w hw
  rw [Language.mem_kstar] at hw
  obtain ⟨ls, rfl, hls⟩ := hw
  induction ls with
  | nil => simpa using nil_mem_pathLang M T k
  | cons x xs ih =>
    have hx : x ∈ pathLang M T k k := hL (hls x (by simp))
    have hxs : xs.flatten ∈ pathLang M T k k := ih fun y hy => hls y (by simp [hy])
    have : x ++ xs.flatten ∈ pathLang M T k k :=
      pathLang_splice M hk ⟨x, hx, xs.flatten, hxs, rfl⟩
    simpa using this


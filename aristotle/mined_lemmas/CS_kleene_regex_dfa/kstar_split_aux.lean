import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-! ## Part 1: the language of a regular expression is accepted by a finite DFA

We use the Myhill–Nerode theorem: it suffices to show that a regular expression has only
finitely many left quotients (Brzozowski derivatives, viewed as languages). -/

section RegexToDFA

variable {α : Type u}


theorem kstar_split_aux {L : Language α} : ∀ ws : List (List α), (∀ w ∈ ws, w ∈ L) →
    ∀ x y : List α, x ≠ [] → x ++ y = ws.flatten →
    ∃ u v y₁ y₂, x = u ++ v ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ y₁ ∈ L ∧ y = y₁ ++ y₂ ∧ y₂ ∈ L∗ := by
  intro ws
  induction ws with
  | nil =>
    intro _ x y hx hflat
    simp only [List.flatten_nil, List.append_eq_nil_iff] at hflat
    exact absurd hflat.1 hx
  | cons w ws ih =>
    intro hws x y hx hflat
    rw [List.flatten_cons] at hflat
    have hw : w ∈ L := hws w (by simp)
    have hws' : ∀ z ∈ ws, z ∈ L := fun z hz => hws z (by simp [hz])
    have hstar : ws.flatten ∈ L∗ := Language.join_mem_kstar hws'
    rcases List.append_eq_append_iff.1 hflat with ⟨a', hw', rfl⟩ | ⟨c', rfl, hflat'⟩
    · exact ⟨[], x, a', ws.flatten, by simp, hx, Language.nil_mem_kstar _, hw' ▸ hw, rfl, hstar⟩
    · rcases eq_or_ne c' [] with rfl | hc'
      · refine ⟨[], w, [], y, by simp, by simpa using hx, Language.nil_mem_kstar _,
          by simpa using hw, by simp, ?_⟩
        simp only [List.nil_append] at hflat'
        exact hflat' ▸ hstar
      · obtain ⟨u, v, y₁, y₂, h1, h2, h3, h4, h5, h6⟩ := ih hws' c' y hc' hflat'.symm
        exact ⟨w ++ u, v, y₁, y₂, by rw [h1, List.append_assoc], h2,
          mul_kstar_le_kstar (a := L) ⟨w, hw, u, h3, rfl⟩, h4, h5, h6⟩

/-- If `x ≠ []` and `x ++ y ∈ L∗`, then the star decomposition of `x ++ y` can be cut at the
factor that contains the end of `x`. -/

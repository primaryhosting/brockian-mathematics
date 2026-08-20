import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier
namespace GaleStewart

variable {A : Type*} [Inhabited A]

/-- The initial segment of a play `f` of length `n`, padded with `default`. -/

lemma exists_good_of_acc {c : ℕ → (ℕ → A) → A} (τ : ℕ → (ℕ → A) → A) :
    ∀ p : ℕ × (ℕ → A), Acc (Succ W c) p →
      ∀ n : ℕ, p = (n, trunc (play c τ) n) → ∃ m, Good W m (trunc (play c τ) m) := by
  intro p hacc
  induction hacc with
  | intro x _ ih =>
    intro n hn
    by_cases hg : Good W n (trunc (play c τ) n)
    · exact ⟨n, hg⟩
    · refine ih (n + 1, trunc (play c τ) (n + 1)) ?_ (n + 1) rfl
      subst hn
      refine ⟨hg, rfl, ?_⟩
      simp only
      by_cases he : Even n
      · rw [if_pos he, trunc_succ]
        congr 1
        rw [play_eq, if_pos he]
      · rw [if_neg he]
        exact ⟨play c τ n, trunc_succ _ _⟩

/-- Openness of the payoff set: any play in `W` has a finite initial segment all of whose
extensions lie in `W`. -/

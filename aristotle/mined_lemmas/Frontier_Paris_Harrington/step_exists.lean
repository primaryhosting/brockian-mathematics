/-
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 rejects a `/-!` module docstring before `import`, so the header
-- above is a plain block comment; it is repeated verbatim as a module docstring
-- immediately after the imports.)
import RequestProject.Ramsey

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

/-- A finite set of natural numbers is *relatively large* (in the sense of
Paris–Harrington) if it is nonempty and its cardinality is at least its least
element. -/

theorem step_exists {k n : ℕ}
    (IH : ∀ (c : Finset ℕ → Fin k) (S : Set ℕ), S.Infinite →
      ∃ A ⊆ S, A.Infinite ∧ HomogOn n c A)
    (c : Finset ℕ → Fin k) (T : Set ℕ) (hT : T.Infinite) :
    ∃ (a : ℕ) (T' : Set ℕ) (j : Fin k), a ∈ T ∧ T' ⊆ T ∧ T'.Infinite ∧
      (∀ x ∈ T', a < x) ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ T' → s.card = n → c (insert a s) = j := by
  obtain ⟨a, ha⟩ := hT.nonempty
  have hTa : (T ∩ Set.Ioi a).Infinite := by
    refine Set.Infinite.mono ?_ (hT.diff (Set.finite_Iic a))
    intro x hx
    exact ⟨hx.1, by simpa using hx.2⟩
  obtain ⟨A, hAsub, hAinf, hAhom⟩ := IH (fun s => c (insert a s)) (T ∩ Set.Ioi a) hTa
  obtain ⟨s₀, hs₀sub, hs₀card⟩ := hAinf.exists_subset_card_eq n
  refine ⟨a, A, c (insert a s₀), ha, fun x hx => (hAsub hx).1, hAinf,
    fun x hx => (hAsub hx).2, ?_⟩
  intro s hs hcard
  exact hAhom s s₀ hs hs₀sub hcard hs₀card

/-- **Infinite Ramsey theorem**: any colouring of the `n`-element subsets of `ℕ`
with `k` colours is constant on the `n`-element subsets of some infinite subset of
any given infinite set. -/

import Mathlib

/-!
# Borel Determinacy
Category: Frontier — Set Theory
Target: Frontier.Borel_determinacy
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

set_option grind.warning false

namespace Frontier

/-! ## Infinite games: positions, strategies, winning strategies

We consider infinite two-player games with perfect information played on an alphabet `X`.
A *play* is a sequence `x : ℕ → X`; the move at time `n` is `x n`.  Which player moves at
time `n` is recorded by a predicate `turn : ℕ → Prop` (the *turn set* of the player under
consideration).  In the classical game `G(A)` on Baire space, player I moves at the even
times and player II at the odd times, and player I wins the play `x` iff `x ∈ A`.
-/

variable {X : Type*}

/-- The position reached after the first `n` moves of the play `x`. -/

lemma cylClosed_of_isClosed [TopologicalSpace X] {A : Set (ℕ → X)} (hA : IsClosed A) :
    CylClosed A := by
  intro x hx
  have hopen : IsOpen Aᶜ := hA.isOpen_compl
  rw [isOpen_pi_iff] at hopen
  obtain ⟨I, u, hu, hsub⟩ := hopen x hx
  refine ⟨(I.sup id) + 1, ?_⟩
  intro y hy
  have hyx : ∀ i, i < (I.sup id) + 1 → y i = x i := by
    intro i hi
    have := hy.eq_of_lt (i := i) (by simpa using hi)
    rw [← this, pre_getElem]
  have : y ∈ (I : Set ℕ).pi u := by
    intro i hi
    have hle : i ≤ I.sup id := Finset.le_sup (f := id) (by simpa using hi)
    rw [hyx i (by omega)]
    exact (hu i (by simpa using hi)).2
  exact hsub this

/-- A play passes through `p` exactly when it agrees with `p` on the first `p.length`
coordinates. -/

import Mathlib

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

/-
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/

theorem step_local (N s t : ℕ) (adj₁ adj₂ : ℕ → ℕ → Bool) (x y : Cfg)
    (h : adj₁ (query x y).1 (query x y).2 = adj₂ (query x y).1 (query x y).2) :
    Step N adj₁ s t x y ↔ Step N adj₂ s t x y := by
  have key : ∀ (e₁ e₂ : ℕ → ℕ → Bool), e₁ (query x y).1 (query x y).2 =
      e₂ (query x y).1 (query x y).2 → Step N e₁ s t x y → Step N e₂ s t x y := by
    intro e₁ e₂ he hstep
    cases hstep with
    | startA hv => exact Step.startA hv
    | stepA hadj hp' hl =>
        simp only [query] at he
        exact Step.stepA (by rw [← he]; exact hadj) hp' hl
    | doneA hpv => exact Step.doneA hpv
    | startI hv => exact Step.startI hv
    | startB hdc hlb hu => exact Step.startB hdc hlb hu
    | stepB hadj hp' hl =>
        simp only [query] at he
        exact Step.stepB (by rw [← he]; exact hadj) hp' hl
    | doneB hpu huv hadj =>
        simp only [query] at he
        exact Step.doneB hpu huv (by rw [← he]; exact hadj)
    | doneI hdc hiN => exact Step.doneI hdc hiN
    | nextRound hi => exact Step.nextRound hi
    | lastRound => exact Step.lastRound
    | accept hdc => exact Step.accept hdc
  exact ⟨key adj₁ adj₂ h, key adj₂ adj₁ h.symm⟩

end IS

/-!
## `NL = coNL`

A nondeterministic machine running in space `S` on a fixed input has a *configuration graph*:
a finite digraph whose vertices are the (at most `2^{O(S)}`) configurations, with an edge
`x → y` when the machine can pass from `x` to `y` in one step.  The machine accepts iff the
accepting configuration is reachable from the initial one in this graph.

`CS.immerman_szelepcsenyi` below states that the *complement* of such an acceptance condition
is again of exactly the same form: for any finite configuration type `C`, any transition
relation `step`, and any two configurations `a b : C`, non-reachability of `b` from `a` is
equivalent to reachability of an accepting configuration in the configuration graph of the
explicitly constructed machine `IS.Step`, which is uniform in `step` and has only
`5 * (Fintype.card C + 2) ^ 8` reachable configurations (`CS.immerman_szelepcsenyi_space`),
i.e. runs in space `O(S)`.  This is Immerman–Szelepcsényi: `NL = coNL`, and more generally
`NSPACE(S) = coNSPACE(S)` for `S ≥ log`.
-/

open IS

variable {C : Type*} [Fintype C]

/-- An indexing of the configurations of a machine by `{0, …, card C - 1}`. -/

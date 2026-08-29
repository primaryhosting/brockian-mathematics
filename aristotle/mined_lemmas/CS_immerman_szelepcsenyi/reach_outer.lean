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

theorem reach_outer (hs : s < N) {t i c : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (hc : c = (R N adj s (i - 1)).card) :
    ∀ v ≤ N, Relation.ReflTransGen (Step N adj s t)
      (.outer i c 0 0) (.outer i c v (((R N adj s i).filter (fun x => x < v)).card)) := by
  intro v
  induction v with
  | zero => intro _; simpa using Relation.ReflTransGen.refl
  | succ v ih =>
      intro hv
      have hvN : v < N := by omega
      have hprev := ih (by omega)
      set k := ((R N adj s i).filter (fun x => x < v)).card with hk
      by_cases hmem : v ∈ R N adj s i
      · obtain ⟨l', hl', hreach⟩ := reach_pathA (t := t) (i := i) (c := c) (v := v) (k := k)
          i (le_refl _) v hmem
        have h1 : Step N adj s t (.outer i c v k) (.pathA i c v k s 0) := Step.startA hvN
        have h2 : Step N adj s t (.pathA i c v k v l') (.outer i c (v + 1) (k + 1)) :=
          Step.doneA rfl
        have : Relation.ReflTransGen (Step N adj s t) (.outer i c 0 0) (.outer i c (v+1) (k+1)) :=
          ((hprev.tail h1).trans hreach).tail h2
        rwa [filter_lt_succ_of_mem hmem]
      · have hcheck : ∀ w ∈ R N adj s (i - 1), w ≠ v ∧ adj w v = false := by
          intro w hw
          constructor
          · rintro rfl
            exact hmem (R_mono (by omega) hw)
          · by_contra hcon
            simp only [Bool.not_eq_false] at hcon
            have : v ∈ R N adj s (i - 1 + 1) := mem_R_succ_of_edge hw hvN hcon
            rw [show i - 1 + 1 = i by omega] at this
            exact hmem this
        obtain ⟨lb', hinner⟩ := reach_inner hs (t := t) (v := v) (k := k) hc hcheck
          ((R N adj s (i - 1)).card) 0 0 (by simp) (by omega)
        have h1 : Step N adj s t (.outer i c v k) (.inner i c v k 0 0) := Step.startI hvN
        have h2 : Step N adj s t (.inner i c v k c lb') (.outer i c (v + 1) k) :=
          Step.doneI rfl hiN
        have : Relation.ReflTransGen (Step N adj s t) (.outer i c 0 0) (.outer i c (v+1) k) :=
          ((hprev.tail h1).trans hinner).tail h2
        rwa [filter_lt_succ_of_not_mem hmem]

/-- The machine reaches the beginning of round `i`, with the correct count `|R (i-1)|`. -/

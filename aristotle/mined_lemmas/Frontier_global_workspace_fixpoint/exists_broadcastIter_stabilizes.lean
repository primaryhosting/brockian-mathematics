import Mathlib
/-!
# Global Workspace Fixpoint
Category: Frontier Mind
Target: Frontier.global_workspace_fixpoint
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

/-- The set of *global-workspace states* that are fixed by a broadcast operator `f`:
states in which one further round of broadcasting changes nothing. -/

lemma exists_broadcastIter_stabilizes {α : Type*} [Fintype α] [CompleteLattice α] (f : α →o α) :
    ∃ n ≤ Fintype.card α, broadcastIter f (n + 1) = broadcastIter f n := by
  by_contra h
  push_neg at h
  -- Then the chain is strictly increasing on `Fin (card α + 1)`, contradicting finiteness.
  have hstrict : StrictMonoOn (broadcastIter f) (Set.Iic (Fintype.card α)) := by
    have hstep : ∀ n < Fintype.card α, broadcastIter f n < broadcastIter f (n + 1) := by
      intro n hn
      exact lt_of_le_of_ne (broadcastIter_monotone f (Nat.le_succ n))
        (fun hEq => h n hn.le hEq.symm)
    intro a ha b hb hab
    have : ∀ k, ∀ m, m + k ≤ Fintype.card α → 0 < k →
        broadcastIter f m < broadcastIter f (m + k) := by
      intro k
      induction k with
      | zero => omega
      | succ k ih =>
          intro m hm _
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; exact hstep m (by omega)
          · have h1 : broadcastIter f m < broadcastIter f (m + k) := ih m (by omega) hk
            have h2 : broadcastIter f (m + k) < broadcastIter f (m + k + 1) :=
              hstep (m + k) (by omega)
            calc broadcastIter f m < broadcastIter f (m + k) := h1
              _ < broadcastIter f (m + k + 1) := h2
              _ = broadcastIter f (m + (k + 1)) := by ring_nf
    have hb' : b ≤ Fintype.card α := hb
    have := this (b - a) a (by omega) (by omega)
    simpa [Nat.add_sub_cancel' hab.le] using this
  have hinj : Function.Injective (fun i : Fin (Fintype.card α + 1) => broadcastIter f i) := by
    intro i j hij
    have hi : (i : ℕ) ∈ Set.Iic (Fintype.card α) := by
      have := i.isLt; simp only [Set.mem_Iic]; omega
    have hj : (j : ℕ) ∈ Set.Iic (Fintype.card α) := by
      have := j.isLt; simp only [Set.mem_Iic]; omega
    exact Fin.ext (hstrict.injOn hi hj hij)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

/-- **Global workspace fixpoint theorem** (Knaster–Tarski, finite version).

For a monotone *broadcast* operator `f` on a finite state lattice `α`, the least fixed point
`OrderHom.lfp f` exists — it is the least element of the set of fixed points of `f`
(Mathlib: `OrderHom.isLeast_lfp`) — and moreover it is *reached* by finitely many broadcast
rounds starting from the empty workspace `⊥`: there is some `n ≤ Fintype.card α` at which the
iteration stabilizes, `f^[n] ⊥ = f^[n+1] ⊥`, and this stable state is exactly the least
fixed point. -/

/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ## Machine model

We work with a *non-uniform* space-bounded machine model.  A machine works on inputs of one
fixed length; a language belongs to a space class if for every input length there is a machine
of the appropriate size deciding the language on inputs of that length.

A machine is described by its set of configurations `Cfg` (which is the whole memory of the
machine: the space used is `log₂ (card Cfg)`), a designated start configuration, a function
`head` telling which position of the (read-only) input is currently scanned, and a transition
which may depend on the current configuration and on the single input bit that is being read.
Note that the machine has *no* other access to the input, which is what makes the space measure
meaningful. -/

/-- The `i`-th bit of an input word; `false` beyond the end of the word. -/

theorem savitch {L : Set (List Bool)} {f : ℕ → ℕ} (hL : L ∈ NSPACE f) :
    L ∈ DSPACE (fun n => 16 * (f n + 1) ^ 2) := by
  intro n
  obtain ⟨M, hcard, hML⟩ := hL n
  have hA : NN M ≤ 2 ^ (f n + 1) := by
    have h1 : NN M = Fintype.card M.Cfg + 1 := by simp [NN]
    have h2 : 1 ≤ 2 ^ f n := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (f n + 1) = 2 ^ f n + 2 ^ f n := by ring
    omega
  refine ⟨savDSM M (f n + 1), ?_, ?_⟩
  · have h1 : Fintype.card (savDSM M (f n + 1)).Cfg = Fintype.card (SavCfg M (f n + 1)) := rfl
    rw [h1]
    calc Fintype.card (SavCfg M (f n + 1))
        ≤ 2 ^ ((3 * (f n + 1) + 3) * ((f n + 1) + 1) + 1) := card_savCfg_le M (f n + 1) hA
      _ ≤ 2 ^ (16 * (f n + 1) ^ 2) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          nlinarith [sq_nonneg (f n)]
  · intro x hx
    refine ⟨RkB (M.E' x) (f n + 1) (some M.start) none, sav_outputs M (f n + 1) x, ?_⟩
    rw [RkB_iff_accepts M (f n + 1) hA x]
    exact (hML x hx).symm

end SavitchMain

end CS

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


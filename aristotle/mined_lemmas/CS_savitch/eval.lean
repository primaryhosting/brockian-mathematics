/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

theorem eval (n : ℕ) : ∀ (k : ℕ) (todo : List N.Mem) (a b : N.Mem) (st : List (Frame N.Mem)),
    SReach N S g x (.call n todo a b k st) (.ret n todo (decide (CY N S x n k a b)) st) := by
  intro k
  induction k with
  | zero =>
    intro todo a b st
    have hval : (decide (CY N S x n 0 a b)) = decide (a = b ∨ stepR N x a b) :=
      decide_eq_decide.mpr Iff.rfl
    rw [hval]
    exact SReach.one' dstep_call_zero
  | succ k ihk =>
    intro todo a b st
    cases hc : cands N S n with
    | nil =>
      have hval : (decide (CY N S x n (k + 1) a b)) = false := by
        refine decide_eq_false ?_
        rintro ⟨mm, hmm, -⟩
        rw [hc] at hmm
        exact absurd hmm (List.not_mem_nil)
      rw [hval]
      exact SReach.one' (dstep_call_succ_nil hc)
    | cons m ms =>
      have s1 : SReach N S g x (.call n todo a b (k + 1) st)
          (.call n todo a m k (⟨a, b, k, m, ms, false⟩ :: st)) :=
        SReach.one' (dstep_call_succ_cons hc)
      have s2 := loop_eval ihk ms todo a b m st
      have hiff : CY N S x n (k + 1) a b ↔
          (∃ mm ∈ m :: ms, CY N S x n k a mm ∧ CY N S x n k mm b) := by
        rw [CY, hc]
      rw [decide_eq_decide.mpr hiff]
      exact s1.trans' s2

/-! ### The outer loop and the scanning phase -/


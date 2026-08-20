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

theorem outer_reject {n : ℕ} :
    ∀ (todo : List N.Mem), (∀ b ∈ todo, ¬ (N.acc b ∧ CY N S x n (g n) N.start b)) →
      ∀ t, (dstep N S g x)^[t] (.outer n todo) ≠ .acc := by
  intro todo
  induction todo with
  | nil =>
    intro _ t
    rw [Function.iterate_fixed dstep_outer_nil t]
    simp
  | cons b bs ih =>
    intro hno t
    have hbs : ∀ b' ∈ bs, ¬ (N.acc b' ∧ CY N S x n (g n) N.start b') := fun b' hb' =>
      hno b' (List.mem_cons_of_mem _ hb')
    by_cases hb : N.acc b
    · have hcy : ¬ CY N S x n (g n) N.start b := fun h => hno b List.mem_cons_self ⟨hb, h⟩
      obtain ⟨t0, ht0⟩ := eval (N := N) (S := S) (g := g) (x := x) n (g n) bs N.start b []
      rw [decide_eq_false hcy] at ht0
      have e1 : (dstep N S g x)^[1] (SMem.outer n (b :: bs))
          = .call n bs N.start b (g n) [] := by
        simpa using dstep_outer_cons_acc (S := S) (g := g) (x := x) hb
      have e2 : (dstep N S g x)^[1 + t0] (SMem.call n bs N.start b (g n) [])
          = .outer n bs := by
        rw [Function.iterate_add_apply, ht0]
        simpa using dstep_ret_nil_false (N := N) (S := S) (g := g) (x := x) (n := n) (todo := bs)
      have hstep : (dstep N S g x)^[(1 + t0) + 1] (SMem.outer n (b :: bs)) = .outer n bs := by
        rw [Function.iterate_add_apply, e1, e2]
      rcases Nat.lt_or_ge t ((1 + t0) + 1) with hlt | hge
      · intro hcon
        have hacc := iter_acc_mono hcon (le_of_lt hlt)
        rw [hstep] at hacc
        simp at hacc
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
        have hcomm : (1 + t0) + 1 + d = d + ((1 + t0) + 1) := by omega
        rw [hcomm, Function.iterate_add_apply, hstep]
        exact ih hbs d
    · cases t with
      | zero => simp
      | succ t =>
        rw [Function.iterate_succ_apply, dstep_outer_cons_not_acc hb]
        exact ih hbs t


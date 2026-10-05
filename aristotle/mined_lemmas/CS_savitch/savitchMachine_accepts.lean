/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a module docstring: Lean 4 requires `import` lines to come
first, so the very first comment of the file cannot be a module docstring.)

This file develops space bounded machines, proves Savitch's theorem
`NSPACE f ⊆ DSPACE (f ^ 2)` and deduces `PSPACE = NPSPACE`.
-/

set_option autoImplicit false

namespace CS

/-! ## Languages -/

/-- A language is a predicate on binary strings. -/
abbrev Language := List Bool → Prop

/-- The bit of `x` at position `i` (`false` beyond the end of `x`). -/

theorem savitchMachine_accepts (M : NMachine) (s : ℕ → ℕ) (x : List Bool)
    (hs : M.size x.length ≤ 2 ^ s x.length) :
    (savitchMachine M s).Accepts x ↔ M.Accepts x := by
  have hiter : ∀ t : ℕ,
      (((savitchMachine M s).next x)^[t] ((savitchMachine M s).init x.length)).1
        = (srun (M.size x.length) (M.edgeAll x.length) (M.ipos x.length) (bitAt x))^[t]
            (none, [⟨M.init x.length, M.size x.length, s x.length + 1, 0, false⟩]) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hK : M.size x.length + 1 ≤ 2 ^ (s x.length + 1) := by
    have h1 : (1 : ℕ) ≤ 2 ^ s x.length := Nat.one_le_two_pow
    have h2 : 2 ^ (s x.length + 1) = 2 ^ (s x.length) + 2 ^ (s x.length) := by
      rw [pow_succ]; ring
    omega
  have hE := M.edgeAll_le x.length (M.ipos x.length) (bitAt x)
  rw [M.accepts_iff_steps x hK,
    ← sim_accepts hE (M.init x.length) (M.size x.length) (s x.length + 1)
      (M.init_lt x.length).le le_rfl]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hiter t]
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    show (((savitchMachine M s).next x)^[t] ((savitchMachine M s).init x.length)).1
      = (some true, [])
    rw [hiter t]
    exact ht

/-- **Savitch's theorem**: nondeterministic space `f` is contained in deterministic space
`f ^ 2`. -/

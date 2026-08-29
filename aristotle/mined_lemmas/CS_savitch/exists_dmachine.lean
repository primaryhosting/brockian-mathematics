import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem exists_dmachine {s : ℕ} {C : Type} [Fintype C] (hcard : Fintype.card C ≤ 2 ^ s)
    (F : C → C) (c₀ : C) (P : C → Bool) :
    ∃ D : DMachine s, (∀ t, D.acc (D.run t) = P (F^[t] c₀)) ∧
      (∀ t, D.step (D.run t) = D.run t ↔ F (F^[t] c₀) = F^[t] c₀) := by
  classical
  let e := Fintype.equivFin C
  refine ⟨{ size := Fintype.card C
            hsize := hcard
            step := fun i => e (F (e.symm i))
            start := e c₀
            acc := fun i => P (e.symm i) }, ?_, ?_⟩
  · intro t
    show P (e.symm ((fun i => e (F (e.symm i)))^[t] (e c₀))) = P (F^[t] c₀)
    rw [iterate_conj e F t c₀, Equiv.symm_apply_apply]
  · intro t
    show (fun i => e (F (e.symm i))) ((fun i => e (F (e.symm i)))^[t] (e c₀))
        = (fun i => e (F (e.symm i)))^[t] (e c₀) ↔ _
    rw [iterate_conj e F t c₀]
    simp only [Equiv.symm_apply_apply]
    exact ⟨fun h => e.injective h, fun h => congrArg e h⟩

/-! ### Savitch's theorem for a single machine -/

/-- Savitch's simulation: a nondeterministic machine of space `s` is simulated by a
halting deterministic machine of space `9 * (s + 1) ^ 2`. -/

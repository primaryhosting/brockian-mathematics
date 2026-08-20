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

theorem scanIter_bound (x : List Bool) (t : ℕ) :
    (scanStep x)^[t] (some 0) = none ∨
      ∃ i ≤ x.length, (scanStep x)^[t] (some 0) = some i := by
  induction t with
  | zero => exact Or.inr ⟨0, Nat.zero_le _, rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | ⟨i, hi, h⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]
      cases hx : x[i]? with
      | none => exact Or.inr ⟨i, hi, by simp [scanStep, hx]⟩
      | some b =>
        cases b with
        | true => exact Or.inl (by simp [scanStep, hx])
        | false =>
          have hlt : i < x.length := by
            by_contra hc
            push_neg at hc
            rw [List.getElem?_eq_none hc] at hx
            simp at hx
          exact Or.inr ⟨i + 1, by omega, by simp [scanStep, hx]⟩


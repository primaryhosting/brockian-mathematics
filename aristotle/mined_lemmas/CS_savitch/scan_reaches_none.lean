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

theorem scan_reaches_none (x : List Bool) :
    ∀ (d i : ℕ), x[i + d]? = some true → ∃ t, (scanStep x)^[t] (some i) = none := by
  intro d
  induction d with
  | zero =>
    intro i hx
    exact ⟨1, by simp [scanStep, (by simpa using hx : x[i]? = some true)]⟩
  | succ d ih =>
    intro i hx
    cases hxi : x[i]? with
    | none =>
      have hle : x.length ≤ i := by
        by_contra hc
        push_neg at hc
        rw [List.getElem?_eq_getElem hc] at hxi
        simp at hxi
      rw [List.getElem?_eq_none (by omega)] at hx
      simp at hx
    | some b =>
      cases b with
      | true => exact ⟨1, by simp [scanStep, hxi]⟩
      | false =>
        have hx' : x[(i + 1) + d]? = some true := by
          have : (i + 1) + d = i + (d + 1) := by omega
          rw [this]; exact hx
        obtain ⟨t, ht⟩ := ih (i + 1) hx'
        refine ⟨t + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        have : scanStep x (some i) = some (i + 1) := by simp [scanStep, hxi]
        rw [this, ht]


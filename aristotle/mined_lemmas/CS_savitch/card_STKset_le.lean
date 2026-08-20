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

theorem card_STKset_le {n : ℕ} (hS : (S n).card ≤ 2 ^ g n) :
    (STKset N S g n).card ≤ 2 ^ (5 * g n * g n + 6 * g n) := by
  have hFF := card_FFset_le (N := N) (S := S) (g := g) (n := n) hS
  have h1 : (STKset N S g n).card ≤ ((FFset N S g n).card + 1) ^ g n :=
    card_listsLE _ _
  have h2 : (FFset N S g n).card + 1 ≤ 2 ^ (5 * g n + 6) := by
    have : 2 ^ (5 * g n + 6) = 2 ^ (5 * g n + 5) + 2 ^ (5 * g n + 5) := by ring
    have h3 : (1 : ℕ) ≤ 2 ^ (5 * g n + 5) := Nat.one_le_two_pow
    omega
  have h4 : ((FFset N S g n).card + 1) ^ g n ≤ (2 ^ (5 * g n + 6)) ^ g n :=
    Nat.pow_le_pow_left h2 _
  have h5 : (2 ^ (5 * g n + 6)) ^ g n = 2 ^ (5 * g n * g n + 6 * g n) := by
    rw [← pow_mul]
    congr 1
    ring
  omega


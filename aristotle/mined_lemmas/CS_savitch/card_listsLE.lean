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

theorem card_listsLE {β : Type} (A : Finset β) :
    ∀ k, (listsLE k A).card ≤ (A.card + 1) ^ k := by
  intro k
  induction k with
  | zero => simp [listsLE]
  | succ k ih =>
    have h1 : (listsLE (k + 1) A).card
        ≤ ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card + 1 := by
      rw [listsLE]
      exact Finset.card_insert_le _ _
    have h2 : ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card
        ≤ A.card * (listsLE k A).card := by
      calc ((A ×ˢ listsLE k A).image (fun p => p.1 :: p.2)).card
          ≤ (A ×ˢ listsLE k A).card := Finset.card_image_le
        _ = A.card * (listsLE k A).card := Finset.card_product _ _
    have h3 : (1 : ℕ) ≤ (A.card + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    have h4 : A.card * (listsLE k A).card ≤ A.card * (A.card + 1) ^ k :=
      Nat.mul_le_mul_left _ ih
    have : (A.card + 1) ^ (k + 1) = A.card * (A.card + 1) ^ k + (A.card + 1) ^ k := by
      ring
    omega

/-! ### The invariant -/

variable (N : Machine) (S : ℕ → Finset N.Mem) (g : ℕ → ℕ)

/-- Configurations that can occur as endpoints of subproblems. -/

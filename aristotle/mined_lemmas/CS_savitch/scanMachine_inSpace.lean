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

theorem scanMachine_inSpace : InSpace scanMachine (fun n => 1 * (n + 1) ^ 1 + 1) := by
  refine ⟨fun n => insert none ((Finset.range (n + 1)).image some), ?_, ?_⟩
  · intro x m hm
    obtain ⟨t, ht⟩ := (scanReach_iff x m).mp hm
    rcases scanIter_bound x t with h | ⟨i, hi, h⟩
    · rw [← ht, h]; exact Finset.mem_insert_self _ _
    · rw [← ht, h]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (show i < x.length + 1 by omega), rfl⟩)
  · intro n
    have h1 : (insert none ((Finset.range (n + 1)).image (some : ℕ → Option ℕ))).card
        ≤ ((Finset.range (n + 1)).image (some : ℕ → Option ℕ)).card + 1 :=
      Finset.card_insert_le _ _
    have h2 : ((Finset.range (n + 1)).image (some : ℕ → Option ℕ)).card ≤ n + 1 := by
      refine le_trans Finset.card_image_le ?_
      simp
    have h3 : n + 2 < 2 ^ (n + 2) := Nat.lt_two_pow_self
    show (insert none ((Finset.range (n + 1)).image (some : ℕ → Option ℕ))).card
      ≤ 2 ^ (1 * (n + 1) ^ 1 + 1)
    have h4 : 1 * (n + 1) ^ 1 + 1 = n + 2 := by ring
    rw [h4]
    omega


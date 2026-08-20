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

theorem mem_Dset {n : ℕ} {m : SMem N.Mem} (h : SInv N S g n m) : m ∈ Dset N S g n := by
  cases m with
  | scan i =>
    have hi : i ≤ n := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ ?_)))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  | outer m todo =>
    obtain ⟨rfl, hsuf⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ ?_)))
    exact Finset.mem_image.mpr ⟨todo, mem_LSset hsuf, rfl⟩
  | call m todo a b k st =>
    obtain ⟨rfl, hsuf, ha, hb, hst⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    refine Finset.mem_image.mpr ⟨(todo, a, b, k, st), ?_, rfl⟩
    have hk : k ≤ g m := by have := stackAt_length st k hst; omega
    refine Finset.mem_product.mpr ⟨mem_LSset hsuf, Finset.mem_product.mpr ⟨ha, ?_⟩⟩
    exact Finset.mem_product.mpr ⟨hb, Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (show k < g m + 1 by omega), mem_STKset hst⟩⟩
  | ret m todo v st =>
    obtain ⟨rfl, hsuf, k, hst⟩ := h
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    refine Finset.mem_image.mpr ⟨(todo, v, st), ?_, rfl⟩
    refine Finset.mem_product.mpr ⟨mem_LSset hsuf, Finset.mem_product.mpr ⟨?_, mem_STKset hst⟩⟩
    cases v <;> simp
  | acc =>
    refine Finset.mem_union_right _ ?_
    simp

/-! ### The cardinality bound -/


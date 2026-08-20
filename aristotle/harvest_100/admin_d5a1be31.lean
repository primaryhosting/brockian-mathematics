/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This file is self-contained: the proof uses only core `Lean`/`Init` (`Bool`, `Fin`, `decide`),
-- so no `import` is required.  (Mathlib currently has no Ramsey-number API to reuse here.)

namespace Math

/-- Pigeonhole for five booleans: among `b1, …, b5` some three are equal. -/
private theorem bool_pigeon :
    ∀ b1 b2 b3 b4 b5 : Bool,
      (b1 = b2 ∧ b2 = b3) ∨
      (b1 = b2 ∧ b2 = b4) ∨
      (b1 = b2 ∧ b2 = b5) ∨
      (b1 = b3 ∧ b3 = b4) ∨
      (b1 = b3 ∧ b3 = b5) ∨
      (b1 = b4 ∧ b4 = b5) ∨
      (b2 = b3 ∧ b3 = b4) ∨
      (b2 = b3 ∧ b3 = b5) ∨
      (b2 = b4 ∧ b4 = b5) ∨
      (b3 = b4 ∧ b4 = b5) := by decide

/-- If none of `x`, `y`, `z` equals `v`, then all three are equal (they are all `!v`). -/
private theorem bool_step :
    ∀ v x y z : Bool, x = v ∨ y = v ∨ z = v ∨ (x = y ∧ y = z) := by decide

/-- **R(3,3) = 6.**

An edge 2-colouring of the complete graph on the vertex set `Fin n` is encoded by a function
`c : Fin n → Fin n → Bool`, the colour of the edge `{i, j}` with `i < j` being `c i j`;
a monochromatic triangle is a triple `i < j < k` with `c i j = c i k = c j k`.

First conjunct: *every* 2-colouring of the edges of `K₆` contains a monochromatic triangle.
(No symmetry assumption on `c` is needed, since only the entries with `i < j` are used.)

Second conjunct: there is a 2-colouring of the edges of `K₅` — symmetric, hence an honest
edge colouring — with no monochromatic triangle, namely the pentagon/pentagram colouring. -/
theorem ramsey_3_3 :
    (∀ c : Fin 6 → Fin 6 → Bool,
        ∃ i j k : Fin 6, i < j ∧ j < k ∧ c i j = c i k ∧ c i k = c j k) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j : Fin 5, c i j = c j i) ∧
        ∀ i j k : Fin 5, i < j → j < k → ¬(c i j = c i k ∧ c i k = c j k)) := by
  constructor
  · -- Pigeonhole at vertex `0`: three of the five edges at `0` share a colour, say the
    -- edges to `i < j < k`.  If one of the edges `ij`, `ik`, `jk` also has that colour we
    -- get a triangle through `0`; otherwise `ijk` is a triangle of the other colour.
    intro c
    rcases bool_pigeon (c 0 1) (c 0 2) (c 0 3) (c 0 4) (c 0 5) with
      h | h | h | h | h | h | h | h | h | h
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 2) (c 1 3) (c 2 3) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 2, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 3, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 2, 3, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 2, 3, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 2) (c 1 4) (c 2 4) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 2, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 4, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 2, 4, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 2, 4, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 2) (c 1 5) (c 2 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 2, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 2, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 2, 5, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 3) (c 1 4) (c 3 4) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 3, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 4, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 3, 4, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 3, 4, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 3) (c 1 5) (c 3 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 3, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 3, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 3, 5, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 1) (c 1 4) (c 1 5) (c 4 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 1, 4, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 1, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 4, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨1, 4, 5, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 2) (c 2 3) (c 2 4) (c 3 4) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 2, 3, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 2, 4, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 3, 4, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨2, 3, 4, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 2) (c 2 3) (c 2 5) (c 3 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 2, 3, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 2, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 3, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨2, 3, 5, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 2) (c 2 4) (c 2 5) (c 4 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 2, 4, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 2, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 4, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨2, 4, 5, by decide, by decide, p, q⟩
    · obtain ⟨h1, h2⟩ := h
      rcases bool_step (c 0 3) (c 3 4) (c 3 5) (c 4 5) with hx | hy | hz | ⟨p, q⟩
      · exact ⟨0, 3, 4, by decide, by decide, h1, h1.symm.trans hx.symm⟩
      · exact ⟨0, 3, 5, by decide, by decide, h1.trans h2, (h1.trans h2).symm.trans hy.symm⟩
      · exact ⟨0, 4, 5, by decide, by decide, h2, (h1.trans h2).symm.trans hz.symm⟩
      · exact ⟨3, 4, 5, by decide, by decide, p, q⟩
  · -- The pentagon colouring of `K₅`: `c i j = true` iff `j = i ± 1 (mod 5)`.
    refine ⟨fun i j => decide ((j : Nat) = ((i : Nat) + 1) % 5 ∨ (i : Nat) = ((j : Nat) + 1) % 5),
      ?_, ?_⟩
    · decide
    · decide

/-- The same statement phrased for *symmetric* colourings and unordered triples of distinct
vertices: every symmetric 2-colouring of the edges of `K₆` has three pairwise distinct vertices
spanning a monochromatic triangle, while some symmetric 2-colouring of `K₅` has none.
The symmetry hypothesis in the first conjunct is stated for faithfulness to "edge colouring";
it is in fact not needed, as `Math.ramsey_3_3` shows. -/
theorem ramsey_3_3_symm :
    (∀ c : Fin 6 → Fin 6 → Bool, (∀ i j : Fin 6, c i j = c j i) →
        ∃ i j k : Fin 6, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ c i j = c i k ∧ c i k = c j k) ∧
    (∃ c : Fin 5 → Fin 5 → Bool, (∀ i j : Fin 5, c i j = c j i) ∧
        ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k → ¬(c i j = c i k ∧ c i k = c j k)) := by
  refine ⟨fun c _ => ?_, ?_⟩
  · obtain ⟨i, j, k, hij, hjk, h1, h2⟩ := ramsey_3_3.1 c
    have hik : i < k := Nat.lt_trans hij hjk
    exact ⟨i, j, k, fun he => Nat.ne_of_lt hij (congrArg Fin.val he),
      fun he => Nat.ne_of_lt hik (congrArg Fin.val he),
      fun he => Nat.ne_of_lt hjk (congrArg Fin.val he), h1, h2⟩
  · refine ⟨fun i j => decide ((j : Nat) = ((i : Nat) + 1) % 5 ∨ (i : Nat) = ((j : Nat) + 1) % 5),
      ?_, ?_⟩
    · decide
    · decide

end Math


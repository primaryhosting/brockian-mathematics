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

theorem svalid_small {N K s : ℕ} (hN : N ≤ 2 ^ s) (hK : K = s + 1) :
    Nonempty ({p : SState // SValid N K p} ↪ Fin (2 ^ (6 * (s + 2) ^ 2))) := by
  classical
  refine ⟨Function.Embedding.trans (Function.Embedding.trans
    (⟨fun p => (p.1.1, fun i : Fin (K + 1) => (p.1.2[(i : ℕ)]?).map (fcode N K)), ?_⟩ :
      {p : SState // SValid N K p} ↪
        Option Bool × (Fin (K + 1) → Option (FrameCode N K)))
    (Fintype.equivFin _).toEmbedding) (Fin.castLEEmb ?_)⟩
  · intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2'⟩ := hpq
    have h2 : ∀ i : Fin (K + 1),
        (p.1.2[(i : ℕ)]?).map (fcode N K) = (q.1.2[(i : ℕ)]?).map (fcode N K) :=
      fun i => congrFun h2' i
    refine Subtype.ext (Prod.ext h1 ?_)
    refine List.ext_getElem? ?_
    intro i
    by_cases hi : i < K + 1
    · have hi2 := h2 ⟨i, hi⟩
      simp only at hi2
      cases hp : p.1.2[i]? with
      | none =>
        cases hq : q.1.2[i]? with
        | none => rfl
        | some G => rw [hp, hq] at hi2; simp at hi2
      | some F =>
        cases hq : q.1.2[i]? with
        | none => rw [hp, hq] at hi2; simp at hi2
        | some G =>
          rw [hp, hq] at hi2
          simp only [Option.map_some, Option.some.injEq] at hi2
          have hFmem : F ∈ p.1.2 := List.mem_of_getElem? hp
          have hGmem : G ∈ q.1.2 := List.mem_of_getElem? hq
          rw [fcode_inj (p.2.2 F hFmem) (q.2.2 G hGmem) hi2]
    · have hlp : p.1.2.length ≤ i := le_trans p.2.length_le (by omega)
      have hlq : q.1.2.length ≤ i := le_trans q.2.length_le (by omega)
      rw [List.getElem?_eq_none hlp, List.getElem?_eq_none hlq]
  · have hcard : Fintype.card (Option Bool × (Fin (K + 1) → Option (FrameCode N K)))
        = 3 * ((N + 1) * ((N + 1) * ((K + 1) * ((N + 2) * 2))) + 1) ^ (K + 1) := by
      simp [FrameCode]
    rw [hcard]
    exact svalid_card_bound hN hK

/-! ## Savitch's theorem -/

/-- The configuration graph of `M` on inputs of length `n`, extended by a fresh target node
`M.size n` reachable from every accepting configuration. -/

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

theorem fcode_inj {N K : ℕ} {F G : Frame} (hF : FrameOk N K F) (hG : FrameOk N K G)
    (h : fcode N K F = fcode N K G) : F = G := by
  obtain ⟨hFk, hFu, hFv, hFm⟩ := hF
  obtain ⟨hGk, hGu, hGv, hGm⟩ := hG
  simp only [fcode, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact Frame.ext (by omega) (by omega) (by omega) (by omega) h5

/-- The arithmetic bound behind the space bound of the simulator. -/

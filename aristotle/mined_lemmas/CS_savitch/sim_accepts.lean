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

theorem sim_accepts (hE : ∀ u v, edgeOf edge epos bitf u v → u ≤ N ∧ v ≤ N)
    (u tgt K : ℕ) (hu : u ≤ N) (htgt : tgt ≤ N) :
    (∃ t, (srun N edge epos bitf)^[t] (none, [⟨u, tgt, K, 0, false⟩]) = (some true, []))
      ↔ Steps (edgeOf edge epos bitf) (2 ^ K) u tgt := by
  classical
  obtain ⟨T, hT⟩ := sim_key hE K u tgt [] hu htgt
  constructor
  · rintro ⟨t, ht⟩
    have h1 : (srun N edge epos bitf)^[max t T] (none, [⟨u, tgt, K, 0, false⟩])
        = (some true, []) := by
      rw [show max t T = (max t T - t) + t by omega, Function.iterate_add_apply, ht,
        srun_iterate_nil]
    have h2 : (srun N edge epos bitf)^[max t T] (none, [⟨u, tgt, K, 0, false⟩])
        = (some (decide (Steps (edgeOf edge epos bitf) (2 ^ K) u tgt)), []) := by
      rw [show max t T = (max t T - T) + T by omega, Function.iterate_add_apply, hT,
        srun_iterate_nil]
    rw [h1] at h2
    have h3 : (true : Bool) = decide (Steps (edgeOf edge epos bitf) (2 ^ K) u tgt) := by
      simpa using congrArg Prod.fst h2
    exact of_decide_eq_true h3.symm
  · intro hS
    exact ⟨T, by rwa [decide_eq_true hS] at hT⟩

end Simulator

/-! ## Validity of simulator states, and counting them -/

/-- A frame is well formed for parameters `N`, `K`. -/
structure FrameOk (N K : ℕ) (F : Frame) : Prop where
  /-- level bound -/
  hk : F.k ≤ K
  /-- source bound -/
  hu : F.u ≤ N
  /-- target bound -/
  hv : F.v ≤ N
  /-- midpoint bound -/
  hm : F.m ≤ N + 1

/-- A simulator state is valid if its stack is well formed: levels increase by one from top to
bottom and all components are in range. -/

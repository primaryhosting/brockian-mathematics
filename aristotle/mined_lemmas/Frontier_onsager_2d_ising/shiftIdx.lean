import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

def shiftIdx {L : ℕ} (i : Fin L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- A spin configuration on the `L × L` torus. -/
abbrev Config (L : ℕ) := Fin L × Fin L → Bool

/-- The `±1` spin value at a site. -/

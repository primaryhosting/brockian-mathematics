import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem XA_subset (A : Set (FreeGroup (Fin 2))) : XA A ⊆ SX := by
  rintro x hx
  obtain ⟨w, hw, m, hm, rfl⟩ := by simpa [XA] using hx
  exact phi_mapsTo w (M_subset hm)


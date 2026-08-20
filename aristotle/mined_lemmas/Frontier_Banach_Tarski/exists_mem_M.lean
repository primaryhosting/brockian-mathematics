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

theorem exists_mem_M {x : E} (hx : x ∈ SX) : ∃ w : FreeGroup (Fin 2), ∃ m ∈ M, phi w m = x := by
  set q : Quotient orbitSetoid := Quotient.mk orbitSetoid ⟨x, hx⟩ with hq
  have hout : orbitSetoid.r (Quotient.out q) ⟨x, hx⟩ := Quotient.exact (Quotient.out_eq q)
  obtain ⟨w, hw⟩ := hout
  exact ⟨w, ((Quotient.out q : ↥SX) : E), ⟨q, rfl⟩, hw⟩


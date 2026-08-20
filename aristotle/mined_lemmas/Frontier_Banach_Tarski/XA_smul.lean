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

theorem XA_smul (u : FreeGroup (Fin 2)) (A : Set (FreeGroup (Fin 2))) :
    (phi u) • XA A = XA ((fun w => u * w) '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hy
    refine mem_XA.2 ⟨u * w, ⟨w, hw, rfl⟩, m, hm, ?_⟩
    rw [map_mul]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hwm]
    rfl
  · intro hx
    obtain ⟨w', ⟨w, hw, rfl⟩, m, hm, hwm⟩ := mem_XA.1 hx
    refine ⟨phi w m, mem_XA.2 ⟨w, hw, m, hm, rfl⟩, ?_⟩
    rw [map_mul] at hwm
    simpa using hwm

end Selector

/-- **The Hausdorff paradox** (free part): the sphere minus the countable set of poles is
paradoxical. -/

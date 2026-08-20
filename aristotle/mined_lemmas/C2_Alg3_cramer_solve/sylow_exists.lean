import Mathlib
namespace C2.Alg3

/-- Cramer-style solution: if `det A` is a unit, then `A⁻¹ b` solves `A x = b`. -/

theorem sylow_exists {G : Type*} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    ∃ _P : Sylow p G, True :=
  ⟨Nonempty.some inferInstance, trivial⟩

end C2.Alg3


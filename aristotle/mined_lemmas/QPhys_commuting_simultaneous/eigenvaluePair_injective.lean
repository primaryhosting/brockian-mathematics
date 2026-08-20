import Mathlib

/-!
# Commuting Simultaneous
Category: Quantum Physics
Target: QPhys.commuting_simultaneous
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Module Module.End

namespace QPhys

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {A B : E →ₗ[ℂ] E}

local notation "EV" => Module.End.Eigenvalues

omit [FiniteDimensional ℂ E] in
/-- The map sending a pair of eigenvalues of `A` and `B` to the corresponding pair of scalars
(in the order used by Mathlib's joint eigenspace family) is injective. -/

private theorem eigenvaluePair_injective :
    Function.Injective
      (fun p : EV (A : Module.End ℂ E) × EV (B : Module.End ℂ E) ↦ ((p.2 : ℂ), (p.1 : ℂ))) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Subtype.ext h.2) (Subtype.ext h.1)

/-- The joint eigenspaces indexed by pairs of eigenvalues already exhaust the space. -/

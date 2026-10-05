import Mathlib
/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command in a file
-- (a module doc comment before `import Mathlib` is a hard parse error), so the
-- requested header comment is placed immediately after the single import.

namespace Phys

/-- **Kramers degeneracy.**

Let `V` be a complex vector space (the state space of a quantum system), let
`T : V →ₛₗ[starRingEnd ℂ] V` be the (conjugate-linear) time-reversal operator of a
half-integer-spin system, so that `T ∘ T = -1`, and let `H` be a linear operator
(the Hamiltonian) commuting with `T` (time-reversal invariance).

Then every eigenvector `v ≠ 0` of `H` with real eigenvalue `lam` gives rise to a second
eigenvector `T v` for the same eigenvalue, and `v`, `T v` are linearly independent:
the level `lam` is (at least) doubly degenerate. -/

theorem kramers_degeneracy_two_le_rank
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₛₗ[starRingEnd ℂ] V) (hT2 : ∀ v, T (T v) = -v)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ v, H (T v) = T (H v))
    (lam : ℝ) (v : V) (hv : v ≠ 0) (hHv : H v = (lam : ℂ) • v) :
    2 ≤ Module.rank ℂ (Module.End.eigenspace H (lam : ℂ)) := by
  obtain ⟨hTv, hindep⟩ := kramers_degeneracy T hT2 H hcomm lam v hv hHv
  set W := Module.End.eigenspace H (lam : ℂ)
  have hvW : v ∈ W := Module.End.mem_eigenspace_iff.2 hHv
  have hTvW : T v ∈ W := Module.End.mem_eigenspace_iff.2 hTv
  have h2 : LinearIndependent ℂ ![(⟨v, hvW⟩ : W), ⟨T v, hTvW⟩] := by
    apply LinearIndependent.of_comp W.subtype
    convert hindep using 1
    ext i; fin_cases i <;> rfl
  simpa using h2.cardinal_lift_le_rank

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


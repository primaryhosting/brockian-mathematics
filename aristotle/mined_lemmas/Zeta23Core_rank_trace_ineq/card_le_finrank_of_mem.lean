/-
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring; the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# Rank Trace Ineq
Category: Brockian Corpus
Target: Zeta23Core.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Zeta23Core

open Matrix RCLike Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Frobenius norm of a matrix, `‖M‖_F² = Re tr(Mᴴ M)`. -/

lemma card_le_finrank_of_mem {E ι : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (g : OrthonormalBasis ι 𝕜 E) (T : Finset ι)
    (V : Submodule 𝕜 E) (h : ∀ k ∈ T, g k ∈ V) : T.card ≤ Module.finrank 𝕜 V := by
  classical
  have hli : LinearIndependent 𝕜 (fun k : T => (⟨g k, h k k.2⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hc : (V.subtype ∘ fun k : T => (⟨g k, h k k.2⟩ : V)) = fun k : T => g (k : ι) := rfl
    rw [hc]
    exact (g.orthonormal.comp (fun k : T => (k : ι)) Subtype.val_injective).linearIndependent
  simpa using LinearIndependent.fintype_card_le_finrank hli


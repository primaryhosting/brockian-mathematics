import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

lemma norm_fst_le_of_mem_closure {D : Submodule ℂ E} {T : D →ₗ[ℂ] E} (hsym : IsSymmetricOp T)
    {p : E × E} (hp : p ∈ (opGraph T).topologicalClosure) : ‖p.1‖ ≤ ‖defMap E p‖ := by
  have hclosed : IsClosed {q : E × E | ‖q.1‖ ≤ ‖defMap E q‖} := by
    have h1 : Continuous fun q : E × E => ‖q.1‖ := continuous_norm.comp continuous_fst
    have h2 : Continuous fun q : E × E => ‖defMap E q‖ := (defMap E).continuous.norm
    exact isClosed_le h1 h2
  have hsub : (opGraph T : Set (E × E)) ⊆ {q : E × E | ‖q.1‖ ≤ ‖defMap E q‖} := by
    rintro q hq
    rw [SetLike.mem_coe, mem_opGraph_iff] at hq
    obtain ⟨x, rfl⟩ := hq
    have hid := norm_sub_I_smul_sq hsym x
    have : ‖(x : E)‖ ^ 2 ≤ ‖T x - Complex.I • (x : E)‖ ^ 2 := by
      rw [hid]; nlinarith [sq_nonneg ‖T x‖]
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).mp this
    simpa [defMap] using this
  have hmem : p ∈ closure (opGraph T : Set (E × E)) := by
    rwa [← Submodule.topologicalClosure_coe, SetLike.mem_coe]
  exact closure_minimal hsub hclosed hmem

/-- **Basic criterion for essential self-adjointness.**  A symmetric operator whose two
deficiency subspaces are trivial is essentially self-adjoint. -/

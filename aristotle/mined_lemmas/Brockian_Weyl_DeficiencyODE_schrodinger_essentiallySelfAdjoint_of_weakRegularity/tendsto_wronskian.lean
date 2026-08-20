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

lemma tendsto_wronskian (c : ℤ → ℂ) (hsum : Summable fun n => ‖c n‖ ^ 2) :
    Tendsto (wronskian c) atTop (𝓝 0) ∧ Tendsto (wronskian c) atBot (𝓝 0) := by
  have hs : Tendsto (fun n => ‖c n‖ ^ 2) cofinite (𝓝 0) := hsum.tendsto_cofinite_zero
  rw [Int.cofinite_eq] at hs
  have htop : Tendsto (fun n => ‖c n‖ ^ 2) atTop (𝓝 0) := hs.mono_left le_sup_right
  have hbot : Tendsto (fun n => ‖c n‖ ^ 2) atBot (𝓝 0) := hs.mono_left le_sup_left
  have hshift_top : Tendsto (fun n : ℤ => ‖c (n + 1)‖ ^ 2) atTop (𝓝 0) :=
    htop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hshift_bot : Tendsto (fun n : ℤ => ‖c (n + 1)‖ ^ 2) atBot (𝓝 0) :=
    hbot.comp (tendsto_atBot_add_const_right atBot 1 tendsto_id)
  refine ⟨squeeze_zero_norm (fun n => abs_wronskian_le c n) ?_,
    squeeze_zero_norm (fun n => abs_wronskian_le c n) ?_⟩
  · simpa using ((hshift_top.add htop).div_const 2)
  · simpa using ((hshift_bot.add hbot).div_const 2)

/-- Auxiliary version of the vanishing theorem for `Im z > 0`. -/

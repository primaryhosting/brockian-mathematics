import Mathlib

/-!
# Voevodsky Milnor: definitions and supporting results

Supporting development for `Frontier.voevodsky_milnor` (see `RequestProject/Main.lean`):
mod-2 Milnor K-theory, mod-2 Galois cohomology, the statement of the Milnor conjecture, the
degree-zero base case, the separably closed case, and the degree-one identifications.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false

namespace Frontier

/-!
## Mod-2 Milnor K-theory

For a field `F`, the `n`-th Milnor K-group `K^M_n(F)` is the degree-`n` part of the quotient of
the tensor algebra of the abelian group `Fˣ` by the Steinberg relations `a ⊗ (1 - a) = 0`.
Reducing mod 2, `k^M_n(F) = K^M_n(F)/2` is therefore the quotient of the free `ZMod 2`-module on
`n`-tuples of units by
* multilinearity in each slot, and
* the Steinberg relations (in adjacent slots).

This is the definition used below.
-/

section Milnor

variable (F : Type) [Field F]

/-- The defining relations of mod-2 Milnor K-theory in degree `n`: multilinearity in each slot,
and the Steinberg relation `{a, 1 - a} = 0` in adjacent slots. -/

lemma milnorK2_succ_subsingleton (hchar : ringChar F ≠ 2) (n : ℕ) :
    Subsingleton (MilnorK2 F (n + 1)) := by
  rw [Submodule.Quotient.subsingleton_iff]
  refine eq_top_iff.2 fun x _ => ?_
  have key : ∀ v : Fin (n + 1) → Fˣ,
      Finsupp.single v (1 : ZMod 2) ∈ Submodule.span (ZMod 2) (milnorRelSet F (n + 1)) := by
    intro v
    obtain ⟨b, hb⟩ := exists_sq F hchar (v 0)
    have hmem : Finsupp.single (Function.update v 0 (b * b)) (1 : ZMod 2)
        - Finsupp.single (Function.update v 0 b) 1
        - Finsupp.single (Function.update v 0 b) 1 ∈ milnorRelSet F (n + 1) :=
      Or.inl ⟨0, v, b, b, rfl⟩
    have h1 : Function.update v 0 (b * b) = v := by rw [hb]; exact Function.update_eq_self _ _
    have h2 : Finsupp.single (Function.update v 0 b) (1 : ZMod 2)
        + Finsupp.single (Function.update v 0 b) (1 : ZMod 2) = 0 := by
      rw [← Finsupp.single_add]
      simp only [show (1 : ZMod 2) + 1 = 0 from rfl, Finsupp.single_zero]
    have hspan := Submodule.subset_span (R := ZMod 2) hmem
    rwa [h1, sub_sub, h2, sub_zero] at hspan
  induction x using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ (hf trivial) (hg trivial)
  | single v c =>
      have hc : Finsupp.single v c = c • Finsupp.single v (1 : ZMod 2) := by
        simp [Finsupp.smul_single]
      rw [hc]
      exact Submodule.smul_mem _ _ (key v)


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

lemma mem_contCocycles_one_iff (f : (Fin 1 → AbsGal F) → ZMod 2) :
    f ∈ contCocycles F 1 ↔ ev1 F f ∈ contHom1 F := by
  constructor
  · rintro ⟨hlc, hker⟩
    refine ⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), fun a b => ?_⟩
    have h := congrFun hker ![a, b]
    rw [dd_one_apply] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h
    have h2 : f (fun _ => a * b) + (f (fun _ => a) + f (fun _ => b)) = 0 := by
      rw [← h]; abel
    have h3 := congrArg (fun x => x + (f (fun _ => a) + f (fun _ => b))) h2
    simp only [zero_add] at h3
    rw [add_assoc, add_self_eq_zero_zmod2, add_zero] at h3
    exact h3
  · rintro ⟨hlc, hhom⟩
    have hf : IsLocallyConstant f := by
      have : f = (ev1 F f) ∘ (fun v : Fin 1 → AbsGal F => v 0) := by
        funext v
        show f v = f (fun _ => v 0)
        congr 1
        funext j
        rw [Subsingleton.elim j 0]
      rw [this]
      exact hlc.comp_continuous (continuous_apply 0)
    refine ⟨hf, ?_⟩
    funext g
    rw [dd_one_apply]
    have h := hhom (g 0) (g 1)
    show f (fun _ => g 1) + (f (fun _ => g 0 * g 1) + f (fun _ => g 0)) = 0
    rw [show f (fun _ => g 0 * g 1) = f (fun _ => g 0) + f (fun _ => g 1) from h]
    rw [show f (fun _ => g 1) + (f (fun _ => g 0) + f (fun _ => g 1) + f (fun _ => g 0))
        = (f (fun _ => g 1) + f (fun _ => g 1)) + (f (fun _ => g 0) + f (fun _ => g 0)) by abel,
      add_self_eq_zero_zmod2, add_self_eq_zero_zmod2, add_zero]


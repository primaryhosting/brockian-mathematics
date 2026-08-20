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

lemma dd_mem_contCochains {n : ℕ} {f : (Fin n → AbsGal F) → ZMod 2}
    (hf : f ∈ contCochains F n) : dd (AbsGal F) n f ∈ contCochains F (n + 1) := by
  have hf' : IsLocallyConstant f := hf
  have h1 : IsLocallyConstant fun g : Fin (n + 1) → AbsGal F => f fun i => g i.succ :=
    hf'.comp_continuous (continuous_pi fun i => continuous_apply _)
  have h2 : ∀ j : Fin (n + 1),
      IsLocallyConstant fun g : Fin (n + 1) → AbsGal F => f (Fin.contractNth j (· * ·) g) :=
    fun j => hf'.comp_continuous (continuous_contractNth j)
  have : IsLocallyConstant fun g : Fin (n + 1) → AbsGal F =>
      f (fun i => g i.succ) + ∑ j : Fin (n + 1), f (Fin.contractNth j (· * ·) g) := by
    refine IsLocallyConstant.comp₂ h1 ?_ (· + ·)
    classical
    induction (Finset.univ : Finset (Fin (n + 1))) using Finset.induction with
    | empty => simpa using IsLocallyConstant.const (0 : ZMod 2)
    | insert a s ha ih =>
        simpa [Finset.sum_insert ha] using IsLocallyConstant.comp₂ (h2 a) ih (· + ·)
  simpa [contCochains, Set.mem_setOf_eq, funext fun g => dd_apply (AbsGal F) n f g] using this

/-- Continuous `n`-cocycles. -/

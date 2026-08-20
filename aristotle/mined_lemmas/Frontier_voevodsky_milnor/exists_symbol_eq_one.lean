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

import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

`K^M_n(F)/2` is the abelian group (a `ZMod 2`-vector space) presented by generators the
symbols `{a₁, …, aₙ}` with `aᵢ ∈ Fˣ`, subject to
* multilinearity `{…, a·b, …} = {…, a, …} + {…, b, …}`, and
* the Steinberg relation `{…, a, …, 1 - a, …} = 0`.

Since the coefficients are taken in `ZMod 2` this is exactly Milnor K-theory modulo `2`.

## Main definitions

* `Frontier.milnorRelations F n` : the set of defining relations.
* `Frontier.KMilnorMod2 F n` : the group `K^M_n(F)/2`.
* `Frontier.symbol F v` : the symbol `{v 0, …, v (n-1)}`.

## Main results

* `Frontier.kMilnorMod2ZeroEquiv` : `K^M_0(F)/2 ≃ ℤ/2`.
* `Frontier.exists_symbol_eq_one` : in degree one, every element is a single symbol.
-/

namespace Frontier

variable (F : Type) [Field F]

/-- The defining relations of `K^M_n(F)/2`: multilinearity in each slot and the Steinberg
relation `{…, a, …, 1 - a, …} = 0`. -/

lemma exists_symbol_eq_one (x : KMilnorMod2 F 1) :
    ∃ a : Fˣ, x = symbol F (fun _ => a) := by
  induction x using Submodule.Quotient.induction_on with
  | H c =>
    induction c using Finsupp.induction with
    | zero => exact ⟨1, by simpa using (symbol_one_one (F := F)).symm⟩
    | single_add v r f _ _ ih =>
        obtain ⟨a, ha⟩ := ih
        have hv : v = fun _ => v 0 := by
          funext i; fin_cases i; rfl
        have hmk : (Submodule.Quotient.mk (Finsupp.single v r + f) : KMilnorMod2 F 1)
            = r • symbol F (fun _ => v 0) + symbol F (fun _ => a) := by
          rw [Submodule.Quotient.mk_add, ← ha]
          congr 1
          rw [hv]
          unfold symbol
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hmk]
        by_cases hr : r = 0
        · exact ⟨a, by simp [hr]⟩
        · have hzo : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
          have hr1 : r = 1 := hzo r hr
          refine ⟨v 0 * a, ?_⟩
          rw [hr1, one_smul, symbol_one_mul]

end Frontier

import Mathlib

/-!
# Continuous cochain cohomology with `ZMod 2` coefficients

For a topological group `G` we define the cohomology of the complex of *continuous*
inhomogeneous cochains `Gⁿ → ZMod 2`, where `G` acts trivially on `ZMod 2`
(equipped with the discrete topology).  This is the standard definition of the
Galois cohomology groups `Hⁿ(G, ℤ/2)` when `G` is a profinite group, such as an
absolute Galois group.

The differential is taken to be Mathlib's differential on inhomogeneous cochains
(`groupCohomology.inhomogeneousCochains.d`) for the trivial representation, so that
`d ∘ d = 0` comes for free.

## Main definitions

* `Frontier.contCochains G n` : the submodule of continuous cochains `Gⁿ → ZMod 2`.
* `Frontier.contCohomology G n` : the `n`-th continuous cochain cohomology group.

## Main results

* `Frontier.contCohomologyZeroEquiv` : `H⁰(G, ℤ/2) ≃ ℤ/2`.
* `Frontier.contCohomologyOneEquiv` : `H¹(G, ℤ/2) ≃ Homcont(G, ℤ/2)`.
-/

namespace Frontier

open groupCohomology

variable (G : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- The differential on inhomogeneous cochains with trivial `ZMod 2`-coefficients. -/

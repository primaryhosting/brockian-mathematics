import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem smolensky_dim {m D : ℕ} (hn : n = 2 * m) {ζ : F} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (A : Finset (Cube n)) (P : Cube n → F) (hP : P ∈ Deg F n D)
    (hPA : ∀ x ∈ A, UU ζ Finset.univ x = P x) :
    #A ≤ ∑ i ∈ Finset.range (m + D + 1), n.choose i := by
  classical
  set res : (Cube n → F) →ₗ[F] (↥A → F) :=
    LinearMap.funLeft F F (fun y : ↥A => (y : Cube n)) with hres
  have hressurj : Function.Surjective res :=
    LinearMap.funLeft_surjective_of_injective F F _ (fun y z h => Subtype.ext h)
  set W := Deg F n (m + D) with hW
  -- every `UU ζ S` restricts into the image of `W`
  have hUS : ∀ S : Finset (Fin n), res (UU ζ S) ∈ Submodule.map res W := by
    intro S
    by_cases hS : S.card ≤ m + D
    · exact Submodule.mem_map_of_mem (mem_Deg_of_le (UU_mem_Deg ζ S) hS)
    · have hSm : m < S.card := by omega
      have hcompl : Sᶜ.card ≤ m := by
        have : Sᶜ.card = n - S.card := by simp [Finset.card_compl]
        omega
      have hmem : P * (∏ i ∈ Sᶜ, vv ζ i) ∈ W := by
        refine mem_Deg_of_le (mul_mem_Deg hP
          (prod_mem_Deg (F := F) Sᶜ (fun i => vv ζ i) 1 (fun i _ => vv_mem_Deg ζ i))) ?_
        simp only [mul_one]
        omega
      refine ⟨P * (∏ i ∈ Sᶜ, vv ζ i), hmem, ?_⟩
      funext y
      have hy : (y : Cube n) ∈ A := y.2
      simp only [hres, LinearMap.funLeft_apply]
      rw [← UU_split hζ0 S]
      simp only [Pi.mul_apply]
      rw [hPA _ hy]
  have hmaptop : Submodule.map res W = ⊤ := by
    refine top_le_iff.mp ?_
    have h1 : Submodule.map res (⊤ : Submodule F (Cube n → F)) = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 hressurj]
    rw [← h1, ← span_UU_eq_top hζ1, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨_, ⟨S, rfl⟩, rfl⟩
    exact hUS S
  have hfin : Module.finrank F (↥A → F) = #A := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  calc #A = Module.finrank F (↥A → F) := hfin.symm
    _ = Module.finrank F (Submodule.map res W) := by rw [hmaptop, finrank_top]
    _ ≤ Module.finrank F W := Submodule.finrank_map_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + D + 1), n.choose i := finrank_Deg_le n (m + D)

end CS

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
# Binomial coefficient estimates

Two elementary facts used in the Razborov–Smolensky argument:

* the central binomial coefficient satisfies `C(2m,m)^2 * (3m+1) ≤ 16^m`
  (i.e. `C(2m,m) ≲ 4^m / √(3m)`);
* the partial sum `∑_{i ≤ m+D} C(2m,i)` is at most `4^m/2 + (D+1) C(2m,m)`.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 (3m+1) ≤ 16^m`. -/

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

lemma exists_generator_sq_mem (h2 : (2 : F) ≠ 0)
    (L : IntermediateField F (SeparableClosure F)) (hL : Module.finrank F L = 2) :
    ∃ y : SeparableClosure F, y ∈ L ∧ y ∉ (⊥ : IntermediateField F (SeparableClosure F)) ∧
      ∃ c : F, y ^ 2 = algebraMap F (SeparableClosure F) c := by
  obtain ⟨x, hxL, hxb⟩ := exists_mem_not_mem_bot L hL
  have hadj : IntermediateField.adjoin F {x} = L := adjoin_eq_of_finrank_two hL hxL hxb
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hdeg : (minpoly F x).natDegree = 2 := by
    have h := IntermediateField.adjoin.finrank hint
    rw [hadj, hL] at h
    exact h.symm
  have hmonic : (minpoly F x).Monic := minpoly.monic hint
  have haeval : (Polynomial.aeval x) (minpoly F x) = 0 := minpoly.aeval F x
  set b := (minpoly F x).coeff 1 with hb
  set c := (minpoly F x).coeff 0 with hc
  have hexp : x ^ 2 + algebraMap F (SeparableClosure F) b * x
      + algebraMap F (SeparableClosure F) c = 0 := by
    rw [Polynomial.aeval_eq_sum_range, hdeg] at haeval
    have hlead : (minpoly F x).coeff 2 = 1 := by
      have := hmonic.coeff_natDegree
      rwa [hdeg] at this
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hlead, Algebra.smul_def,
      pow_zero, pow_one, mul_one, map_one, one_mul] at haeval
    rw [← haeval]
    ring
  refine ⟨x + algebraMap F (SeparableClosure F) (b / 2), ?_, ?_, ?_⟩
  · exact add_mem hxL (IntermediateField.algebraMap_mem L _)
  · intro hmem
    apply hxb
    have : x = (x + algebraMap F (SeparableClosure F) (b / 2))
        - algebraMap F (SeparableClosure F) (b / 2) := by ring
    rw [this]
    exact sub_mem hmem (IntermediateField.algebraMap_mem _ _)
  · refine ⟨b ^ 2 / 4 - c, ?_⟩
    have h2' : (2 : F) ≠ 0 := h2
    have hb2 : algebraMap F (SeparableClosure F) (b / 2) * 2 = algebraMap F _ b := by
      rw [← map_ofNat (algebraMap F (SeparableClosure F)) 2, ← map_mul]
      congr 1
      field_simp
    have hsq : algebraMap F (SeparableClosure F) (b ^ 2 / 4)
        = (algebraMap F (SeparableClosure F) (b / 2)) ^ 2 := by
      rw [← map_pow]
      congr 1
      rw [div_pow]
      norm_num
    rw [map_sub, hsq]
    have : (x + algebraMap F (SeparableClosure F) (b / 2)) ^ 2
        = x ^ 2 + algebraMap F (SeparableClosure F) (b / 2) * 2 * x
          + (algebraMap F (SeparableClosure F) (b / 2)) ^ 2 := by ring
    rw [this, hb2]
    linear_combination hexp


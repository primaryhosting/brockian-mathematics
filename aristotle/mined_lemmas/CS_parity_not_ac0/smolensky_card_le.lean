import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/

theorem smolensky_card_le {n D K : ℕ} (hK : n + D ≤ 2 * K) (G : Finset (Bits n)) (g : Fn n)
    (hg : g ∈ Deg n D) (hgG : ∀ x ∈ G, g x = sgn (parity n x)) :
    G.card ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ K)).card := by
  classical
  -- the restriction map to `G`
  let R : Fn n →ₗ[ZMod 3] (↥G → ZMod 3) :=
    { toFun := fun f a => f a.1
      map_add' := by intro f₁ f₂; rfl
      map_smul' := by intro c f; rfl }
  set W : Submodule (ZMod 3) (↥G → ZMod 3) := Submodule.map R (Deg n K) with hW
  -- every monomial restricts into `W`
  have step1 : ∀ T : Finset (Fin n), R (mon T) ∈ W := by
    intro T
    by_cases hT : T.card ≤ K
    · exact Submodule.mem_map_of_mem (mon_mem_Deg hT)
    · push_neg at hT
      have hcompl : (Tᶜ).card + D ≤ K := by
        have h1 : T.card + (Tᶜ).card = n := by
          simp
        omega
      have hmem : mon (Tᶜ) * g ∈ Deg n K := Deg_mono hcompl (Deg_mul (mon_mem_Deg le_rfl) hg)
      have heq : R (mon (Tᶜ) * g) = R (mon T) := by
        funext a
        have ha : (a : Bits n) ∈ G := a.2
        show (mon (Tᶜ) * g) (a : Bits n) = mon T (a : Bits n)
        rw [Pi.mul_apply, hgG _ ha, ← mon_univ_eq_sgn_parity, ← Pi.mul_apply, mon_mul,
          symmDiff_compl_univ]
      rw [← heq]
      exact Submodule.mem_map_of_mem hmem
  -- the restrictions of all monomials span everything
  have hspan : Submodule.map R (Deg n n) ≤ W := by
    rw [Deg, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro h ⟨f, hf, rfl⟩
    simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
    obtain ⟨T, -, rfl⟩ := hf
    exact step1 T
  have hWtop : W = ⊤ := by
    refine eq_top_iff.2 (fun h _ => ?_)
    have hF : (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) ∈ Deg n n :=
      Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (deltaFn_mem _))
    have hRF : R (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) = h := by
      funext b
      show (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) (b : Bits n) = h b
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single b]
      · simp [Pi.smul_apply, deltaFn_self]
      · intro a _ hab
        have : (a : Bits n) ≠ (b : Bits n) := fun hc => hab (Subtype.ext hc)
        simp [Pi.smul_apply, deltaFn_ne (Ne.symm this)]
      · intro hb
        exact absurd (Finset.mem_attach _ _) hb
    rw [← hRF]
    exact hspan (Submodule.mem_map_of_mem hF)
  -- dimension count
  have hcard : Module.finrank (ZMod 3) (↥G → ZMod 3) = G.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have himg : W = Submodule.span (ZMod 3) (((monSet n K).image R : Finset (↥G → ZMod 3)) :
      Set (↥G → ZMod 3)) := by
    rw [hW, Deg, Submodule.map_span, Finset.coe_image]
  have hle : Module.finrank (ZMod 3) ↥W ≤ ((monSet n K).image R).card := by
    rw [himg]
    have := finrank_span_le_card (R := ZMod 3)
      (((monSet n K).image R : Finset (↥G → ZMod 3)) : Set (↥G → ZMod 3))
    simpa using this
  have hWrank : Module.finrank (ZMod 3) ↑W = G.card := by
    rw [hWtop, finrank_top, hcard]
  have hfinal : G.card ≤ ((monSet n K).image R).card := by
    rw [← hWrank]; exact hle
  calc G.card ≤ ((monSet n K).image R).card := hfinal
    _ ≤ (monSet n K).card := Finset.card_image_le
    _ ≤ _ := by rw [monSet]; exact Finset.card_image_le

end CS

import Mathlib
import RequestProject.Basic
import RequestProject.Circuit
import RequestProject.Approx
import RequestProject.Counting
import RequestProject.Smolensky

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Sanity check that the class `AC⁰` as formalised here is not degenerate: the
unbounded fan-in `OR` family is in `AC⁰`. -/

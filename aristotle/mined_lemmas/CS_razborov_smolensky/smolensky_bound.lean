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

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above is
-- written as a plain block comment and repeated verbatim as a module docstring below.)

import RequestProject.RS.CircuitApprox
import RequestProject.RS.Smolensky
import RequestProject.RS.Binomial
import RequestProject.RS.Aux
import RequestProject.RS.Sanity

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the Boolean function `MOD p`
(which tests whether the number of `1`s in the input is divisible by `p`) is not computed by any
family of constant-depth, polynomial-size circuits with unbounded fan-in AND, OR, NOT and
`MOD q` gates, i.e. `MOD p ∉ AC⁰[q]`.

The proof combines
* `CS.RS.Circuit.exists_approx`: every `AC⁰[q]` circuit is approximated, on all but a small
  fraction of the inputs, by a low-degree function over a field of characteristic `q`;
* `CS.RS.smolensky_bound`: a low-degree function can agree with `x ↦ ζ^(weight x)` (for `ζ` a
  primitive `p`-th root of unity) only on a set of inputs of size at most
  `∑_{i ≤ n/2 + D} C(n,i)`;
* `CS.RS.modq_mem_AC0q`: a non-vacuity check, exhibiting `MOD q` itself as a depth-one,
  linear-size circuit family of this kind;
* binomial estimates showing that this is less than the number of inputs left over by the
  approximation step.
-/

namespace CS

open Finset CS.RS

/-- Shifting the weight by `(p - r) % p` detects the residue `r` modulo `p`. -/

theorem smolensky_bound {K : Type*} [Field K] {n : ℕ} (zeta : K) (p : ℕ) (hp : 1 ≤ p)
    (hz : zeta ^ p = 1) (hz1 : zeta ≠ 1) (D : ℕ) (g : Fn K n) (hg : g ∈ Deg K n D)
    (G : Finset (Cube n)) (hG : ∀ x ∈ G, g x = zeta ^ (wt x)) :
    G.card ≤ ∑ i ∈ Finset.range (n/2 + D + 1), n.choose i := by
  classical
  have hz10 : zeta - 1 ≠ 0 := sub_ne_zero.2 hz1
  -- the two families of "linear" functions
  set z : Fin n → Fn K n := fun i x => if x i then zeta else 1 with hzdef
  set w : Fin n → Fn K n := fun i x => if x i then zeta ^ (p-1) else 1 with hwdef
  have hzmem : ∀ i, z i ∈ Deg K n 1 := by
    intro i
    have he : z i = (1 : Fn K n) + (zeta - 1) • (fun x : Cube n => ind K (x i)) := by
      funext x
      rw [hzdef]
      cases h : x i <;> simp [ind, h]
    rw [he]
    exact Submodule.add_mem _ (one_mem_Deg 1) (Submodule.smul_mem _ _ (coord_mem_Deg i))
  have hwmem : ∀ i, w i ∈ Deg K n 1 := by
    intro i
    have he : w i = (1 : Fn K n) + (zeta ^ (p-1) - 1) • (fun x : Cube n => ind K (x i)) := by
      funext x
      rw [hwdef]
      cases h : x i <;> simp [ind, h]
    rw [he]
    exact Submodule.add_mem _ (one_mem_Deg 1) (Submodule.smul_mem _ _ (coord_mem_Deg i))
  have hpowz : zeta * zeta ^ (p-1) = 1 := by
    calc zeta * zeta ^ (p-1) = zeta ^ (p - 1 + 1) := by rw [pow_succ]; ring
      _ = zeta ^ p := by congr 1; omega
      _ = 1 := hz
  have hzw : ∀ i x, z i x * w i x = 1 := by
    intro i x
    rw [hzdef, hwdef]
    simp only
    cases h : x i <;> simp [hpowz]
  have hprodz : ∀ x : Cube n, ∏ i : Fin n, z i x = zeta ^ (wt x) := by
    intro x
    rw [hzdef]
    simp only
    rw [Finset.prod_ite]
    simp [wt, Finset.prod_const]
  -- the multiplicative characters
  set chi : Finset (Fin n) → Fn K n := fun S => ∏ i ∈ S, z i with hchidef
  have hchimem : ∀ S : Finset (Fin n), chi S ∈ Deg K n S.card := by
    intro S
    have h := prod_mem_Deg' S z 1 (fun i _ => hzmem i)
    simpa [hchidef] using h
  -- restriction to `G`
  set R : Fn K n →ₗ[K] ({x : Cube n // x ∈ G} → K) :=
    LinearMap.funLeft K K (fun y : {x : Cube n // x ∈ G} => (y : Cube n)) with hRdef
  have hRapply : ∀ (F : Fn K n) (y : {x : Cube n // x ∈ G}), R F y = F (y : Cube n) := by
    intro F y; rfl
  have hRsurj : Function.Surjective R := by
    intro h
    refine ⟨fun x => if hx : x ∈ G then h ⟨x, hx⟩ else 0, ?_⟩
    funext y
    rw [hRapply]
    simp [y.2]
  set W := Deg K n (n/2 + D) with hWdef
  -- every character restricts into the image of `W`
  have hkey : ∀ S : Finset (Fin n), R (chi S) ∈ Submodule.map R W := by
    intro S
    by_cases hS : S.card ≤ n/2
    · exact ⟨chi S, (Deg_le (by omega)) (hchimem S), rfl⟩
    · push_neg at hS
      refine ⟨g * (∏ i ∈ univ \ S, w i), ?_, ?_⟩
      · have h1 : (∏ i ∈ univ \ S, w i) ∈ Deg K n (univ \ S).card := by
          have h := prod_mem_Deg' (univ \ S) w 1 (fun i _ => hwmem i)
          simpa using h
        have h2 := mul_mem_Deg hg h1
        refine (Deg_le ?_) h2
        have hcard : (univ \ S).card = n - S.card := by
          rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
          simp
        rw [hcard]
        omega
      · funext y
        obtain ⟨x, hx⟩ := y
        rw [hRapply, hRapply]
        show g x * (∏ i ∈ univ \ S, w i) x = chi S x
        rw [Finset.prod_apply, hchidef]
        simp only
        rw [Finset.prod_apply, hG x hx, ← hprodz x]
        rw [← Finset.prod_sdiff (Finset.subset_univ S)]
        rw [mul_comm ((∏ i ∈ univ \ S, z i x)) (∏ i ∈ S, z i x), mul_assoc,
          ← Finset.prod_mul_distrib]
        rw [Finset.prod_congr rfl (fun i _ => hzw i x)]
        simp
  -- the characters span everything
  have hspanchi : Submodule.span K (Set.range chi) = ⊤ := by
    rw [eq_top_iff, ← Deg_top (K := K) (n := n)]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨T, -⟩, rfl⟩
    show mono K T ∈ Submodule.span K (Set.range chi)
    -- `mono K T` is a combination of characters
    have hmonoeq : mono K T = ((zeta - 1)⁻¹) ^ T.card • ∏ i ∈ T, (z i - 1) := by
      funext x
      rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
      have hfac : ∀ i ∈ T, (z i - 1) x = (zeta - 1) * ind K (x i) := by
        intro i _
        rw [Pi.sub_apply, hzdef]
        cases h : x i <;> simp [ind, h]
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const]
      rw [mono, ← mul_assoc, ← mul_pow]
      rw [inv_mul_cancel₀ hz10, one_pow, one_mul]
    rw [hmonoeq]
    refine Submodule.smul_mem _ _ ?_
    have hexp : (∏ i ∈ T, (z i - 1)) = ∑ S ∈ T.powerset, (chi S) * ∏ _i ∈ T \ S, (-1 : Fn K n) := by
      have := Finset.prod_add (fun i => z i) (fun _ => (-1 : Fn K n)) T
      simpa [sub_eq_add_neg, hchidef] using this
    rw [hexp]
    refine Submodule.sum_mem _ (fun S _ => ?_)
    have hconst : (chi S) * ∏ _i ∈ T \ S, (-1 : Fn K n) = ((-1 : K) ^ (T \ S).card) • chi S := by
      funext x
      simp [Finset.prod_const, mul_comm]
    rw [hconst]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
  -- hence the restriction of `W` is everything
  have hmap : Submodule.map R W = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Submodule K ({x : Cube n // x ∈ G} → K))
        = LinearMap.range R := (LinearMap.range_eq_top.2 hRsurj).symm
      _ = Submodule.map R ⊤ := (Submodule.map_top R).symm
      _ = Submodule.map R (Submodule.span K (Set.range chi)) := by rw [hspanchi]
      _ = Submodule.span K (R '' (Set.range chi)) := Submodule.map_span R _
      _ ≤ Submodule.map R W := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨_, ⟨S, rfl⟩, rfl⟩
          exact hkey S
  -- dimension count
  have hcardG : G.card = Module.finrank K ({x : Cube n // x ∈ G} → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  calc G.card = Module.finrank K ({x : Cube n // x ∈ G} → K) := hcardG
    _ = Module.finrank K (⊤ : Submodule K ({x : Cube n // x ∈ G} → K)) :=
        (finrank_top K _).symm
    _ = Module.finrank K (Submodule.map R W) := by rw [hmap]
    _ ≤ Module.finrank K W := Submodule.finrank_map_le R W
    _ ≤ ∑ i ∈ Finset.range (n/2 + D + 1), n.choose i := finrank_Deg_le K n (n/2 + D)

end RS
end CS

import RequestProject.RS.Degree

/-!
# The dimension of the space of low-degree functions
-/

namespace CS
namespace RS

open Finset


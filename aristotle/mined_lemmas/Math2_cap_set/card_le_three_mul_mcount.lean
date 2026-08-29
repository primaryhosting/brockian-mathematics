import Mathlib
/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
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

/-!
## The cap set problem

We prove the Croot–Lev–Pach / Ellenberg–Gijswijt bound: a subset of `𝔽₃ⁿ` containing no
non-trivial three-term arithmetic progression has size `o(3ⁿ)`.
-/

namespace CapSet

open Finset

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Points of `𝔽₃ⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ZMod 3

/-- Exponent vectors of reduced monomials (each exponent is `0`, `1` or `2`). -/
abbrev Exp (n : ℕ) := Fin n → Fin 3

/-- The monomial function `x ↦ ∏ i, x i ^ α i` on `𝔽₃ⁿ`. -/

theorem card_le_three_mul_mcount (n : ℕ) (hn : 1 ≤ n) (A : Finset (Pt n))
    (hA : ThreeAPFree (A : Set (Pt n))) : A.card ≤ 3 * mcount n (2 * n / 3) := by
  set e := 2 * n / 3 with he
  set d := 2 * n - e - 1 with hdd
  have harith1 : d + e + 1 = 2 * n := by omega
  have harith2 : d ≤ 2 * e + 1 := by omega
  set B : Finset (Pt n) := A.image (fun a => -a) with hB
  have hBcard : B.card = A.card := Finset.card_image_of_injective _ neg_injective
  -- the cap set property: sums of two distinct elements of `A` avoid `B`
  have hcap : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x + y ∉ B := by
    intro x hx y hy hxy hmem
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.1 hmem
    have hzz : x + y = z + z := by rw [← hzeq, two_smul_eq_neg]
    have h1 : x = z := hA (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hz) (Finset.mem_coe.2 hy) hzz
    have h2 : y = z := hA (Finset.mem_coe.2 hy) (Finset.mem_coe.2 hz) (Finset.mem_coe.2 hx)
      (by rw [add_comm]; exact hzz)
    exact hxy (h1.trans h2.symm)
  -- the space of polynomials of degree `≤ d` supported on `B`
  set fmap : (Pt n → ZMod 3) →ₗ[ZMod 3] ({v : Pt n // v ∈ Bᶜ} → ZMod 3) :=
    LinearMap.funLeft (ZMod 3) (ZMod 3) (fun v : {v : Pt n // v ∈ Bᶜ} => (v : Pt n)) with hfmap
  set W : Submodule (ZMod 3) (Pt n → ZMod 3) := polySpace n d ⊓ LinearMap.ker fmap with hW
  have hcodim : Module.finrank (ZMod 3) ({v : Pt n // v ∈ Bᶜ} → ZMod 3) = #(Bᶜ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hWrank : mcount n d ≤ Module.finrank (ZMod 3) W + #(Bᶜ) := by
    have h := finrank_inf_ker_ge (polySpace n d) fmap
    rw [finrank_polySpace, hcodim] at h
    exact h
  obtain ⟨P, hPW, hPsupp⟩ := exists_large_support W
  have hPpoly : P ∈ polySpace n d := hPW.1
  have hPvanish : ∀ v : Pt n, v ∉ B → P v = 0 := by
    intro v hv
    have := congrFun (LinearMap.mem_ker.1 hPW.2) ⟨v, Finset.mem_compl.2 hv⟩
    simpa [hfmap, LinearMap.funLeft] using this
  -- the set of `a ∈ A` where the polynomial does not vanish at `2a = -a`
  set S : Finset (Pt n) := A.filter (fun a => P (-a) ≠ 0) with hS
  have hsupp_le : #{v | P v ≠ 0} ≤ #S := by
    refine Finset.card_le_card_of_injOn (fun v => -v) ?_ ?_
    · intro v hv
      have hv0 : P v ≠ 0 := by simpa using (Finset.mem_filter.1 hv).2
      have hvB : v ∈ B := by
        by_contra hc
        exact hv0 (hPvanish v hc)
      obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hvB
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · show -v ∈ A
        have hva : -v = a := by rw [← hae, neg_neg]
        rwa [hva]
      · show P (-(-v)) ≠ 0
        rwa [neg_neg]
    · intro u _ v _ h
      exact neg_injective h
  -- the functions `y ↦ P (a + y)` for `a ∈ S` are linearly independent
  have hPaa : ∀ a ∈ S, P (a + a) ≠ 0 := by
    intro a ha
    rw [two_smul_eq_neg]
    exact (Finset.mem_filter.1 ha).2
  have hPsum : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → P (x + y) = 0 := fun x hx y hy hxy =>
    hPvanish _ (hcap x hx y hy hxy)
  have hSA : S ⊆ A := Finset.filter_subset _ _
  have hindep : LinearIndependent (ZMod 3)
      (fun a : {x // x ∈ S} => (fun y => P ((a : Pt n) + y) : Pt n → ZMod 3)) := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf a
    have hev := congrFun hcf (a : Pt n)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
    rw [Finset.sum_eq_single a] at hev
    · exact (mul_eq_zero.1 hev).resolve_right (hPaa a a.2)
    · intro b _ hba
      have hne : (b : Pt n) ≠ (a : Pt n) := fun h => hba (Subtype.ext h)
      rw [hPsum (b : Pt n) (hSA b.2) (a : Pt n) (hSA a.2) hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  -- all these functions lie in a space of dimension at most `2 * mcount n e`
  obtain ⟨q, c, hqc⟩ := exists_split d e harith2 P hPpoly
  set fs : Finset (Pt n → ZMod 3) :=
    (Dset n e).image (fun β => q β) ∪ (Dset n e).image (fun γ => mono γ) with hfs
  set U : Submodule (ZMod 3) (Pt n → ZMod 3) := Submodule.span (ZMod 3) (fs : Set (Pt n → ZMod 3))
    with hU
  have hmemU : ∀ x : Pt n, (fun y => P (x + y)) ∈ U := by
    intro x
    have hrepr : (fun y => P (x + y))
        = (∑ β ∈ Dset n e, mono β x • q β) + ∑ γ ∈ Dset n e, c γ x • mono γ := by
      funext y
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hqc x y
    rw [hrepr]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun β hβ => ?_)
      (Submodule.sum_mem _ fun γ hγ => ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by
        simp only [hfs, Finset.coe_union, Set.mem_union]
        exact Or.inl (by simpa using Finset.mem_image_of_mem (fun β => q β) hβ)))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by
        simp only [hfs, Finset.coe_union, Set.mem_union]
        exact Or.inr (by simpa using Finset.mem_image_of_mem (fun γ => mono γ) hγ)))
  have hScard : #S ≤ 2 * mcount n e := by
    have hindepU : LinearIndependent (ZMod 3)
        (fun a : {x // x ∈ S} => (⟨fun y => P ((a : Pt n) + y), hmemU (a : Pt n)⟩ : U)) := by
      refine LinearIndependent.of_comp U.subtype ?_
      exact hindep
    have h1 : Fintype.card {x // x ∈ S} ≤ Module.finrank (ZMod 3) U :=
      hindepU.fintype_card_le_finrank
    have h2 : Module.finrank (ZMod 3) U ≤ #fs := finrank_span_finset_le_card fs
    have h3 : #fs ≤ 2 * mcount n e := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have hb1 : ((Dset n e).image (fun β => q β)).card ≤ mcount n e := Finset.card_image_le
      have hb2 : ((Dset n e).image (fun γ => mono γ)).card ≤ mcount n e := Finset.card_image_le
      omega
    rw [Fintype.card_coe] at h1
    omega
  -- put everything together
  have hcompl : #(Bᶜ) + A.card = 3 ^ n := by
    have h := Finset.card_add_card_compl B
    have hcard : Fintype.card (Pt n) = 3 ^ n := by simp [Pt]
    omega
  have hpow : 3 ^ n ≤ mcount n d + mcount n e := pow_le_mcount_add harith1
  omega



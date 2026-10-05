/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## What is proved here

* `Math2.sunflower_bound` : the sunflower lemma with the classical Erdős–Rado bound, i.e. every
  family of `w`-element sets with more than `w ! * (r-1) ^ w` members contains a sunflower with
  `r` petals.
* `Math2.exists_large_sunflower_free_family` : the factor `(r-1) ^ w` in that bound is necessary,
  since for `r ≥ 2` there is a sunflower-free family of `(r-1) ^ w` sets of size `w`.

The quantitative improvement of Alweiss, Lovett, Wu and Zhang, which replaces the factor `w !` by
`(C * Real.log w) ^ w`, is *not* established here; the bound proved below is the classical one.
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A finite family `S` of finite sets is a *sunflower* if there is a *core* `K` such that any
two distinct members of `S` meet exactly in `K`. -/

theorem exists_large_sunflower_free_family (w r : ℕ) (hr : 2 ≤ r) :
    ∃ F : Finset (Finset (Fin w × Fin (r - 1))),
      (∀ A ∈ F, A.card = w) ∧ F.card = (r - 1) ^ w ∧
        ¬ ∃ S ⊆ F, S.card = r ∧ IsSunflower S := by
  classical
  refine ⟨Finset.univ.image (graphFinset (w := w) (k := r - 1)), ?_, ?_, ?_⟩
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨f, _, rfl⟩ := hA
    exact card_graphFinset f
  · rw [Finset.card_image_of_injective _ graphFinset_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  · rintro ⟨S, hSF, hScard, K, hK⟩
    -- the set of functions whose graph belongs to `S`
    set T : Finset (Fin w → Fin (r - 1)) :=
      Finset.univ.filter (fun f => graphFinset f ∈ S) with hT
    have hTS : T.image graphFinset = S := by
      ext A
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨f, hf, rfl⟩; exact hf
      · intro hA
        have := hSF hA
        rw [Finset.mem_image] at this
        obtain ⟨f, _, rfl⟩ := this
        exact ⟨f, hA, rfl⟩
    have hTcard : T.card = r := by
      have himg : (T.image graphFinset).card = T.card :=
        Finset.card_image_of_injective _ graphFinset_injective
      rw [hTS, hScard] at himg
      omega
    -- every coordinate is constant on `T`
    have hconst : ∀ i : Fin w, ∃ v : Fin (r - 1), (i, v) ∈ K := by
      intro i
      have hlt : (Finset.univ : Finset (Fin (r - 1))).card < T.card := by
        rw [hTcard, Finset.card_univ, Fintype.card_fin]; omega
      obtain ⟨f, hf, g, hg, hfg, hval⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
          (fun f _ => Finset.mem_univ (f i))
      refine ⟨f i, ?_⟩
      have hfS : graphFinset f ∈ S := by
        simpa [hT] using hf
      have hgS : graphFinset g ∈ S := by
        simpa [hT] using hg
      have hne : graphFinset f ≠ graphFinset g := fun h => hfg (graphFinset_injective h)
      have := hK _ hfS _ hgS hne
      rw [← this, Finset.mem_inter]
      exact ⟨(mem_graphFinset f i (f i)).mpr rfl, (mem_graphFinset g i (f i)).mpr hval.symm⟩
    -- hence all members of `S` are equal, contradicting `S.card = r ≥ 2`
    have hKsub : ∀ A ∈ S, K ⊆ A := by
      intro A hA
      obtain ⟨B, hB, hBA⟩ : ∃ B ∈ S, B ≠ A := by
        by_contra hcon
        push_neg at hcon
        have : S ⊆ {A} := fun B hB => Finset.mem_singleton.mpr (hcon B hB)
        have := Finset.card_le_card this
        rw [hScard, Finset.card_singleton] at this
        omega
      rw [← hK _ hA _ hB (Ne.symm hBA)]
      exact Finset.inter_subset_left
    have hall : ∀ f ∈ T, ∀ g ∈ T, f = g := by
      intro f hf g hg
      have hfS : graphFinset f ∈ S := by simpa [hT] using hf
      have hgS : graphFinset g ∈ S := by simpa [hT] using hg
      funext i
      obtain ⟨v, hv⟩ := hconst i
      have h1 : f i = v := (mem_graphFinset f i v).mp (hKsub _ hfS hv)
      have h2 : g i = v := (mem_graphFinset g i v).mp (hKsub _ hgS hv)
      rw [h1, h2]
    have hTle : T.card ≤ 1 := Finset.card_le_one.mpr hall
    omega

end Math2


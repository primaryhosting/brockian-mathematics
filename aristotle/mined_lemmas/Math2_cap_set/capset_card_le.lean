/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The cap-set bound: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have size
`o(3ⁿ)`.  This is the Croot–Lev–Pach / Ellenberg–Gijswijt theorem, proved here by the
polynomial method.
-/

open Finset

namespace Math2
namespace CapSet

instance factThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The field `𝔽₃`. -/
abbrev F := ZMod 3

/-- The vector space `𝔽₃ⁿ`. -/
abbrev V (n : ℕ) := Fin n → F

/-- Exponent vectors of reduced monomials: each exponent is `0`, `1` or `2`. -/
abbrev E (n : ℕ) := Fin n → Fin 3

/-- Total degree of a reduced monomial. -/

theorem capset_card_le {n : ℕ} (A : Finset (V n)) (hA : ThreeAPFree (A : Set (V n))) :
    A.card ≤ 3 * (M n (2 * n / 3)).card := by
  classical
  set d := 4 * n / 3 with hd
  set T : Finset (V n) := A.image (fun a => -a) with hT
  have hfrX : Module.finrank F (V n → F) = 3 ^ n := by
    rw [Module.finrank_fintype_fun_eq_card]; simp
  have hTcard : T.card = A.card := Finset.card_image_of_injective _ neg_injective
  have hAle : A.card ≤ 3 ^ n := by
    have h : A.card ≤ Fintype.card (V n) := Finset.card_le_univ A
    simpa using h
  have hcompl : Fintype.card {x : V n // x ∉ T} = 3 ^ n - A.card := by
    rw [Fintype.card_subtype]
    have h : (Finset.univ.filter (fun x : V n => x ∉ T)) = Tᶜ := by ext x; simp
    rw [h, Finset.card_compl, hTcard]
    simp
  -- lower bound for the dimension of `W n d ⊓ ker`
  have hKrank : 3 ^ n ≤ Module.finrank F ↥(LinearMap.ker (restrMap T)) + (3 ^ n - A.card) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (restrMap T)
    have h2 : Module.finrank F ↥(LinearMap.range (restrMap T)) ≤ 3 ^ n - A.card := by
      have h3 := Submodule.finrank_le (LinearMap.range (restrMap T))
      rwa [Module.finrank_fintype_fun_eq_card, hcompl] at h3
    rw [hfrX] at h1
    omega
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq (W n d) (LinearMap.ker (restrMap T))
  have hsuple : Module.finrank F ↥(W n d ⊔ LinearMap.ker (restrMap T)) ≤ 3 ^ n := by
    have h := Submodule.finrank_le (W n d ⊔ LinearMap.ker (restrMap T))
    rwa [hfrX] at h
  have hWrank : (M n d).card ≤ Module.finrank F ↥(W n d) := card_M_le_finrank_W n d
  have hWsrank : (M n d).card
      ≤ Module.finrank F ↥(W n d ⊓ LinearMap.ker (restrMap T)) + (3 ^ n - A.card) := by
    omega
  -- a polynomial with large support
  obtain ⟨P, hPmem, hPsupp⟩ := exists_large_support (W n d ⊓ LinearMap.ker (restrMap T))
  have hPW : P ∈ W n d := hPmem.1
  have hPK : ∀ x : V n, x ∉ T → P x = 0 := by
    intro x hx
    have h : (restrMap T) P = 0 := hPmem.2
    exact congrFun h ⟨x, hx⟩
  set S : Finset (V n) := A.filter (fun x => P (x + x) ≠ 0) with hS
  -- the support of `P` is contained in `-S`
  have hsuppS : (Finset.univ.filter (fun x : V n => P x ≠ 0)).card ≤ S.card := by
    have hsub : (Finset.univ.filter (fun x : V n => P x ≠ 0)) ⊆ S.image (fun a => -a) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      by_cases hxT : x ∈ T
      · rw [hT] at hxT
        obtain ⟨a, haA, hax⟩ := Finset.mem_image.1 hxT
        refine Finset.mem_image.2 ⟨a, ?_, hax⟩
        rw [hS, Finset.mem_filter]
        refine ⟨haA, ?_⟩
        rw [neg_eq_add_self a, hax]
        exact hx
      · exact absurd (hPK x hxT) hx
    calc (Finset.univ.filter (fun x : V n => P x ≠ 0)).card ≤ (S.image (fun a => -a)).card :=
          Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
  -- the rank bound applies to `S`
  have hSbound : S.card ≤ 2 * (M n (d / 2)).card := by
    refine rank_bound (clp_mem hPW) ?_ ?_
    · intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact hx.2
    · intro x hx y hy hne
      by_contra hxy
      have hxT : x + y ∈ T := by
        by_contra hnot
        exact hxy (hPK _ hnot)
      rw [hT] at hxT
      obtain ⟨c, hcA, hc⟩ := Finset.mem_image.1 hxT
      have hxA : x ∈ A := (Finset.mem_filter.1 (hS ▸ hx)).1
      have hyA : y ∈ A := (Finset.mem_filter.1 (hS ▸ hy)).1
      have hsum : x + y = c + c := by rw [neg_eq_add_self c, hc]
      have h1 : x = c := hA hxA hcA hyA hsum
      have h2 : y = c := hA hyA hcA hxA (by rw [add_comm]; exact hsum)
      exact hne (h1.trans h2.symm)
  -- putting things together
  have hde : d / 2 ≤ 2 * n / 3 := by omega
  have hMe : (M n (d / 2)).card ≤ (M n (2 * n / 3)).card :=
    Finset.card_le_card (M_mono hde)
  have hcompM : 3 ^ n ≤ (M n d).card + (M n (2 * n / 3)).card := by
    have h1 : (Finset.univ \ M n d).card ≤ (M n (2 * n / 3)).card := card_compl_M_le
    have h2 : (Finset.univ \ M n d).card + (M n d).card = (Finset.univ : Finset (E n)).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
    have h4 : (Finset.univ : Finset (E n)).card = 3 ^ n := by
      simp
    omega
  omega

end Main

section Counting

/-- The generating identity `∑_a (1/2)^{deg a} = (7/4)^n`. -/

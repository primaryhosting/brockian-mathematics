/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math2

/-- The **Erdős–Ko–Rado theorem** for families of subsets of `[n] = {0, 1, ..., n-1}`.

If `𝒜` is a family of `k`-element subsets of `Finset.range n` that is intersecting (any two
members, including a member with itself, meet), and `n ≥ 2 * k`, then `#𝒜 ≤ (n-1).choose (k-1)`.

The proof transfers the statement to `Finset (Fin n)` and applies Mathlib's
`Finset.erdos_ko_rado` (proved there via the Kruskal–Katona theorem). -/
theorem erdos_ko_rado {n k : ℕ} {𝒜 : Finset (Finset ℕ)}
    (hsub : ∀ A ∈ 𝒜, A ⊆ Finset.range n)
    (hcard : ∀ A ∈ 𝒜, A.card = k)
    (hint : ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty)
    (hn : 2 * k ≤ n) :
    𝒜.card ≤ (n - 1).choose (k - 1) := by
  classical
  -- The corresponding family of subsets of `Fin n`.
  set ℬ : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B : Finset (Fin n) => B.image Fin.val ∈ 𝒜) with hℬ
  have hmemℬ : ∀ B : Finset (Fin n), B ∈ ℬ ↔ B.image Fin.val ∈ 𝒜 := by
    intro B; simp [hℬ]
  -- `B ↦ B.image Fin.val` maps `ℬ` bijectively onto `𝒜`.
  have himg : ℬ.image (fun B : Finset (Fin n) => B.image Fin.val) = 𝒜 := by
    ext A
    constructor
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hA
      exact (hmemℬ B).1 hB
    · intro hA
      refine Finset.mem_image.2 ⟨A.attachFin (fun m hm => Finset.mem_range.1 (hsub A hA hm)), ?_, ?_⟩
      · rw [hmemℬ, Finset.image_val_attachFin]
        exact hA
      · exact Finset.image_val_attachFin _
  have hinj : Set.InjOn (fun B : Finset (Fin n) => B.image Fin.val) ℬ := by
    intro B _ C _ h
    exact Finset.image_injective Fin.val_injective h
  have hcards : 𝒜.card = ℬ.card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  -- Transfer the hypotheses.
  have hsized : (ℬ : Set (Finset (Fin n))).Sized k := by
    intro B hB
    have hB' : B.image Fin.val ∈ 𝒜 := (hmemℬ B).1 hB
    have := hcard _ hB'
    rwa [Finset.card_image_of_injective _ Fin.val_injective] at this
  have hinter : (ℬ : Set (Finset (Fin n))).Intersecting := by
    intro B hB C hC hdisj
    have hB' : B.image Fin.val ∈ 𝒜 := (hmemℬ B).1 hB
    have hC' : C.image Fin.val ∈ 𝒜 := (hmemℬ C).1 hC
    obtain ⟨x, hx⟩ := hint _ hB' _ hC'
    rw [Finset.mem_inter] at hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx.1
    obtain ⟨c, hc, hbc⟩ := Finset.mem_image.1 hx.2
    have : c = b := Fin.val_injective hbc
    subst this
    exact Finset.disjoint_left.1 hdisj hb hc
  have hk : k ≤ n / 2 := by omega
  rw [hcards]
  exact Finset.erdos_ko_rado hinter hsized hk

/-- The star family of all `k`-subsets of `[n]` containing the element `0`. -/
def star (n k : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range n).powersetCard k).filter (fun A => 0 ∈ A)

lemma mem_star {n k : ℕ} {A : Finset ℕ} :
    A ∈ star n k ↔ (A ⊆ Finset.range n ∧ A.card = k) ∧ 0 ∈ A := by
  simp [star, Finset.mem_powersetCard, and_assoc]

lemma card_star {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (star n k).card = (n - 1).choose (k - 1) := by
  classical
  have hbij : (star n k).card = ((Finset.Ico 1 n).powersetCard (k - 1)).card := by
    refine Finset.card_bij (fun A _ => A.erase 0) ?_ ?_ ?_
    · intro A hA
      rw [mem_star] at hA
      obtain ⟨⟨hsub, hcard⟩, hzero⟩ := hA
      rw [Finset.mem_powersetCard]
      refine ⟨fun x hx => ?_, ?_⟩
      · have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
        have hxn : x < n := Finset.mem_range.1 (hsub (Finset.mem_of_mem_erase hx))
        exact Finset.mem_Ico.2 ⟨Nat.one_le_iff_ne_zero.2 hx0, hxn⟩
      · rw [Finset.card_erase_of_mem hzero, hcard]
    · intro A hA B hB hAB
      rw [mem_star] at hA hB
      have := congrArg (insert 0) hAB
      rwa [Finset.insert_erase hA.2, Finset.insert_erase hB.2] at this
    · intro B hB
      rw [Finset.mem_powersetCard] at hB
      obtain ⟨hsub, hcard⟩ := hB
      have hzero : 0 ∉ B := fun h => by simpa using (Finset.mem_Ico.1 (hsub h)).1
      refine ⟨insert 0 B, ?_, ?_⟩
      · rw [mem_star]
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Finset.mem_range.2 hn
          · exact Finset.mem_range.2 (Finset.mem_Ico.1 (hsub hx)).2
        · rw [Finset.card_insert_of_notMem hzero, hcard]
          omega
      · show (insert 0 B).erase 0 = B
        exact Finset.erase_insert hzero
  rw [hbij, Finset.card_powersetCard, Nat.card_Ico]

/-- **Sharpness of Erdős–Ko–Rado**: for `1 ≤ k` the star family (all `k`-subsets of `[n]`
containing a fixed element) is an intersecting `k`-uniform family of subsets of `[n]`
attaining the bound `(n-1).choose (k-1)`. -/
theorem erdos_ko_rado_sharp {n k : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (∀ A ∈ star n k, A ⊆ Finset.range n) ∧ (∀ A ∈ star n k, A.card = k) ∧
      (∀ A ∈ star n k, ∀ B ∈ star n k, (A ∩ B).Nonempty) ∧
      (star n k).card = (n - 1).choose (k - 1) := by
  refine ⟨fun A hA => (mem_star.1 hA).1.1, fun A hA => (mem_star.1 hA).1.2, ?_, card_star hk hn⟩
  intro A hA B hB
  exact ⟨0, Finset.mem_inter.2 ⟨(mem_star.1 hA).2, (mem_star.1 hB).2⟩⟩

end Math2


import Mathlib

/-!
# Orbits of a permutation

Minimal theory of orbits of a permutation of a finite type, as needed for face counting in a
combinatorial embedding of a graph: a permutation all of whose orbits have at least `n` elements
has at most `#α / n` orbits.
-/

namespace Frontier

variable {α : Type*}

/-- The setoid on `α` whose equivalence classes are the orbits of the permutation `f`. -/

theorem numOrbits_mul_le [Finite α] (f : Equiv.Perm α) (n : ℕ)
    (h : ∀ (a : α) (i : ℕ), 0 < i → i < n → (f ^ i) a ≠ a) :
    n * numOrbits f ≤ Nat.card α := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fintype (Quotient (orbitSetoid f)) := Quotient.fintype _
  have key : ∀ b : Quotient (orbitSetoid f),
      n ≤ (Finset.univ.filter (fun a : α => Quotient.mk (orbitSetoid f) a = b)).card := by
    intro b
    obtain ⟨a, rfl⟩ := Quotient.exists_rep b
    have hne : ∀ i j : ℕ, i < j → j < n → (f ^ i) a ≠ (f ^ j) a := by
      intro i j hlt hj hij
      have hcomp : (f ^ i) ((f ^ (j - i)) a) = (f ^ j) a := by
        rw [← Equiv.Perm.mul_apply, ← pow_add]
        congr 2
        omega
      exact h a (j - i) (by omega) (by omega) ((f ^ i).injective (hcomp.trans hij.symm))
    have hinj : Set.InjOn (fun i : ℕ => (f ^ i) a) (Finset.range n) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      simp only at hij
      by_contra hij'
      rcases lt_or_gt_of_ne hij' with hlt | hlt
      · exact hne i j hlt hj hij
      · exact hne j i hlt hi hij.symm
    have hsub : ((Finset.range n).image (fun i : ℕ => (f ^ i) a)) ⊆
        Finset.univ.filter (fun x : α => Quotient.mk (orbitSetoid f) x = Quotient.mk _ a) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Quotient.sound
      refine ⟨-(i : ℤ), ?_⟩
      rw [← Equiv.Perm.mul_apply, ← zpow_natCast f i, ← zpow_add]
      simp
    calc n = ((Finset.range n).image (fun i : ℕ => (f ^ i) a)).card := by
            rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun a : α => Quotient.mk (orbitSetoid f) a) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_univ _)
  simp only [numOrbits, Nat.card_eq_fintype_card, ← Finset.card_univ]
  rw [hfib]
  calc n * (Finset.univ : Finset (Quotient (orbitSetoid f))).card
      = ∑ _b : Quotient (orbitSetoid f), n := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun b _ => key b)

/-- If every orbit of `f` has at least three elements then `f` has at most `#α / 3` orbits. -/

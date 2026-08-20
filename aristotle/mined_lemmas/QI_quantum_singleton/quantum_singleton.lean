import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

theorem quantum_singleton {k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (Q : QCode q n (q ^ k) d) :
    k + 2 * (d - 1) ≤ n := by
  have hq0 : 0 < q := by omega
  have hK : 0 < q ^ k := Nat.pow_pos hq0
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · have h := dim_le_ambient Q
    have : k ≤ n := (Nat.pow_le_pow_iff_right hq).mp h
    omega
  set m := d - 1 with hm
  by_cases hcase : 2 * m ≤ n
  · obtain ⟨SA, -, hSA⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := m)
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    have hcompl : ((Finset.univ : Finset (Fin n)) \ SA).card = n - m := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hSA]
      simp
    obtain ⟨SB, hsub, hSB⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n)) \ SA) (n := m) (by rw [hcompl]; omega)
    have hdisj : Disjoint SA SB :=
      Finset.disjoint_left.mpr fun x hx hxB => (Finset.mem_sdiff.mp (hsub hxB)).2 hx
    have hle := dim_le_of_two_regions Q hK SA SB hdisj (by omega) (by omega)
    rw [hSA, hSB] at hle
    have : k ≤ n - m - m := (Nat.pow_le_pow_iff_right hq).mp hle
    omega
  · exfalso
    obtain ⟨SA, -, hSA⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := min m n)
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    have hcompl : ((Finset.univ : Finset (Fin n)) \ SA).card = n - min m n := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hSA]
      simp
    obtain ⟨SB, hsub, hSB⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n)) \ SA) (n := n - min m n) (by rw [hcompl])
    have hdisj : Disjoint SA SB :=
      Finset.disjoint_left.mpr fun x hx hxB => (Finset.mem_sdiff.mp (hsub hxB)).2 hx
    have hle := dim_le_of_two_regions Q hK SA SB hdisj (by omega) (by omega)
    rw [hSA, hSB] at hle
    have hz : n - min m n - (n - min m n) = 0 := by omega
    rw [hz, pow_zero] at hle
    have : k ≤ 0 := (Nat.pow_le_pow_iff_right hq).mp (by simpa using hle)
    omega

/-- Extending an operator supported on no qudits at all just rescales the identity. -/

import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/
def distinctSets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter fun S => ∑ i ∈ S, i = n

lemma mem_distinctSets {n : ℕ} {S : Finset ℕ} :
    S ∈ distinctSets n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n) := by
  simp only [distinctSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hsub, hsum⟩
    refine ⟨fun h0 => ?_, hsum⟩
    have := hsub h0
    simp at this
  · rintro ⟨h0, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have h1 : 1 ≤ x := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact h0 hx)
    have h2 : x ≤ n := hsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp [Finset.mem_Icc, h1, h2]

/-- The coefficient predicted by Euler's pentagonal number theorem. -/
def pentSign (n : ℕ) : ℤ :=
  (if n = 0 then 1 else 0)
  + ∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a - 1) then ((-1 : ℤ)) ^ a else 0)
  + ∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a + 1) then ((-1 : ℤ)) ^ a else 0)

/-! ## Franklin's involution -/

/-- Largest element of a finset of naturals (`0` if empty). -/
def mx (S : Finset ℕ) : ℕ := S.max.getD 0

/-- Smallest element of a finset of naturals (`0` if empty). -/
def mn (S : Finset ℕ) : ℕ := S.min.getD 0

/-- Length of the "staircase" `mx S, mx S - 1, …` contained in `S`. -/
noncomputable def stair (S : Finset ℕ) : ℕ := sInf {j | mx S - j ∉ S}

/-- Franklin's map. -/
noncomputable def franklin (S : Finset ℕ) : Finset ℕ :=
  if mn S ≤ stair S then insert (mx S + 1) ((S.erase (mn S)).erase (mx S - mn S + 1))
  else insert (stair S) (insert (mx S - stair S) (S.erase (mx S)))

/-- The exceptional (fixed) configurations of Franklin's involution. -/
def IsExc (S : Finset ℕ) : Prop :=
  S = ∅ ∨ ∃ a, 1 ≤ a ∧ (S = Finset.Icc a (2 * a - 1) ∨ S = Finset.Icc (a + 1) (2 * a))

noncomputable instance : DecidablePred IsExc := fun _ => Classical.propDecidable _

/-! ### Basic facts about `mx`, `mn`, `stair` -/

lemma mx_eq {S : Finset ℕ} (hne : S.Nonempty) : mx S = S.max' hne := by
  rw [mx, ← Finset.coe_max' hne]; rfl

lemma mn_eq {S : Finset ℕ} (hne : S.Nonempty) : mn S = S.min' hne := by
  rw [mn, ← Finset.coe_min' hne]; rfl

lemma mx_mem {S : Finset ℕ} (hne : S.Nonempty) : mx S ∈ S := by
  rw [mx_eq hne]; exact S.max'_mem hne

lemma le_mx {S : Finset ℕ} {x : ℕ} (h : x ∈ S) : x ≤ mx S := by
  rw [mx_eq ⟨x, h⟩]; exact Finset.le_max' S x h

lemma mn_mem {S : Finset ℕ} (hne : S.Nonempty) : mn S ∈ S := by
  rw [mn_eq hne]; exact S.min'_mem hne

lemma mn_le {S : Finset ℕ} {x : ℕ} (h : x ∈ S) : mn S ≤ x := by
  rw [mn_eq ⟨x, h⟩]; exact Finset.min'_le S x h

lemma stair_notMem {S : Finset ℕ} (h0 : 0 ∉ S) : mx S - stair S ∉ S :=
  Nat.sInf_mem (⟨mx S, by simpa using h0⟩ : {j | mx S - j ∉ S}.Nonempty)

lemma mem_of_lt_stair {S : Finset ℕ} {i : ℕ} (h : i < stair S) : mx S - i ∈ S := by
  have := Nat.notMem_of_lt_sInf h
  simpa using this

lemma stair_le {S : Finset ℕ} {i : ℕ} (h : mx S - i ∉ S) : stair S ≤ i := Nat.sInf_le h

lemma le_stair {S : Finset ℕ} {c : ℕ} (h0 : 0 ∉ S) (h : ∀ i < c, mx S - i ∈ S) : c ≤ stair S := by
  by_contra hc
  push_neg at hc
  exact stair_notMem h0 (h _ hc)

lemma stair_pos {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) : 1 ≤ stair S := by
  rcases Nat.eq_zero_or_pos (stair S) with h | h
  · exact absurd (mx_mem hne) (by simpa [h] using stair_notMem (S := S) h0)
  · exact h

lemma stair_le_mx {S : Finset ℕ} (h0 : 0 ∉ S) : stair S ≤ mx S :=
  stair_le (by simpa using h0)

lemma mn_le_mx_sub_stair {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) :
    mn S ≤ mx S - stair S + 1 := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have h3 : mx S - (stair S - 1) ∈ S := mem_of_lt_stair (by omega)
  have := mn_le h3
  omega

/-! ### The exceptional sets -/

lemma mx_Icc {a b : ℕ} (h : a ≤ b) : mx (Finset.Icc a b) = b := by
  have hb : b ∈ Finset.Icc a b := by simp [Finset.mem_Icc, h]
  refine le_antisymm ?_ (le_mx hb)
  have := mx_mem (⟨b, hb⟩ : (Finset.Icc a b).Nonempty)
  rw [Finset.mem_Icc] at this
  exact this.2

lemma mn_Icc {a b : ℕ} (h : a ≤ b) : mn (Finset.Icc a b) = a := by
  have hb : a ∈ Finset.Icc a b := by simp [Finset.mem_Icc, h]
  refine le_antisymm (mn_le hb) ?_
  have := mn_mem (⟨a, hb⟩ : (Finset.Icc a b).Nonempty)
  rw [Finset.mem_Icc] at this
  exact this.1

lemma zero_notMem_Icc {a b : ℕ} (ha : 1 ≤ a) : 0 ∉ Finset.Icc a b := by
  intro hmem
  rw [Finset.mem_Icc] at hmem
  omega

lemma stair_Icc {a b : ℕ} (h : a ≤ b) (ha : 1 ≤ a) : stair (Finset.Icc a b) = b + 1 - a := by
  have hmx : mx (Finset.Icc a b) = b := mx_Icc h
  refine le_antisymm (stair_le ?_) (le_stair (zero_notMem_Icc ha) ?_)
  · rw [hmx]
    intro hmem
    rw [Finset.mem_Icc] at hmem
    omega
  · intro i hi
    rw [hmx, Finset.mem_Icc]
    omega

/-- If `S` is not exceptional and we are in the first Franklin case, the move is legal. -/
lemma caseA_ne {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hexc : ¬ IsExc S) : mn S ≠ mx S - mn S + 1 := by
  intro heq
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ hm))
  have h2 : mn S ≤ mx S := le_mx hm
  refine hexc (Or.inr ⟨mn S, h1, Or.inl ?_⟩)
  have hMx : mx S = 2 * mn S - 1 := by omega
  ext x
  simp only [Finset.mem_Icc]
  constructor
  · exact fun hx => ⟨mn_le hx, by rw [← hMx]; exact le_mx hx⟩
  · rintro ⟨hx1, hx2⟩
    have hx2' : x ≤ mx S := by omega
    have : mx S - (mx S - x) ∈ S := mem_of_lt_stair (by omega)
    have heq2 : mx S - (mx S - x) = x := by omega
    rwa [heq2] at this

/-- If `S` is not exceptional and we are in the second Franklin case, the move is legal. -/
lemma caseB_ne {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hexc : ¬ IsExc S) : mx S ≠ 2 * stair S := by
  intro heq
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have h3 : mn S ≤ mx S - stair S + 1 := mn_le_mx_sub_stair hne h0
  refine hexc (Or.inr ⟨stair S, h1, Or.inr ?_⟩)
  ext x
  simp only [Finset.mem_Icc]
  constructor
  · exact fun hx => ⟨by have := mn_le hx; omega, by rw [← heq]; exact le_mx hx⟩
  · rintro ⟨hx1, hx2⟩
    have : mx S - (mx S - x) ∈ S := mem_of_lt_stair (by omega)
    have heq2 : mx S - (mx S - x) = x := by omega
    rwa [heq2] at this

lemma caseB_franklin {S : Finset ℕ} (hB : stair S < mn S) :
    franklin S = insert (stair S) (insert (mx S - stair S) (S.erase (mx S))) := by
  rw [franklin, if_neg (by omega)]

/-! ### Case A of the involution -/

section CaseA

variable {S : Finset ℕ}

lemma one_le_mn (hne : S.Nonempty) (h0 : 0 ∉ S) : 1 ≤ mn S :=
  Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ mn_mem hne))

lemma caseA_mem_top (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S) :
    mx S - mn S + 1 ∈ S := by
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have hmem := mem_of_lt_stair (S := S) (i := mn S - 1) (by omega)
  have h3 : mx S - (mn S - 1) = mx S - mn S + 1 := by omega
  rwa [h3] at hmem

lemma caseA_lt (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : mn S < mx S - mn S + 1 :=
  lt_of_le_of_ne (mn_le (caseA_mem_top hne h0 hA)) hne2

lemma caseA_franklin (hA : mn S ≤ stair S) :
    franklin S = insert (mx S + 1) ((S.erase (mn S)).erase (mx S - mn S + 1)) := if_pos hA

lemma caseA_top_mem_erase (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : mx S - mn S + 1 ∈ S.erase (mn S) :=
  Finset.mem_erase.2 ⟨fun h => hne2 h.symm, caseA_mem_top hne h0 hA⟩

lemma caseA_succ_notMem :
    mx S + 1 ∉ (S.erase (mn S)).erase (mx S - mn S + 1) := by
  intro h
  have hS : mx S + 1 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
  have := le_mx hS
  omega

lemma caseA_sum (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) :
    ∑ i ∈ franklin S, i = ∑ i ∈ S, i := by
  have hm : mn S ∈ S := mn_mem hne
  have h2 : mn S ≤ mx S := le_mx hm
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  rw [caseA_franklin hA, Finset.sum_insert (caseA_succ_notMem)]
  have e1 : mn S + ∑ i ∈ S.erase (mn S), i = ∑ i ∈ S, i :=
    Finset.add_sum_erase S (fun i => i) hm
  have e2 : (mx S - mn S + 1) + ∑ i ∈ (S.erase (mn S)).erase (mx S - mn S + 1), i
      = ∑ i ∈ S.erase (mn S), i := Finset.add_sum_erase _ (fun i => i) ht'
  omega

lemma caseA_zero (h0 : 0 ∉ S) (hA : mn S ≤ stair S) : 0 ∉ franklin S := by
  rw [caseA_franklin hA]
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))

lemma caseA_card (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) :
    (franklin S).card + 1 = S.card := by
  have hm : mn S ∈ S := mn_mem hne
  have ht : mx S - mn S + 1 ∈ S := caseA_mem_top hne h0 hA
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  have h2 : 2 ≤ S.card :=
    Finset.one_lt_card.2 ⟨mn S, hm, mx S - mn S + 1, ht, hne2⟩
  rw [caseA_franklin hA, Finset.card_insert_of_notMem (caseA_succ_notMem),
    Finset.card_erase_of_mem ht', Finset.card_erase_of_mem hm]
  omega

lemma caseA_mem_succ (hA : mn S ≤ stair S) : mx S + 1 ∈ franklin S := by
  rw [caseA_franklin hA]; exact Finset.mem_insert_self _ _

lemma caseA_mx (hA : mn S ≤ stair S) : mx (franklin S) = mx S + 1 := by
  have hmem := caseA_mem_succ (S := S) hA
  refine le_antisymm ?_ (le_mx hmem)
  have hall : ∀ x ∈ franklin S, x ≤ mx S + 1 := by
    intro x hx
    rw [caseA_franklin hA] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    · have := le_mx (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
      omega
  exact hall _ (mx_mem ⟨_, hmem⟩)

lemma caseA_mn (hne : S.Nonempty) (hA : mn S ≤ stair S) : mn S < mn (franklin S) := by
  have hm : mn S ∈ S := mn_mem hne
  have h2 : mn S ≤ mx S := le_mx hm
  have hall : ∀ x ∈ franklin S, mn S < x := by
    intro x hx
    rw [caseA_franklin hA] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    · have hxS : x ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
      have hxne : x ≠ mn S := (Finset.mem_erase.1 (Finset.mem_of_mem_erase h)).1
      have := mn_le hxS
      omega
  exact hall _ (mn_mem ⟨_, caseA_mem_succ (S := S) hA⟩)

lemma caseA_stair (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : stair (franklin S) = mn S := by
  have hmx := caseA_mx hA
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have hlt : mn S < mx S - mn S + 1 := caseA_lt hne h0 hA hne2
  refine le_antisymm ?_ ?_
  · refine stair_le ?_
    rw [hmx]
    have he : mx S + 1 - mn S = mx S - mn S + 1 := by omega
    rw [he, caseA_franklin hA]
    intro hmem
    rcases Finset.mem_insert.1 hmem with h | h
    · omega
    · exact (Finset.notMem_erase _ _) h
  · refine le_stair (caseA_zero h0 hA) ?_
    intro i hi
    rw [hmx, caseA_franklin hA]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp
    · have hmem : mx S - (i - 1) ∈ S := mem_of_lt_stair (by omega)
      have heq : mx S + 1 - i = mx S - (i - 1) := by omega
      rw [heq]
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨by omega, Finset.mem_erase.2 ⟨by omega, hmem⟩⟩)

lemma caseA_inv (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : franklin (franklin S) = S := by
  have hmx := caseA_mx hA
  have hst := caseA_stair hne h0 hA hne2
  have hmn := caseA_mn hne hA
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  rw [caseB_franklin (S := franklin S) (by omega), hmx, hst]
  have e1 : (franklin S).erase (mx S + 1) = (S.erase (mn S)).erase (mx S - mn S + 1) := by
    rw [caseA_franklin hA, Finset.erase_insert (caseA_succ_notMem)]
  have e2 : mx S + 1 - mn S = mx S - mn S + 1 := by omega
  rw [e1, e2, Finset.insert_erase ht', Finset.insert_erase hm]

lemma caseA_notExc (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : ¬ IsExc (franklin S) := by
  have hmx := caseA_mx hA
  have hst := caseA_stair hne h0 hA hne2
  have hmn := caseA_mn hne hA
  have hlt : mn S < mx S - mn S + 1 := caseA_lt hne h0 hA hne2
  have h2 : mn S ≤ mx S := le_mx (mn_mem hne)
  rintro (h | ⟨c, hc, h | h⟩)
  · have hmem := caseA_mem_succ (S := S) hA
    rw [h] at hmem
    simp at hmem
  · have hle : c ≤ 2 * c - 1 := by omega
    have h1 : mn (franklin S) = c := by rw [h, mn_Icc hle]
    have h3 : stair (franklin S) = c := by rw [h, stair_Icc hle hc]; omega
    omega
  · have hle : c + 1 ≤ 2 * c := by omega
    have h3 : stair (franklin S) = c := by rw [h, stair_Icc hle (by omega)]; omega
    have h4 : mx (franklin S) = 2 * c := by rw [h, mx_Icc hle]
    omega

end CaseA

/-! ### Case B of the involution -/

section CaseB

variable {S : Finset ℕ}

lemma caseB_lt (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : stair S < mx S - stair S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have h3 : mn S ≤ mx S - stair S + 1 := mn_le_mx_sub_stair hne h0
  omega

lemma caseB_stair_notMem (hB : stair S < mn S) : stair S ∉ S :=
  fun h => absurd (mn_le h) (by omega)

lemma caseB_ins_notMem (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) :
    stair S ∉ insert (mx S - stair S) (S.erase (mx S)) := by
  have hlt := caseB_lt hne h0 hB hne2
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact caseB_stair_notMem hB (Finset.mem_of_mem_erase h)

lemma caseB_sub_notMem (h0 : 0 ∉ S) : mx S - stair S ∉ S.erase (mx S) :=
  fun h => stair_notMem h0 (Finset.mem_of_mem_erase h)

lemma caseB_sum (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) :
    ∑ i ∈ franklin S, i = ∑ i ∈ S, i := by
  have h2 : stair S ≤ mx S := stair_le_mx h0
  rw [caseB_franklin hB, Finset.sum_insert (caseB_ins_notMem hne h0 hB hne2),
    Finset.sum_insert (caseB_sub_notMem h0)]
  have e1 : mx S + ∑ i ∈ S.erase (mx S), i = ∑ i ∈ S, i :=
    Finset.add_sum_erase S (fun i => i) (mx_mem hne)
  omega

lemma caseB_zero (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : 0 ∉ franklin S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have hlt := caseB_lt hne h0 hB hne2
  rw [caseB_franklin hB]
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact h0 (Finset.mem_of_mem_erase h)

lemma caseB_card (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : (franklin S).card = S.card + 1 := by
  have h1 : 1 ≤ S.card := Finset.card_pos.2 hne
  rw [caseB_franklin hB, Finset.card_insert_of_notMem (caseB_ins_notMem hne h0 hB hne2),
    Finset.card_insert_of_notMem (caseB_sub_notMem h0), Finset.card_erase_of_mem (mx_mem hne)]
  omega

lemma caseB_mx (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : mx (franklin S) = mx S - 1 := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmem : mx S - 1 ∈ franklin S := by
    rw [caseB_franklin hB]
    rcases Nat.lt_or_ge 1 (stair S) with h | h
    · have hmS : mx S - 1 ∈ S := mem_of_lt_stair (S := S) (i := 1) h
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨by omega, hmS⟩))
    · have : mx S - stair S = mx S - 1 := by omega
      rw [← this]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  refine le_antisymm ?_ (le_mx hmem)
  have hall : ∀ x ∈ franklin S, x ≤ mx S - 1 := by
    intro x hx
    rw [caseB_franklin hB] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have hxS : x ∈ S := Finset.mem_of_mem_erase h
      have hxne : x ≠ mx S := (Finset.mem_erase.1 h).1
      have := le_mx hxS
      omega
  exact hall _ (mx_mem ⟨_, hmem⟩)

lemma caseB_mn (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : mn (franklin S) = stair S := by
  have hlt := caseB_lt hne h0 hB hne2
  have hmem : stair S ∈ franklin S := by
    rw [caseB_franklin hB]; exact Finset.mem_insert_self _ _
  refine le_antisymm (mn_le hmem) ?_
  have hall : ∀ x ∈ franklin S, stair S ≤ x := by
    intro x hx
    rw [caseB_franklin hB] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have := mn_le (Finset.mem_of_mem_erase h)
      omega
  exact hall _ (mn_mem ⟨_, hmem⟩)

lemma caseB_stair (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : stair S ≤ stair (franklin S) := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  refine le_stair (caseB_zero hne h0 hB hne2) ?_
  intro i hi
  rw [hmx, caseB_franklin hB]
  rcases Nat.lt_or_ge (i + 1) (stair S) with h | h
  · have hmS : mx S - (i + 1) ∈ S := mem_of_lt_stair h
    have heq : mx S - 1 - i = mx S - (i + 1) := by omega
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.2 ⟨by omega, hmS⟩))
  · have heq : mx S - 1 - i = mx S - stair S := by omega
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

lemma caseB_inv (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : franklin (franklin S) = S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  have hmn := caseB_mn hne h0 hB hne2
  have hst := caseB_stair hne h0 hB hne2
  rw [caseA_franklin (S := franklin S) (by omega), hmx, hmn]
  have e1 : mx S - 1 + 1 = mx S := by omega
  have e2 : mx S - 1 - stair S + 1 = mx S - stair S := by omega
  rw [e1, e2]
  have e3 : (franklin S).erase (stair S) = insert (mx S - stair S) (S.erase (mx S)) := by
    rw [caseB_franklin hB, Finset.erase_insert (caseB_ins_notMem hne h0 hB hne2)]
  rw [e3, Finset.erase_insert (caseB_sub_notMem h0), Finset.insert_erase (mx_mem hne)]

lemma caseB_notExc (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : ¬ IsExc (franklin S) := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  have hmn := caseB_mn hne h0 hB hne2
  have hst := caseB_stair hne h0 hB hne2
  rintro (h | ⟨c, hc, h | h⟩)
  · have hmem : stair S ∈ franklin S := by
      rw [caseB_franklin hB]; exact Finset.mem_insert_self _ _
    rw [h] at hmem
    simp at hmem
  · have hle : c ≤ 2 * c - 1 := by omega
    have h3 : mn (franklin S) = c := by rw [h, mn_Icc hle]
    have h4 : mx (franklin S) = 2 * c - 1 := by rw [h, mx_Icc hle]
    omega
  · have hle : c + 1 ≤ 2 * c := by omega
    have h3 : mn (franklin S) = c + 1 := by rw [h, mn_Icc hle]
    have h5 : stair (franklin S) = c := by rw [h, stair_Icc hle (by omega)]; omega
    omega

end CaseB

/-! ### The cancellation -/

/-- The exceptional distinct partitions of `n`. -/
noncomputable def excSets (n : ℕ) : Finset (Finset ℕ) :=
  (distinctSets n).filter (fun S => IsExc S)

/-- The non-exceptional distinct partitions of `n`. -/
noncomputable def nonExcSets (n : ℕ) : Finset (Finset ℕ) :=
  (distinctSets n).filter (fun S => ¬ IsExc S)

lemma mem_excSets {n : ℕ} {S : Finset ℕ} :
    S ∈ excSets n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n ∧ IsExc S) := by
  rw [excSets, Finset.mem_filter, mem_distinctSets]
  tauto

lemma mem_nonExcSets {n : ℕ} {S : Finset ℕ} :
    S ∈ nonExcSets n ↔ (0 ∉ S ∧ ∑ i ∈ S, i = n ∧ ¬ IsExc S) := by
  rw [nonExcSets, Finset.mem_filter, mem_distinctSets]
  tauto

lemma nonExcSets_facts {n : ℕ} {S : Finset ℕ} (hS : S ∈ nonExcSets n) :
    S.Nonempty ∧ 0 ∉ S ∧ ∑ i ∈ S, i = n ∧ ¬ IsExc S := by
  obtain ⟨h0, hsum, hexc⟩ := mem_nonExcSets.1 hS
  refine ⟨?_, h0, hsum, hexc⟩
  rcases Finset.eq_empty_or_nonempty S with rfl | h
  · exact absurd (Or.inl rfl) hexc
  · exact h

lemma franklin_props {n : ℕ} {S : Finset ℕ} (hS : S ∈ nonExcSets n) :
    franklin S ∈ nonExcSets n ∧ ((-1 : ℤ)) ^ (franklin S).card = -((-1 : ℤ)) ^ S.card ∧
      franklin (franklin S) = S := by
  obtain ⟨hne, h0, hsum, hexc⟩ := nonExcSets_facts hS
  rcases le_or_gt (mn S) (stair S) with hA | hB
  · have hne2 := caseA_ne hne h0 hA hexc
    refine ⟨mem_nonExcSets.2 ⟨caseA_zero h0 hA, ?_, caseA_notExc hne h0 hA hne2⟩, ?_,
      caseA_inv hne h0 hA hne2⟩
    · rw [caseA_sum hne h0 hA hne2, hsum]
    · have hc := caseA_card hne h0 hA hne2
      rw [← hc, pow_succ]
      ring
  · have hne2 := caseB_ne hne h0 hB hexc
    refine ⟨mem_nonExcSets.2 ⟨caseB_zero hne h0 hB hne2, ?_, caseB_notExc hne h0 hB hne2⟩, ?_,
      caseB_inv hne h0 hB hne2⟩
    · rw [caseB_sum hne h0 hB hne2, hsum]
    · have hc := caseB_card hne h0 hB hne2
      rw [hc, pow_succ]
      ring

lemma sum_nonExc (n : ℕ) : ∑ S ∈ nonExcSets n, ((-1 : ℤ)) ^ S.card = 0 := by
  refine Finset.sum_involution (fun S _ => franklin S) (fun S hS => ?_) (fun S hS _ => ?_)
    (fun S hS => (franklin_props hS).1) (fun S hS => (franklin_props hS).2.2)
  · show ((-1 : ℤ)) ^ S.card + ((-1 : ℤ)) ^ (franklin S).card = 0
    have := (franklin_props hS).2.1
    linarith
  · intro h
    replace h : franklin S = S := h
    have h2 := (franklin_props hS).2.1
    rw [h] at h2
    have : ((-1 : ℤ)) ^ S.card ≠ 0 := pow_ne_zero _ (by norm_num)
    apply this
    linarith

/-! ### Arithmetic of pentagonal numbers -/

lemma two_mul_sum_Icc {a b : ℕ} (h : a ≤ b + 1) :
    2 * (∑ i ∈ Finset.Icc a b, i) + a * (a - 1) = (b + 1) * b := by
  have hcons := Finset.sum_Ico_consecutive (fun i => i) (Nat.zero_le a) h
  rw [Finset.Ico_add_one_right_eq_Icc] at hcons
  have h1 := Finset.sum_range_id_mul_two a
  have h2 := Finset.sum_range_id_mul_two (b + 1)
  simp only [Nat.add_sub_cancel] at h2
  simp only [Finset.range_eq_Ico] at h1 h2 ⊢
  simp only at hcons
  omega

lemma sum_E1 (a : ℕ) (ha : 1 ≤ a) : 2 * (∑ i ∈ Finset.Icc a (2 * a - 1), i) = a * (3 * a - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have h := two_mul_sum_Icc (a := k + 1) (b := 2 * (k + 1) - 1) (by omega)
  have e0 : 2 * (k + 1) - 1 + 1 = 2 * k + 2 := by omega
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
  have e3 : k + 1 - 1 = k := by omega
  rw [e0, e1, e3] at h
  rw [e1, e2]
  nlinarith [h]

lemma sum_E2 (a : ℕ) : 2 * (∑ i ∈ Finset.Icc (a + 1) (2 * a), i) = a * (3 * a + 1) := by
  have h := two_mul_sum_Icc (a := a + 1) (b := 2 * a) (by omega)
  simp only [Nat.add_sub_cancel] at h
  nlinarith [h]

lemma card_E1 (a : ℕ) (ha : 1 ≤ a) : (Finset.Icc a (2 * a - 1)).card = a := by
  rw [Nat.card_Icc]; omega

lemma card_E2 (a : ℕ) : (Finset.Icc (a + 1) (2 * a)).card = a := by
  rw [Nat.card_Icc]; omega

lemma pent1_key (a : ℕ) (ha : 1 ≤ a) : a * (3 * a - 1) + a = 3 * a * a := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have e2 : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
  rw [e2]; ring

lemma pent1_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * (3 * a - 1) = b * (3 * b - 1)) :
    a = b := by
  have e1 := pent1_key a ha
  have e2 := pent1_key b hb
  rcases lt_trichotomy a b with hlt | heq | hlt
  · nlinarith
  · exact heq
  · nlinarith

lemma pent2_inj {a b : ℕ} (h : a * (3 * a + 1) = b * (3 * b + 1)) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hlt
  · nlinarith
  · exact heq
  · nlinarith

lemma pent_cross {a b : ℕ} (ha : 1 ≤ a) (h : a * (3 * a - 1) = b * (3 * b + 1)) : False := by
  have e1 := pent1_key a ha
  have hb2 : b * (3 * b + 1) = 3 * b * b + b := by ring
  have key : 3 * a * a = 3 * b * b + b + a := by linarith
  have key' : 3 * (a : ℤ) * a = 3 * (b : ℤ) * b + b + a := by exact_mod_cast key
  have hfac : ((a : ℤ) + b) * (3 * ((a : ℤ) - b) - 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 hfac with h1 | h1
  · omega
  · omega

lemma pent1_le {a n : ℕ} (ha : 1 ≤ a) (h : 2 * n = a * (3 * a - 1)) : a ≤ n := by
  have := pent1_key a ha
  nlinarith

lemma pent2_le {a n : ℕ} (ha : 1 ≤ a) (h : 2 * n = a * (3 * a + 1)) : a ≤ n := by
  nlinarith

/-! ### Evaluating the exceptional sum -/

lemma mem_excSets_iff {n : ℕ} {S : Finset ℕ} :
    S ∈ excSets n ↔ (S = ∅ ∧ n = 0)
      ∨ (∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a - 1) ∧ S = Finset.Icc a (2 * a - 1))
      ∨ (∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a + 1) ∧ S = Finset.Icc (a + 1) (2 * a)) := by
  rw [mem_excSets]
  constructor
  · rintro ⟨h0, hsum, (rfl | ⟨a, ha, rfl | rfl⟩)⟩
    · exact Or.inl ⟨rfl, by simpa using hsum.symm⟩
    · refine Or.inr (Or.inl ⟨a, ha, ?_, rfl⟩)
      have := sum_E1 a ha
      omega
    · refine Or.inr (Or.inr ⟨a, ha, ?_, rfl⟩)
      have := sum_E2 a
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨a, ha, h2, rfl⟩ | ⟨a, ha, h2, rfl⟩)
    · exact ⟨by simp, by simp, Or.inl rfl⟩
    · refine ⟨zero_notMem_Icc ha, ?_, Or.inr ⟨a, ha, Or.inl rfl⟩⟩
      have := sum_E1 a ha
      omega
    · refine ⟨zero_notMem_Icc (by omega), ?_, Or.inr ⟨a, ha, Or.inr rfl⟩⟩
      have := sum_E2 a
      omega

lemma pentSign_eq {n : ℕ} (hn : n ≠ 0) :
    pentSign n = (∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a - 1) then ((-1 : ℤ)) ^ a else 0))
      + ∑ a ∈ Finset.Icc 1 n, (if 2 * n = a * (3 * a + 1) then ((-1 : ℤ)) ^ a else 0) := by
  rw [pentSign, if_neg hn, zero_add]

lemma sum_exc (n : ℕ) : ∑ S ∈ excSets n, ((-1 : ℤ)) ^ S.card = pentSign n := by
  by_cases hn : n = 0
  · subst hn
    have h : excSets 0 = {∅} := by
      ext S
      rw [mem_excSets_iff, Finset.mem_singleton]
      constructor
      · rintro (⟨rfl, -⟩ | ⟨a, ha, h2, rfl⟩ | ⟨a, ha, h2, rfl⟩)
        · rfl
        · exact absurd (pent1_key a ha) (by nlinarith)
        · exact absurd h2 (by nlinarith)
      · rintro rfl
        exact Or.inl ⟨rfl, rfl⟩
    rw [h, Finset.sum_singleton, pentSign]
    simp
  by_cases h1 : ∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a - 1)
  · obtain ⟨a, ha, h2⟩ := h1
    have han : a ≤ n := pent1_le ha h2
    have hexc : excSets n = {Finset.Icc a (2 * a - 1)} := by
      ext S
      rw [mem_excSets_iff, Finset.mem_singleton]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨b, hb, hb2, rfl⟩ | ⟨b, hb, hb2, rfl⟩)
        · exact absurd rfl hn
        · rw [pent1_inj hb ha (by omega)]
        · exact absurd (by omega : a * (3 * a - 1) = b * (3 * b + 1)) (fun h => pent_cross ha h)
      · rintro rfl
        exact Or.inr (Or.inl ⟨a, ha, h2, rfl⟩)
    rw [hexc, Finset.sum_singleton, card_E1 a ha, pentSign_eq hn]
    have s1 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b - 1) then ((-1 : ℤ)) ^ b else 0))
        = (-1 : ℤ) ^ a := by
      refine (Finset.sum_eq_single a (fun b hb hba => ?_) (fun hcon => ?_)).trans (if_pos h2)
      · refine if_neg (fun hcon => hba ?_)
        rw [Finset.mem_Icc] at hb
        exact pent1_inj hb.1 ha (by omega)
      · exact absurd (Finset.mem_Icc.2 ⟨ha, han⟩) hcon
    have s2 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b + 1) then ((-1 : ℤ)) ^ b else 0))
        = 0 := by
      refine Finset.sum_eq_zero (fun b hb => if_neg (fun hcon => ?_))
      exact pent_cross (a := a) (b := b) ha (by omega)
    rw [s1, s2, add_zero]
  by_cases h3 : ∃ a, 1 ≤ a ∧ 2 * n = a * (3 * a + 1)
  · obtain ⟨a, ha, h2⟩ := h3
    have han : a ≤ n := pent2_le ha h2
    have hexc : excSets n = {Finset.Icc (a + 1) (2 * a)} := by
      ext S
      rw [mem_excSets_iff, Finset.mem_singleton]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨b, hb, hb2, rfl⟩ | ⟨b, hb, hb2, rfl⟩)
        · exact absurd rfl hn
        · exact absurd ⟨b, hb, hb2⟩ h1
        · rw [pent2_inj (a := b) (b := a) (by omega)]
      · rintro rfl
        exact Or.inr (Or.inr ⟨a, ha, h2, rfl⟩)
    rw [hexc, Finset.sum_singleton, card_E2 a, pentSign_eq hn]
    have s1 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b - 1) then ((-1 : ℤ)) ^ b else 0))
        = 0 := by
      refine Finset.sum_eq_zero (fun b hb => if_neg (fun hcon => ?_))
      rw [Finset.mem_Icc] at hb
      exact h1 ⟨b, hb.1, hcon⟩
    have s2 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b + 1) then ((-1 : ℤ)) ^ b else 0))
        = (-1 : ℤ) ^ a := by
      refine (Finset.sum_eq_single a (fun b hb hba => ?_) (fun hcon => ?_)).trans (if_pos h2)
      · exact if_neg (fun hcon => hba (pent2_inj (by omega)))
      · exact absurd (Finset.mem_Icc.2 ⟨ha, han⟩) hcon
    rw [s1, s2, zero_add]
  · have hexc : excSets n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro S hS
      rcases mem_excSets_iff.1 hS with ⟨-, rfl⟩ | ⟨a, ha, h2, -⟩ | ⟨a, ha, h2, -⟩
      · exact hn rfl
      · exact h1 ⟨a, ha, h2⟩
      · exact h3 ⟨a, ha, h2⟩
    rw [hexc, Finset.sum_empty, pentSign_eq hn]
    have s1 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b - 1) then ((-1 : ℤ)) ^ b else 0))
        = 0 := by
      refine Finset.sum_eq_zero (fun b hb => if_neg (fun hcon => ?_))
      rw [Finset.mem_Icc] at hb
      exact h1 ⟨b, hb.1, hcon⟩
    have s2 : (∑ b ∈ Finset.Icc 1 n, (if 2 * n = b * (3 * b + 1) then ((-1 : ℤ)) ^ b else 0))
        = 0 := by
      refine Finset.sum_eq_zero (fun b hb => if_neg (fun hcon => ?_))
      rw [Finset.mem_Icc] at hb
      exact h3 ⟨b, hb.1, hcon⟩
    rw [s1, s2, add_zero]

/-- The combinatorial form of Euler's pentagonal number theorem: the signed count of
partitions of `n` into distinct parts. -/
theorem sum_distinctSets (n : ℕ) :
    ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card = pentSign n := by
  have h := Finset.sum_filter_add_sum_filter_not (distinctSets n) (fun S => IsExc S)
    (fun S => ((-1 : ℤ)) ^ S.card)
  rw [← h, ← excSets, ← nonExcSets, sum_nonExc, sum_exc, add_zero]

/-! ## Passing to generating functions -/

lemma coeff_prod_shifted (T : Finset ℕ) (n : ℕ) (h0 : 0 ∉ T) (hsub : Finset.Icc 1 n ⊆ T) :
    (PowerSeries.coeff n) (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have hexp : (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j))
      = ∑ t ∈ T.powerset, ((-1 : ℤ⟦X⟧)) ^ t.card * X ^ (∑ i ∈ t, i) := by
    have h := Finset.prod_add (fun j => -((X : ℤ⟦X⟧) ^ j)) (fun _ => (1 : ℤ⟦X⟧)) T
    simp only [Finset.prod_const_one, mul_one] at h
    rw [show (∏ j ∈ T, (1 - (X : ℤ⟦X⟧) ^ j)) = ∏ j ∈ T, (-((X : ℤ⟦X⟧) ^ j) + 1) from
      Finset.prod_congr rfl (fun j _ => by ring), h]
    exact Finset.sum_congr rfl (fun t _ => by rw [Finset.prod_neg, Finset.prod_pow_eq_pow_sum])
  have hcoeff : ∀ k m : ℕ, (PowerSeries.coeff (R := ℤ) n) (((-1 : ℤ⟦X⟧)) ^ k * X ^ m)
      = if m = n then ((-1 : ℤ)) ^ k else 0 := by
    intro k m
    rw [show ((-1 : ℤ⟦X⟧)) ^ k = C ((-1 : ℤ) ^ k) by rw [map_pow]; norm_num,
      PowerSeries.coeff_C_mul]
    rcases eq_or_ne m n with rfl | h
    · simp
    · rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm h), if_neg h]; ring
  rw [hexp, map_sum]
  simp only [hcoeff]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun t _ => rfl)
  ext t
  simp only [distinctSets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hT, hsum⟩
    refine ⟨fun x hx => ?_, hsum⟩
    have hx0 : x ≠ 0 := fun h => h0 (h ▸ hT hx)
    have hxn : x ≤ n := hsum ▸ Finset.single_le_sum (f := fun i => i) (fun i _ => Nat.zero_le i) hx
    simp only [Finset.mem_Icc]
    omega
  · rintro ⟨hT, hsum⟩
    exact ⟨fun x hx => hsub (hT hx), hsum⟩

lemma coeff_prod_finset (s : Finset ℕ) (n : ℕ) (hs : Finset.range n ⊆ s) :
    (PowerSeries.coeff n) (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have himg : ∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1))
      = ∏ j ∈ s.image (fun i => i + 1), (1 - (X : ℤ⟦X⟧) ^ j) := by
    rw [Finset.prod_image (fun a _ b _ h => by omega)]
  rw [himg]
  refine coeff_prod_shifted _ _ (fun h => ?_) (fun x hx => ?_)
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    omega
  · rw [Finset.mem_Icc] at hx
    refine Finset.mem_image.2 ⟨x - 1, hs (Finset.mem_range.2 (by omega)), by omega⟩

lemma coeff_tprod (n : ℕ) :
    (PowerSeries.coeff n) (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ S ∈ distinctSets n, ((-1 : ℤ)) ^ S.card := by
  have hp : HasProd (fun i : ℕ => (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) :=
    (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
  have hc := ((PowerSeries.WithPiTopology.continuous_coeff ℤ n).tendsto _).comp hp
  refine tendsto_nhds_unique hc ?_
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop (Finset.range n)] with s hs
  exact (coeff_prod_finset s n hs).symm

/-! ### The pentagonal series -/

lemma coeff_sign_X_pow (n k m : ℕ) :
    (PowerSeries.coeff (R := ℤ) n) (((-1 : ℤ⟦X⟧)) ^ k * X ^ m)
      = if m = n then ((-1 : ℤ)) ^ k else 0 := by
  rw [show ((-1 : ℤ⟦X⟧)) ^ k = C ((-1 : ℤ) ^ k) by rw [map_pow]; norm_num,
    PowerSeries.coeff_C_mul]
  rcases eq_or_ne m n with rfl | h
  · simp
  · rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm h), if_neg h]; ring

lemma coeff_pentTerm (n k : ℕ) :
    (PowerSeries.coeff n) (((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))
      = (if (k + 1) * (3 * k + 2) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
        + (if (k + 1) * (3 * k + 4) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0) := by
  rw [mul_add, map_add, coeff_sign_X_pow, coeff_sign_X_pow]

lemma le_pent1 (k : ℕ) : k + 1 ≤ (k + 1) * (3 * k + 2) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

lemma le_pent2 (k : ℕ) : k + 1 ≤ (k + 1) * (3 * k + 4) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

lemma coeff_pentTerm_eq_zero {n k : ℕ} (hk : n ≤ k) :
    (PowerSeries.coeff n) (((-1 : ℤ⟦X⟧)) ^ (k + 1) *
      (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2))) = 0 := by
  have h1 := le_pent1 k
  have h2 := le_pent2 k
  rw [coeff_pentTerm, if_neg (by omega), if_neg (by omega), add_zero]

lemma summable_pent :
    Summable fun k : ℕ =>
      ((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  refine summable_of_finite_support ((Set.finite_Iio d).subset (fun k hk => ?_))
  simp only [Function.mem_support] at hk
  simp only [Set.mem_Iio]
  by_contra hcon
  exact hk (coeff_pentTerm_eq_zero (by omega))

lemma two_dvd_pent1 (k : ℕ) : 2 ∣ (k + 1) * (3 * k + 2) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨(m + m + 1) * (3 * m + 1), by ring⟩
  · exact ⟨(m + 1) * (6 * m + 5), by ring⟩

lemma two_dvd_pent2 (k : ℕ) : 2 ∣ (k + 1) * (3 * k + 4) := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact ⟨(m + m + 1) * (3 * m + 2), by ring⟩
  · exact ⟨(m + 1) * (6 * m + 7), by ring⟩

lemma pent1_iff (k n : ℕ) : (k + 1) * (3 * k + 2) / 2 = n ↔ 2 * n = (k + 1) * (3 * (k + 1) - 1) := by
  obtain ⟨q, hq⟩ := two_dvd_pent1 k
  have e : 3 * (k + 1) - 1 = 3 * k + 2 := by omega
  rw [e, hq]
  omega

lemma pent2_iff (k n : ℕ) : (k + 1) * (3 * k + 4) / 2 = n ↔ 2 * n = (k + 1) * (3 * (k + 1) + 1) := by
  obtain ⟨q, hq⟩ := two_dvd_pent2 k
  have e : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
  rw [e, hq]
  omega

lemma Icc_one_eq_map (n : ℕ) :
    Finset.Icc 1 n = (Finset.range n).map ⟨fun k => k + 1, add_left_injective 1⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x - 1, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩
    omega

lemma coeff_pentSeries (n : ℕ) :
    (PowerSeries.coeff n) (1 + ∑' k : ℕ, ((-1 : ℤ⟦X⟧)) ^ (k + 1) *
        (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)))
      = pentSign n := by
  rw [map_add, PowerSeries.coeff_one,
    summable_pent.map_tsum _ (PowerSeries.WithPiTopology.continuous_coeff ℤ n),
    tsum_eq_sum (s := Finset.range n)
      (fun k hk => coeff_pentTerm_eq_zero (by simpa using hk))]
  simp only [coeff_pentTerm]
  rw [Finset.sum_add_distrib, pentSign, Icc_one_eq_map, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have e1 : ∑ k ∈ Finset.range n, (if (k + 1) * (3 * k + 2) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
      = ∑ k ∈ Finset.range n,
        (if 2 * n = (k + 1) * (3 * (k + 1) - 1) then ((-1 : ℤ)) ^ (k + 1) else 0) :=
    Finset.sum_congr rfl (fun k _ => if_congr (pent1_iff k n) rfl rfl)
  have e2 : ∑ k ∈ Finset.range n, (if (k + 1) * (3 * k + 4) / 2 = n then ((-1 : ℤ)) ^ (k + 1) else 0)
      = ∑ k ∈ Finset.range n,
        (if 2 * n = (k + 1) * (3 * (k + 1) + 1) then ((-1 : ℤ)) ^ (k + 1) else 0) :=
    Finset.sum_congr rfl (fun k _ => if_congr (pent2_iff k n) rfl rfl)
  rw [e1, e2]
  ring

/-- **Euler's pentagonal number theorem**: as formal power series over `ℤ`,
`∏_{i ≥ 1} (1 - X^i) = 1 + ∑_{a ≥ 1} (-1)^a (X^{a(3a-1)/2} + X^{a(3a+1)/2})`. -/
theorem euler_pentagonal :
    ∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))
      = 1 + ∑' k : ℕ, ((-1 : ℤ⟦X⟧)) ^ (k + 1) *
          (X ^ ((k + 1) * (3 * k + 2) / 2) + X ^ ((k + 1) * (3 * k + 4) / 2)) := by
  ext n
  rw [coeff_tprod, coeff_pentSeries, sum_distinctSets]

end Math


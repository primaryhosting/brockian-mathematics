import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

theorem approx_circuit {n : ℕ} (l : ℕ) (hl : 1 ≤ l) :
    ∀ {k : ℕ} (C : Ckt n k), ∃ (P : Fin k → Cube n → ZMod q) (B : Finset (Cube n)),
      B.card * 2 ^ l ≤ k * 2 ^ n ∧
      (∀ i, P i ∈ Deg (ZMod q) n (((q - 1) * l) ^ (C.depth i))) ∧
      (∀ i, ∀ x ∉ B, P i x = bit q (C.eval q x i)) := by
  classical
  have hq2 : 2 ≤ q := hq.out.two_le
  have hbase : 1 ≤ (q - 1) * l := Nat.one_le_iff_ne_zero.2 (by
    have : q - 1 ≠ 0 := by omega
    exact Nat.mul_ne_zero this (by omega))
  have hpowmono : ∀ a b : ℕ, a ≤ b → ((q - 1) * l) ^ a ≤ ((q - 1) * l) ^ b :=
    fun a b h => Nat.pow_le_pow_right hbase h
  intro k C
  induction C with
  | nil => exact ⟨Fin.elim0, ∅, by simp, fun i => i.elim0, fun i => i.elim0⟩
  | @cons k c g ih =>
      obtain ⟨P, B, hB, hdeg, hcorr⟩ := ih
      obtain ⟨newP, E, hE, hnewdeg, hnewcorr⟩ :
        ∃ (newP : Cube n → ZMod q) (E : Finset (Cube n)),
          E.card * 2 ^ l ≤ 2 ^ n ∧
          newP ∈ Deg (ZMod q) n (((q - 1) * l) ^ (g.depth c.depth)) ∧
          (∀ x, x ∉ B → x ∉ E → newP x = bit q (g.eval q (c.eval q x) x)) := by
        cases g with
        | var i =>
            refine ⟨coord (ZMod q) i, ∅, by simp, ?_, ?_⟩
            · simpa [Node.depth] using coord_mem_Deg (F := ZMod q) i (le_refl 1)
            · intro x _ _
              by_cases h : x i <;> simp [Node.eval, coord, bit, h]
        | const b =>
            refine ⟨fun _ => bit q b, ∅, by simp, ?_, ?_⟩
            · exact const_mem_Deg _ _
            · intro x _ _
              simp [Node.eval]
        | not j =>
            refine ⟨1 - P j, ∅, by simp, ?_, ?_⟩
            · exact Submodule.sub_mem _ (one_mem_Deg _) (hdeg j)
            · intro x hxB _
              simp only [Node.eval, Pi.sub_apply, Pi.one_apply, hcorr j x hxB]
              rw [← bit_not]
        | mod L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set y : Fin L.length → Cube n → ZMod q := fun pos => P (L[pos]) with hy
            have hydeg : ∀ pos, y pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine mem_Deg_of_le (hdeg (L[pos])) ?_
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            refine ⟨fun x => 1 - Ez q (∑ pos : Fin L.length, y pos x), ∅, by simp, ?_, ?_⟩
            · have hsum : (fun x => ∑ pos : Fin L.length, y pos x) ∈ Deg (ZMod q) n dmax := by
                have he : (fun x => ∑ pos : Fin L.length, y pos x)
                    = ∑ pos : Fin L.length, y pos := by
                  funext x; simp [Finset.sum_apply]
                rw [he]
                exact Submodule.sum_mem _ (fun pos _ => hydeg pos)
              have hpow := pow_mem_Deg hsum (q - 1)
              have hfun : (fun x => 1 - Ez q (∑ pos : Fin L.length, y pos x))
                  = 1 - (fun x => ∑ pos : Fin L.length, y pos x) ^ (q - 1) := by
                funext x; simp [Ez, Pi.pow_apply]
              rw [hfun]
              refine Submodule.sub_mem _ (one_mem_Deg _) (mem_Deg_of_le hpow ?_)
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
            · intro x hxB _
              dsimp only
              have hval : ∑ pos : Fin L.length, y pos x
                  = ((L.countP (fun j => c.eval q x j) : ℕ) : ZMod q) := by
                rw [← sum_bit_countP (q := q) (fun j => c.eval q x j) L]
                rw [← Fin.sum_univ_fun_getElem L (fun j => bit q (c.eval q x j))]
                exact Finset.sum_congr rfl (fun pos _ => hcorr _ x hxB)
              rw [hval, Ez_eq_ite]
              have hdvd : (((L.countP (fun j => c.eval q x j) : ℕ) : ZMod q) = 0)
                  ↔ q ∣ L.countP (fun j => c.eval q x j) :=
                ZMod.natCast_eq_zero_iff _ _
              simp only [Node.eval, bit]
              by_cases hd : q ∣ L.countP (fun j => c.eval q x j)
              · rw [if_pos (hdvd.2 hd), if_pos (by simpa using hd)]
                simp
              · rw [if_neg (fun hcon => hd (hdvd.1 hcon)), if_neg (by simpa using hd)]
                simp
        | or L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set y : Fin L.length → Cube n → ZMod q := fun pos => P (L[pos]) with hy
            have hydeg : ∀ pos, y pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine mem_Deg_of_le (hdeg (L[pos])) ?_
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            obtain ⟨ch, hch⟩ := exists_or_choice (q := q) (n := n) l y
            refine ⟨orPoly y ch,
              (Finset.univ : Finset (Cube n)).filter (fun x => orPoly y ch x ≠ orTarget y x),
              hch, ?_, ?_⟩
            · refine mem_Deg_of_le (orPoly_mem_Deg y ch hydeg) ?_
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact le_of_eq (by ring)
            · intro x hxB hxE
              have hEq : orPoly y ch x = orTarget y x := by
                by_contra hcon
                exact hxE (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
              rw [hEq, orTarget]
              have hyx : ∀ pos : Fin L.length, y pos x = bit q (c.eval q x (L[pos])) :=
                fun pos => hcorr _ x hxB
              have hiff : (∀ pos : Fin L.length, y pos x = 0)
                  ↔ ∀ a ∈ L, c.eval q x a = false := by
                rw [← forall_getElem_iff L (fun a => c.eval q x a = false)]
                constructor
                · intro h pos
                  have := hyx pos
                  rw [h pos] at this
                  exact bit_eq_zero_iff.1 this.symm
                · intro h pos
                  rw [hyx pos, h pos]
                  simp [bit]
              simp only [Node.eval]
              by_cases hany : L.any (fun j => c.eval q x j) = true
              · have hnot : ¬ (∀ pos : Fin L.length, y pos x = 0) := by
                  rw [hiff]
                  intro hcon
                  obtain ⟨a, ha, hva⟩ := List.any_eq_true.1 hany
                  rw [hcon a ha] at hva
                  exact Bool.false_ne_true hva
                rw [if_neg hnot, hany]
                simp [bit]
              · have hyes : ∀ pos : Fin L.length, y pos x = 0 := by
                  rw [hiff]
                  intro a ha
                  by_contra hcon
                  exact hany (List.any_eq_true.2 ⟨a, ha, by simpa using hcon⟩)
                rw [if_pos hyes]
                have hf : L.any (fun j => c.eval q x j) = false := by simpa using hany
                rw [hf]
                simp [bit]
        | and L =>
            set dmax := ((q - 1) * l) ^ ((L.map c.depth).foldr max 0) with hdmax
            set z : Fin L.length → Cube n → ZMod q := fun pos => 1 - P (L[pos]) with hz
            have hzdeg : ∀ pos, z pos ∈ Deg (ZMod q) n dmax := by
              intro pos
              refine Submodule.sub_mem _ (one_mem_Deg _) (mem_Deg_of_le (hdeg (L[pos])) ?_)
              exact hpowmono _ _ (le_foldr_max c.depth L (List.getElem_mem pos.2))
            obtain ⟨ch, hch⟩ := exists_or_choice (q := q) (n := n) l z
            refine ⟨1 - orPoly z ch,
              (Finset.univ : Finset (Cube n)).filter (fun x => orPoly z ch x ≠ orTarget z x),
              hch, ?_, ?_⟩
            · refine Submodule.sub_mem _ (one_mem_Deg _)
                (mem_Deg_of_le (orPoly_mem_Deg z ch hzdeg) ?_)
              simp only [Node.depth]
              rw [pow_add, pow_one, ← hdmax]
              exact le_of_eq (by ring)
            · intro x hxB hxE
              have hEq : orPoly z ch x = orTarget z x := by
                by_contra hcon
                exact hxE (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcon⟩)
              simp only [Pi.sub_apply, Pi.one_apply, hEq, orTarget]
              have hzx : ∀ pos : Fin L.length, z pos x = 1 - bit q (c.eval q x (L[pos])) := by
                intro pos
                simp only [hz, Pi.sub_apply, Pi.one_apply, hcorr _ x hxB]
              have hiff : (∀ pos : Fin L.length, z pos x = 0)
                  ↔ ∀ a ∈ L, c.eval q x a = true := by
                rw [← forall_getElem_iff L (fun a => c.eval q x a = true)]
                constructor
                · intro h pos
                  have h2 := hzx pos
                  rw [h pos] at h2
                  by_contra hcon
                  have : c.eval q x (L[pos]) = false := by simpa using hcon
                  rw [this] at h2
                  simp [bit] at h2
                · intro h pos
                  rw [hzx pos, h pos]
                  simp [bit]
              simp only [Node.eval]
              by_cases hall : L.all (fun j => c.eval q x j) = true
              · have hyes : ∀ pos : Fin L.length, z pos x = 0 := by
                  rw [hiff]
                  intro a ha
                  exact List.all_eq_true.1 hall a ha
                rw [if_pos hyes, hall]
                simp [bit]
              · have hnot : ¬ (∀ pos : Fin L.length, z pos x = 0) := by
                  rw [hiff]
                  intro hcon
                  exact hall (List.all_eq_true.2 (fun a ha => hcon a ha))
                rw [if_neg hnot]
                have hf : L.all (fun j => c.eval q x j) = false := by simpa using hall
                rw [hf]
                simp [bit]
      refine ⟨Fin.snoc P newP, B ∪ E, ?_, ?_, ?_⟩
      · have hcard : (B ∪ E).card ≤ B.card + E.card := Finset.card_union_le _ _
        have : (B ∪ E).card * 2 ^ l ≤ (B.card + E.card) * 2 ^ l :=
          Nat.mul_le_mul_right _ hcard
        have h2 : (B.card + E.card) * 2 ^ l ≤ (k + 1) * 2 ^ n := by
          rw [add_mul, add_mul, one_mul]
          exact Nat.add_le_add hB hE
        omega
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [Ckt.depth] using hnewdeg
        · intro j
          simpa [Ckt.depth] using hdeg j
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · intro x hx
          simp only [Fin.snoc_last, Ckt.eval]
          exact hnewcorr x (fun h => hx (Finset.mem_union_left _ h))
            (fun h => hx (Finset.mem_union_right _ h))
        · intro j x hx
          simp only [Fin.snoc_castSucc, Ckt.eval]
          rw [hcorr j x (fun h => hx (Finset.mem_union_left _ h))]

end Field

end CS

import Mathlib

/-!
# Low-degree functions on the Boolean cube

For a commutative ring `F` we consider the `F`-valued functions on the Boolean cube
`Cube n = Fin n → Bool`.  A *monomial* is a function of the form
`x ↦ ∏ i ∈ S, (if x i then 1 else 0)`.  The submodule `Deg F n D` is the span of all
monomials of degree at most `D`; these are exactly the functions computed by
multilinear polynomials of degree at most `D`.
-/

namespace CS

open Finset

/-- The Boolean cube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The number of `true` coordinates of a point of the cube. -/

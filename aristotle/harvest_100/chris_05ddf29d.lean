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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `Mono c col S` says that the finite set `S` is monochromatic of colour `col`
for the edge-colouring `c` : every pair of distinct vertices of `S` gets colour `col`. -/
def Mono {V : Type*} (c : V → V → Bool) (col : Bool) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c u v = col

/-- The Ramsey property: every symmetric two-colouring of the edges of the complete
graph on `N` vertices contains a `red` clique of size `s` or a `blue` clique of size `t`. -/
def RamseyProp (N s t : ℕ) : Prop :=
  ∀ c : Fin N → Fin N → Bool, (∀ u v, c u v = c v u) →
    (∃ S : Finset (Fin N), S.card = s ∧ Mono c true S) ∨
    (∃ S : Finset (Fin N), S.card = t ∧ Mono c false S)

section General

variable {V : Type*} [DecidableEq V] {c : V → V → Bool}

theorem mono_triple (hsymm : ∀ u v, c u v = c v u) {col : Bool} {x y z : V}
    (h1 : c x y = col) (h2 : c x z = col) (h3 : c y z = col) :
    Mono c col ({x, y, z} : Finset V) := by
  intro u hu v hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | exact absurd rfl huv
      | assumption
      | (rw [hsymm]; assumption)

theorem no_red_triple (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : c x y = true) (h2 : c x z = true) (h3 : c y z = true) : False :=
  hno3 {x, y, z} (Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
    (mono_triple hsymm h1 h2 h3)

theorem mono_insert (hsymm : ∀ u v, c u v = c v u) {col : Bool} {v : V} {S : Finset V}
    (hS : Mono c col S) (hv : ∀ u ∈ S, c v u = col) (hvS : v ∉ S) :
    Mono c col (insert v S) := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact hv y hy'
  · rcases Finset.mem_insert.mp hy with rfl | hy'
    · rw [hsymm]; exact hv x hx'
    · exact hS x hx' y hy' hxy

/-- In a colouring with no red triangle, the red neighbourhood of a vertex is blue. -/
theorem mono_false_of_red_nbhd (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S) {v : V} {S : Finset V}
    (hvS : v ∉ S) (h : ∀ u ∈ S, c v u = true) : Mono c false S := by
  intro u hu w hw huw
  by_contra hne
  have hcuw : c u w = true := by
    cases hc : c u w with
    | false => exact absurd hc hne
    | true => rfl
  have hvu : v ≠ u := by rintro rfl; exact hvS hu
  have hvw : v ≠ w := by rintro rfl; exact hvS hw
  exact no_red_triple hsymm hno3 hvu hvw huw (h u hu) (h w hw) hcuw

/-- Handshake lemma (parity form): for a symmetric irreflexive relation, the sum over a
finite set `T` of the number of `T`-neighbours is even. -/
theorem even_sum_adj_card (A : V → V → Prop) [DecidableRel A]
    (hs : ∀ x y, A x y → A y x) (hi : ∀ x, ¬ A x x) (T : Finset V) :
    Even (∑ v ∈ T, (T.filter (A v)).card) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : ((insert a T).filter (A a)) = T.filter (A a) := by
        rw [Finset.filter_insert, if_neg (hi a)]
      have h2 : ∀ v ∈ T, ((insert a T).filter (A v)).card
          = (T.filter (A v)).card + (if A v a then 1 else 0) := by
        intro v hv
        rw [Finset.filter_insert]
        by_cases h : A v a
        · rw [if_pos h, if_pos h,
            Finset.card_insert_of_notMem (fun hmem => ha (Finset.mem_filter.mp hmem).1)]
        · rw [if_neg h, if_neg h, add_zero]
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, h1]
      have h3 : (∑ v ∈ T, if A v a then 1 else 0) = (T.filter (A a)).card := by
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases h : A a x
        · rw [if_pos (hs a x h), if_pos h]
        · rw [if_neg (fun hax => h (hs x a hax)), if_neg h]
      rw [h3]
      obtain ⟨m, hm⟩ := ih
      exact ⟨m + (T.filter (A a)).card, by omega⟩

/-- `R(3,3) ≤ 6`: with no red triangle, any 6 vertices contain a blue triangle. -/
theorem exists_blue3 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 6 ≤ T.card) : ∃ S ⊆ T, S.card = 3 ∧ Mono c false S := by
  obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hEcard : (T.erase v).card = T.card - 1 := Finset.card_erase_of_mem hv
  set E := T.erase v with hEdef
  set R := E.filter (fun u => c v u = true) with hRdef
  set B := E.filter (fun u => c v u = false) with hBdef
  have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by
    ext x; simp [hBdef]
  have hsum : R.card + B.card = E.card := by
    rw [hBeq, hRdef]
    exact Finset.card_filter_add_card_filter_not _
  have hRE : R ⊆ E := Finset.filter_subset _ _
  have hBE : B ⊆ E := Finset.filter_subset _ _
  have hET : E ⊆ T := Finset.erase_subset _ _
  by_cases hcase : 3 ≤ R.card
  · obtain ⟨S, hSR, hS3⟩ := Finset.exists_subset_card_eq hcase
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
    exact ⟨S, fun x hx => hET (hRE (hSR hx)), hS3,
      mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2)⟩
  · have hB3 : 3 ≤ B.card := by omega
    obtain ⟨S, hSB, hS3⟩ := Finset.exists_subset_card_eq hB3
    by_cases hpair : ∃ u ∈ S, ∃ w ∈ S, u ≠ w ∧ c u w = false
    · obtain ⟨u, hu, w, hw, huw, hcuw⟩ := hpair
      have hvu : v ≠ u := Ne.symm (Finset.mem_erase.mp (hBE (hSB hu))).1
      have hvw : v ≠ w := Ne.symm (Finset.mem_erase.mp (hBE (hSB hw))).1
      have hcvu : c v u = false := (Finset.mem_filter.mp (hSB hu)).2
      have hcvw : c v w = false := (Finset.mem_filter.mp (hSB hw)).2
      refine ⟨{v, u, w}, ?_, Finset.card_eq_three.mpr ⟨v, u, w, hvu, hvw, huw, rfl⟩,
        mono_triple hsymm hcvu hcvw hcuw⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hv
      · exact hET (hBE (hSB hu))
      · exact hET (hBE (hSB hw))
    · exfalso
      refine hno3 S hS3 ?_
      intro u hu w hw huw
      by_contra hne
      refine hpair ⟨u, hu, w, hw, huw, ?_⟩
      cases hc : c u w with
      | false => rfl
      | true => exact absurd hc hne

/-- `R(3,4) ≤ 9`: with no red triangle, any 9 vertices contain a blue set of size 4. -/
theorem exists_blue4 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 9 ≤ T.card) : ∃ S ⊆ T, S.card = 4 ∧ Mono c false S := by
  obtain ⟨T', hT'T, hT'⟩ := Finset.exists_subset_card_eq hT
  by_contra hcon
  push_neg at hcon
  have key : ∀ v ∈ T', ((T'.erase v).filter (fun u => c v u = true)).card = 3 := by
    intro v hv
    set E := T'.erase v with hEdef
    set R := E.filter (fun u => c v u = true) with hRdef
    set B := E.filter (fun u => c v u = false) with hBdef
    have hEcard : E.card = 8 := by rw [hEdef, Finset.card_erase_of_mem hv, hT']
    have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by ext x; simp [hBdef]
    have hsum : R.card + B.card = 8 := by
      rw [← hEcard, hBeq, hRdef]
      exact Finset.card_filter_add_card_filter_not _
    have hRE : R ⊆ E := Finset.filter_subset _ _
    have hBE : B ⊆ E := Finset.filter_subset _ _
    have hET : E ⊆ T' := Finset.erase_subset _ _
    have hR4 : R.card ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨S, hSR, hS4⟩ := Finset.exists_subset_card_eq (show 4 ≤ R.card by omega)
      have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
      exact hcon S (fun x hx => hT'T (hET (hRE (hSR hx)))) hS4
        (mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2))
    have hB5 : B.card ≤ 5 := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨S, hSB, hS3, hSm⟩ := exists_blue3 hsymm hno3 B (by omega)
      have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hBE (hSB h))).1 rfl
      refine hcon (insert v S) ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hT'T hv
        · exact hT'T (hET (hBE (hSB hx)))
      · rw [Finset.card_insert_of_notMem hvS, hS3]
      · exact mono_insert hsymm hSm (fun u hu => (Finset.mem_filter.mp (hSB hu)).2) hvS
    omega
  have heven := even_sum_adj_card (fun x y => x ≠ y ∧ c x y = true)
    (fun x y h => ⟨Ne.symm h.1, by rw [hsymm]; exact h.2⟩) (by simp) T'
  have hrw : ∀ v ∈ T', (T'.filter (fun u => v ≠ u ∧ c v u = true)).card = 3 := by
    intro v hv
    rw [← key v hv]
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hu, hne, hc⟩; exact ⟨⟨Ne.symm hne, hu⟩, hc⟩
    · rintro ⟨⟨hne, hu⟩, hc⟩; exact ⟨hu, Ne.symm hne, hc⟩
  rw [Finset.sum_congr rfl hrw, Finset.sum_const, hT'] at heven
  norm_num at heven

/-- `R(3,5) ≤ 14`: with no red triangle, any 14 vertices contain a blue set of size 5. -/
theorem exists_blue5 (hsymm : ∀ u v, c u v = c v u)
    (hno3 : ∀ S : Finset V, S.card = 3 → ¬ Mono c true S)
    (T : Finset V) (hT : 14 ≤ T.card) : ∃ S ⊆ T, S.card = 5 ∧ Mono c false S := by
  obtain ⟨T', hT'T, hT'⟩ := Finset.exists_subset_card_eq hT
  have hv' : T'.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hv'
  set E := T'.erase v with hEdef
  set R := E.filter (fun u => c v u = true) with hRdef
  set B := E.filter (fun u => c v u = false) with hBdef
  have hEcard : E.card = 13 := by rw [hEdef, Finset.card_erase_of_mem hv, hT']
  have hBeq : B = E.filter (fun u => ¬ (c v u = true)) := by ext x; simp [hBdef]
  have hsum : R.card + B.card = 13 := by
    rw [← hEcard, hBeq, hRdef]
    exact Finset.card_filter_add_card_filter_not _
  have hRE : R ⊆ E := Finset.filter_subset _ _
  have hBE : B ⊆ E := Finset.filter_subset _ _
  have hET : E ⊆ T' := Finset.erase_subset _ _
  by_cases hcase : 5 ≤ R.card
  · obtain ⟨S, hSR, hS5⟩ := Finset.exists_subset_card_eq hcase
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hRE (hSR h))).1 rfl
    exact ⟨S, fun x hx => hT'T (hET (hRE (hSR hx))), hS5,
      mono_false_of_red_nbhd hsymm hno3 hvS (fun u hu => (Finset.mem_filter.mp (hSR hu)).2)⟩
  · obtain ⟨S, hSB, hS4, hSm⟩ := exists_blue4 hsymm hno3 B (by omega)
    have hvS : v ∉ S := fun h => (Finset.mem_erase.mp (hBE (hSB h))).1 rfl
    refine ⟨insert v S, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hT'T hv
      · exact hT'T (hET (hBE (hSB hx)))
    · rw [Finset.card_insert_of_notMem hvS, hS4]
    · exact mono_insert hsymm hSm (fun u hu => (Finset.mem_filter.mp (hSB hu)).2) hvS

end General

/-- The upper bound `R(3,5) ≤ 14`. -/
theorem ramseyProp_fourteen : RamseyProp 14 3 5 := by
  intro c hsymm
  by_cases h : ∃ S : Finset (Fin 14), S.card = 3 ∧ Mono c true S
  · exact Or.inl h
  · push_neg at h
    obtain ⟨S, -, hS5, hSm⟩ := exists_blue5 hsymm (fun S hS => h S hS) Finset.univ (by simp)
    exact Or.inr ⟨S, hS5, hSm⟩

/-! ### The extremal colouring on 13 vertices

The circulant graph `C₁₃(1,5)`: vertices `ZMod 13`, with `u` and `v` red-adjacent
iff `u - v ∈ {1, 5, 8, 12}`.  It has no red triangle and no blue set of size `5`. -/

/-- The difference `u - v` modulo `13`. -/
def diff13 (u v : Fin 13) : ℕ := (u.val + 13 - v.val) % 13

/-- The extremal colouring on 13 vertices. -/
def col13 (u v : Fin 13) : Bool :=
  diff13 u v == 1 || diff13 u v == 5 || diff13 u v == 8 || diff13 u v == 12

/-- Membership in the non-neighbourhood of `0`. -/
def inNB (u : Fin 13) : Bool :=
  u.val == 2 || u.val == 3 || u.val == 4 || u.val == 6 ||
    u.val == 7 || u.val == 9 || u.val == 10 || u.val == 11

/-- Translation by `-a` on `Fin 13`. -/
def shift13 (a x : Fin 13) : Fin 13 := ⟨(x.val + 13 - a.val) % 13, Nat.mod_lt _ (by norm_num)⟩

theorem col13_symm : ∀ u v : Fin 13, col13 u v = col13 v u := by decide

set_option maxRecDepth 100000 in
theorem col13_no_triangle : ∀ u v w : Fin 13, u ≠ v → u ≠ w → v ≠ w →
    ¬(col13 u v = true ∧ col13 u w = true ∧ col13 v w = true) := by decide

theorem col13_inNB : ∀ u : Fin 13, u ≠ 0 → col13 u 0 = false → inNB u := by decide

set_option maxRecDepth 100000 in
theorem col13_no_blue4_inNB : ∀ p q r s : Fin 13, inNB p → inNB q → inNB r → inNB s →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬(col13 p q = false ∧ col13 p r = false ∧ col13 p s = false ∧ col13 q r = false ∧
      col13 q s = false ∧ col13 r s = false) := by decide

set_option maxRecDepth 100000 in
theorem shift13_inj : ∀ a x y : Fin 13, shift13 a x = shift13 a y → x = y := by decide

set_option maxRecDepth 100000 in
theorem shift13_col : ∀ a x y : Fin 13, col13 (shift13 a x) (shift13 a y) = col13 x y := by decide

theorem shift13_self : ∀ a : Fin 13, shift13 a a = 0 := by decide

theorem col13_no_red3 : ∀ S : Finset (Fin 13), S.card = 3 → ¬ Mono col13 true S := by
  intro S hS hM
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hS
  refine col13_no_triangle x y z hxy hxz hyz ⟨?_, ?_, ?_⟩
  · exact hM x (by simp) y (by simp) hxy
  · exact hM x (by simp) z (by simp) hxz
  · exact hM y (by simp) z (by simp) hyz

theorem col13_no_blue5 : ∀ S : Finset (Fin 13), S.card = 5 → ¬ Mono col13 false S := by
  intro S hS hM
  obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hinj : Function.Injective (shift13 a) := fun x y h => shift13_inj a x y h
  set S' := S.image (shift13 a) with hS'def
  have hcard : S'.card = 5 := by rw [hS'def, Finset.card_image_of_injective _ hinj, hS]
  have hM' : Mono col13 false S' := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    rw [shift13_col]
    exact hM x hx y hy (fun e => huv (by rw [e]))
  have h0 : (0 : Fin 13) ∈ S' := by
    have h := Finset.mem_image_of_mem (shift13 a) ha
    rwa [shift13_self] at h
  set S'' := S'.erase 0 with hS''def
  have hc'' : S''.card = 4 := by rw [hS''def, Finset.card_erase_of_mem h0, hcard]
  obtain ⟨p, hp⟩ : S''.Nonempty := Finset.card_pos.mp (by omega)
  have hcp : (S''.erase p).card = 3 := by rw [Finset.card_erase_of_mem hp, hc'']
  obtain ⟨q, r, s, hqr, hqs, hrs, hqrs⟩ := Finset.card_eq_three.mp hcp
  have hmemq : q ∈ S''.erase p := by rw [hqrs]; simp
  have hmemr : r ∈ S''.erase p := by rw [hqrs]; simp
  have hmems : s ∈ S''.erase p := by rw [hqrs]; simp
  have hq : q ∈ S'' := (Finset.mem_erase.mp hmemq).2
  have hr : r ∈ S'' := (Finset.mem_erase.mp hmemr).2
  have hs' : s ∈ S'' := (Finset.mem_erase.mp hmems).2
  have hpq : p ≠ q := Ne.symm (Finset.mem_erase.mp hmemq).1
  have hpr : p ≠ r := Ne.symm (Finset.mem_erase.mp hmemr).1
  have hps : p ≠ s := Ne.symm (Finset.mem_erase.mp hmems).1
  have hnb : ∀ u ∈ S'', inNB u = true := by
    intro u hu
    have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
    have huS' : u ∈ S' := (Finset.mem_erase.mp hu).2
    exact col13_inNB u hu0 (hM' u huS' 0 h0 hu0)
  have hblue : ∀ u ∈ S'', ∀ v ∈ S'', u ≠ v → col13 u v = false := by
    intro u hu v hv huv
    exact hM' u (Finset.mem_erase.mp hu).2 v (Finset.mem_erase.mp hv).2 huv
  exact col13_no_blue4_inNB p q r s (hnb p hp) (hnb q hq) (hnb r hr) (hnb s hs')
    hpq hpr hps hqr hqs hrs
    ⟨hblue p hp q hq hpq, hblue p hp r hr hpr, hblue p hp s hs' hps,
      hblue q hq r hr hqr, hblue q hq s hs' hqs, hblue r hr s hs' hrs⟩

theorem mono_map {V W : Type*} [DecidableEq V] [DecidableEq W] (d : W → W → Bool) (f : V ↪ W)
    (col : Bool) (S : Finset V) (h : Mono (fun u v => d (f u) (f v)) col S) :
    Mono d col (S.map f) := by
  intro u hu v hv huv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hv
  exact h x hx y hy (fun e => huv (by rw [e]))

/-- The lower bound: there is no Ramsey property below `14`. -/
theorem not_ramseyProp_of_le {N : ℕ} (hN : N ≤ 13) : ¬ RamseyProp N 3 5 := by
  intro hR
  set f : Fin N ↪ Fin 13 := ⟨Fin.castLE hN, Fin.castLE_injective hN⟩ with hf
  have hsymm : ∀ u v : Fin N, col13 (f u) (f v) = col13 (f v) (f u) :=
    fun u v => col13_symm _ _
  rcases hR (fun u v => col13 (f u) (f v)) hsymm with ⟨S, hS3, hSm⟩ | ⟨S, hS5, hSm⟩
  · exact col13_no_red3 (S.map f) (by rw [Finset.card_map, hS3]) (mono_map col13 f true S hSm)
  · exact col13_no_blue5 (S.map f) (by rw [Finset.card_map, hS5]) (mono_map col13 f false S hSm)

/-- **The Ramsey number `R(3,5)` equals `14`.** -/
theorem ramsey_3_5 : IsLeast {N : ℕ | RamseyProp N 3 5} 14 := by
  refine ⟨ramseyProp_fourteen, ?_⟩
  intro N hN
  by_contra hlt
  push_neg at hlt
  exact not_ramseyProp_of_le (by omega) hN

end Math


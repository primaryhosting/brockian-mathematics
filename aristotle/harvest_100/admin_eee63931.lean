import RequestProject.EulerPolyhedron

/-!
# Fullerene cages have exactly twelve pentagonal faces

A fullerene cage is a polyhedral (spherical) carbon cage in which every atom has exactly three
neighbours and every ring is a pentagon or a hexagon.  Combining Euler's formula
`V - E + F = 2` with the two incidence counts `3V = 2E` and `5p + 6h = 2E` forces the number
of pentagons to be exactly `12`, no matter how many hexagons there are.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### The edge involution -/

omit [Fintype α] in
/-- The edge permutation of a sphere map is an involution. -/
lemma IsSphereMap.edge_sq {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) : e * e = 1 := by
  induction h with
  | @edge a b hab => exact swap_mul_self a b
  | @pendant D s e h x c d hx hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      calc (swap c d * e) * (swap c d * e)
          = swap c d * ((e * swap c d) * e) := by group
        _ = swap c d * ((swap c d * e) * e) := by rw [comm_swap_of_fixed hec hed]
        _ = (swap c d * swap c d) * (e * e) := by group
        _ = 1 := by rw [swap_mul_self, ih, mul_one]
  | @chord D s e h x y c d hx hy hxy hface hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      calc (swap c d * e) * (swap c d * e)
          = swap c d * ((e * swap c d) * e) := by group
        _ = swap c d * ((swap c d * e) * e) := by rw [comm_swap_of_fixed hec hed]
        _ = (swap c d * swap c d) * (e * e) := by group
        _ = 1 := by rw [swap_mul_self, ih, mul_one]

omit [Fintype α] in
/-- The edge permutation of a sphere map has no fixed dart in `D`: every edge really has two
distinct darts. -/
lemma IsSphereMap.edge_ne {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    ∀ z ∈ D, e z ≠ z := by
  induction h with
  | @edge a b hab =>
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · rw [swap_apply_left]; exact fun hcon => hab hcon.symm
      · rw [swap_apply_right]; exact hab
  | @pendant D s e h x c d hx hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hzD
      · rw [Perm.mul_apply, hec, swap_apply_left]; exact hcd.symm
      · rw [Perm.mul_apply, hed, swap_apply_right]; exact hcd
      · have hez : e z ∈ D := (h.maps_into z hzD).2
        rw [Perm.mul_apply,
          swap_apply_of_ne_of_ne (fun hcon => hc (by rw [← hcon]; exact hez))
            (fun hcon => hdD (by rw [← hcon]; exact hez))]
        exact ih z hzD
  | @chord D s e h x y c d hx hy hxy hface hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hzD
      · rw [Perm.mul_apply, hec, swap_apply_left]; exact hcd.symm
      · rw [Perm.mul_apply, hed, swap_apply_right]; exact hcd
      · have hez : e z ∈ D := (h.maps_into z hzD).2
        rw [Perm.mul_apply,
          swap_apply_of_ne_of_ne (fun hcon => hc (by rw [← hcon]; exact hez))
            (fun hcon => hdD (by rw [← hcon]; exact hez))]
        exact ih z hzD

omit [DecidableEq α] [Fintype α] in
lemma sameCycle_of_involution {e : Perm α} (h2 : e * e = 1) {z w : α} (h : e.SameCycle z w) :
    w = z ∨ w = e z := by
  obtain ⟨i, hi⟩ := h
  have hsq : e ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h2
  rcases Int.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have : e ^ i = 1 := by
      rw [hk, show k + k = 2 * k by ring, zpow_mul, hsq, one_zpow]
    rw [← hi, this]
    rfl
  · right
    have : e ^ i = e := by
      rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
    rw [← hi, this]

/-- The edge (orbit of the edge involution) through a dart consists of exactly its two darts. -/
lemma IsSphereMap.cyc_edge {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {z : α}
    (hz : z ∈ D) : cyc e D z = {z, e z} := by
  have hez : e z ∈ D := (h.maps_into z hz).2
  ext w
  simp only [mem_cyc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hsc⟩
    exact (sameCycle_of_involution h.edge_sq hsc).imp id id
  · rintro (rfl | rfl)
    · exact ⟨hz, SameCycle.refl _ _⟩
    · exact ⟨hez, ⟨1, by simp⟩⟩

lemma IsSphereMap.cyc_edge_card {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {z : α}
    (hz : z ∈ D) : (cyc e D z).card = 2 := by
  rw [h.cyc_edge hz, Finset.card_insert_of_notMem (by simpa using (h.edge_ne z hz).symm)]
  simp

/-! ### Counting faces of a given size -/

/-- The number of faces of the map with exactly `k` darts on their boundary (`k`-gons). -/
noncomputable def numFacesOfSize (D : Finset α) (s e : Perm α) (k : ℕ) : ℕ :=
  ((D.image (cyc (s * e) D)).filter (fun C => C.card = k)).card

/-- **A fullerene cage has exactly twelve pentagonal faces.**

For a map on the sphere in which every vertex has degree three and every face is a pentagon
or a hexagon, the number of pentagonal faces is exactly `12` (whatever the number of
hexagons is). -/
theorem fullerene_twelve_pentagons {D : Finset α} {s e : Perm α} (hmap : IsSphereMap D s e)
    (hdeg : ∀ z ∈ D, (cyc s D z).card = 3)
    (hfaces : ∀ z ∈ D, (cyc (s * e) D z).card = 5 ∨ (cyc (s * e) D z).card = 6) :
    numFacesOfSize D s e 5 = 12 := by
  classical
  set Fs := D.image (cyc (s * e) D) with hFs
  have hmem : ∀ C ∈ Fs, C.card = 5 ∨ C.card = 6 := by
    intro C hC
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hC
    exact hfaces z hz
  have hV : D.card = 3 * norb s D := card_eq_mul_norb hdeg
  have hE : D.card = 2 * norb e D := card_eq_mul_norb (fun z hz => hmap.cyc_edge_card hz)
  have hneg : Fs.filter (fun C => ¬ C.card = 5) = Fs.filter (fun C => C.card = 6) := by
    apply Finset.filter_congr
    intro C hC
    rcases hmem C hC with h5 | h6
    · simp [h5]
    · simp [h6]
  have hsplit : numFacesOfSize D s e 5 + numFacesOfSize D s e 6 = norb (s * e) D := by
    unfold numFacesOfSize norb
    rw [← hFs, ← hneg]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : D.card = 5 * numFacesOfSize D s e 5 + 6 * numFacesOfSize D s e 6 := by
    have h1 : D.card = ∑ C ∈ Fs, C.card := card_eq_sum_card_cyc (s * e) D
    rw [h1, ← Finset.sum_filter_add_sum_filter_not Fs (fun C => C.card = 5) (fun C => C.card),
      hneg]
    have e5 : ∑ C ∈ Fs.filter (fun C => C.card = 5), C.card
        = 5 * numFacesOfSize D s e 5 := by
      rw [Finset.sum_congr rfl (fun C hC => (Finset.mem_filter.1 hC).2)]
      simp [numFacesOfSize, hFs, mul_comm]
    have e6 : ∑ C ∈ Fs.filter (fun C => C.card = 6), C.card
        = 6 * numFacesOfSize D s e 6 := by
      rw [Finset.sum_congr rfl (fun C hC => (Finset.mem_filter.1 hC).2)]
      simp [numFacesOfSize, hFs, mul_comm]
    rw [e5, e6]
  have heuler := euler_polyhedron hmap
  unfold numV numE numF at heuler
  omega

end Chem

import Mathlib

/-!
# Counting orbits of a permutation on a finite set

This file develops the combinatorial tool needed for Euler's polyhedron formula:
the number of cycles (orbits) of a permutation changes by exactly one when the
permutation is multiplied by a transposition `swap x y`:

* it *decreases* by one if `x` and `y` lie in different cycles (the two cycles merge);
* it *increases* by one if `x` and `y` lie in the same cycle (the cycle splits).

Everything is relative to a finite ambient type `α` and a `Finset α` of interest.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The elements of `D` lying in the same `π`-cycle as `x`. -/
def cyc (π : Perm α) (D : Finset α) (x : α) : Finset α := D.filter (fun y => π.SameCycle x y)

/-- The number of `π`-orbits meeting `D`. -/
def norb (π : Perm α) (D : Finset α) : ℕ := (D.image (cyc π D)).card

lemma mem_cyc {π : Perm α} {D : Finset α} {x y : α} :
    y ∈ cyc π D x ↔ y ∈ D ∧ π.SameCycle x y := by
  simp [cyc]

lemma self_mem_cyc {π : Perm α} {D : Finset α} {x : α} (hx : x ∈ D) : x ∈ cyc π D x :=
  mem_cyc.2 ⟨hx, SameCycle.refl _ _⟩

lemma cyc_eq_iff {π : Perm α} {D : Finset α} {x y : α} (hy : y ∈ D) :
    cyc π D x = cyc π D y ↔ π.SameCycle x y := by
  constructor
  · intro h
    have : y ∈ cyc π D x := by rw [h]; exact self_mem_cyc hy
    exact (mem_cyc.1 this).2
  · intro h
    ext z
    simp only [mem_cyc]
    exact and_congr_right fun _ => ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

lemma cyc_eq_of_sameCycle {π : Perm α} {D : Finset α} {x y : α} (h : π.SameCycle x y) :
    cyc π D x = cyc π D y := by
  ext z
  simp only [mem_cyc]
  exact and_congr_right fun _ => ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

/-! ### Iterating `swap x y * π` up to the first return time -/

omit [Fintype α] in
lemma pow_swap_mul_apply_eq {π : Perm α} {x y : α} {N : ℕ}
    (h : ∀ i, 0 < i → i < N → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y)) :
    ∀ i, i < N → ((swap x y * π) ^ i) x = (π ^ i) x := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n < N := Nat.lt_of_succ_lt hn
      have hstep : ((swap x y * π) ^ (n + 1)) x = (swap x y) (π ((π ^ n) x)) := by
        rw [pow_succ']
        simp [ih hn']
      rw [hstep]
      have hx : (π ^ (n + 1)) x = π ((π ^ n) x) := by
        rw [pow_succ']; rfl
      rw [← hx]
      have := h (n + 1) (Nat.succ_pos n) hn
      rw [swap_apply_of_ne_of_ne this.1 this.2]

omit [Fintype α] in
lemma pow_swap_mul_apply_last {π : Perm α} {x y : α} {N : ℕ} (hN : 0 < N)
    (h : ∀ i, 0 < i → i < N → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y)) :
    ((swap x y * π) ^ N) x = (swap x y) ((π ^ N) x) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n < n + 1 := Nat.lt_succ_self n
  have := pow_swap_mul_apply_eq h n hn
  rw [pow_succ', pow_succ']
  simp [this]

omit [DecidableEq α] in
lemma exists_pos_pow_apply_eq_self (π : Perm α) (x : α) : ∃ n, 0 < n ∧ (π ^ n) x = x := by
  refine ⟨orderOf π, orderOf_pos π, ?_⟩
  rw [pow_orderOf_eq_one]
  rfl

omit [DecidableEq α] [Fintype α] in
lemma pow_mod_apply {π : Perm α} {x : α} {m : ℕ} (hm : (π ^ m) x = x) (i : ℕ) :
    (π ^ (i % m)) x = (π ^ i) x := by
  have key : ∀ k : ℕ, (π ^ (m * k)) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
        have : m * (n + 1) = m * n + m := by ring
        rw [this, pow_add, Perm.mul_apply, hm, ih]
  conv_rhs => rw [show i = i % m + m * (i / m) from (Nat.mod_add_div i m).symm]
  rw [pow_add, Perm.mul_apply, key]

omit [DecidableEq α] [Fintype α] in
lemma sameCycle_of_pow {π : Perm α} {x : α} (i : ℕ) : π.SameCycle x ((π ^ i) x) :=
  ⟨(i : ℤ), by simp⟩

/-! ### Cycles of `swap x y * π` when `x` and `y` are in different cycles -/

/-- If `x` and `y` are in different `π`-cycles, then every element of the `π`-cycle of `x`
is in the `(swap x y * π)`-cycle of `x`. -/
lemma sameCycle_swap_mul_of_left {π : Perm α} {x y z : α} (hxy : ¬ π.SameCycle x y)
    (h : π.SameCycle x z) : (swap x y * π).SameCycle x z := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_pos_pow_apply_eq_self π x
  -- the minimal positive return time
  set P : ℕ → Prop := fun n => 0 < n ∧ (π ^ n) x = x with hP
  have hex : ∃ n, P n := ⟨m, hm0, hm⟩
  classical
  set k := Nat.find hex with hk
  obtain ⟨hk0, hkx⟩ : P k := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < k → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) := by
    intro i hi hik
    constructor
    · intro hcon
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hi, hcon⟩ : P i)
      omega
    · intro hcon
      exact hxy (hcon ▸ sameCycle_of_pow i)
  obtain ⟨i, _, _, hi⟩ := h.exists_pow_eq π
  have hi' : (π ^ (i % k)) x = z := by rw [pow_mod_apply hkx i, hi]
  have : ((swap x y * π) ^ (i % k)) x = z := by
    rw [pow_swap_mul_apply_eq hmin (i % k) (Nat.mod_lt _ hk0), hi']
  exact ⟨(i % k : ℤ), by simpa using this⟩

/-- If `x` and `y` are in different `π`-cycles, then they are in the same
`(swap x y * π)`-cycle: the two cycles merge. -/
lemma sameCycle_swap_mul_xy {π : Perm α} {x y : α} (hxy : ¬ π.SameCycle x y) :
    (swap x y * π).SameCycle x y := by
  classical
  obtain ⟨m, hm0, hm⟩ := exists_pos_pow_apply_eq_self π x
  set P : ℕ → Prop := fun n => 0 < n ∧ (π ^ n) x = x with hP
  have hex : ∃ n, P n := ⟨m, hm0, hm⟩
  set k := Nat.find hex with hk
  obtain ⟨hk0, hkx⟩ : P k := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < k → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) := by
    intro i hi hik
    constructor
    · intro hcon
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hi, hcon⟩ : P i)
      omega
    · intro hcon
      exact hxy (hcon ▸ sameCycle_of_pow i)
  have : ((swap x y * π) ^ k) x = y := by
    rw [pow_swap_mul_apply_last hk0 hmin, hkx, swap_apply_left]
  exact ⟨(k : ℤ), by simpa using this⟩

omit [Fintype α] in
/-- Elements outside the cycles of `x` and `y` are unaffected. -/
lemma pow_swap_mul_apply_of_not_mem {π : Perm α} {x y z : α} (hzx : ¬ π.SameCycle z x)
    (hzy : ¬ π.SameCycle z y) : ∀ i : ℕ, ((swap x y * π) ^ i) z = (π ^ i) z := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
      have hne : (π ^ (n + 1)) z ≠ x ∧ (π ^ (n + 1)) z ≠ y := by
        constructor
        · intro hcon
          exact hzx (hcon ▸ sameCycle_of_pow (n + 1))
        · intro hcon
          exact hzy (hcon ▸ sameCycle_of_pow (n + 1))
      have h1 : ((swap x y * π) ^ (n + 1)) z = (swap x y) (π ((π ^ n) z)) := by
        rw [pow_succ']
        simp [ih]
      have h2 : (π ^ (n + 1)) z = π ((π ^ n) z) := by rw [pow_succ']; rfl
      rw [h1, ← h2, swap_apply_of_ne_of_ne hne.1 hne.2]

lemma sameCycle_swap_mul_of_right {π : Perm α} {x y z : α} (hxy : ¬ π.SameCycle x y)
    (h : π.SameCycle y z) : (swap x y * π).SameCycle y z := by
  have h' := sameCycle_swap_mul_of_left (x := y) (y := x) (fun hc => hxy hc.symm) h
  rwa [swap_comm] at h'

/-- Anything in the cycle of `x` or of `y` lands in the merged cycle. -/
lemma sameCycle_swap_mul_of_mem {π : Perm α} {x y z : α} (hxy : ¬ π.SameCycle x y)
    (hz : π.SameCycle z x ∨ π.SameCycle z y) : (swap x y * π).SameCycle x z := by
  rcases hz with hz | hz
  · exact sameCycle_swap_mul_of_left hxy hz.symm
  · exact (sameCycle_swap_mul_xy hxy).trans (sameCycle_swap_mul_of_right hxy hz.symm)

/-- The relation describing the cycles of `swap x y * π`: the `π`-cycles, with those of
`x` and `y` glued together. -/
def MergeRel (π : Perm α) (x y : α) (z w : α) : Prop :=
  π.SameCycle z w ∨
    ((π.SameCycle z x ∨ π.SameCycle z y) ∧ (π.SameCycle w x ∨ π.SameCycle w y))

omit [DecidableEq α] [Fintype α] in
lemma MergeRel.refl (π : Perm α) (x y z : α) : MergeRel π x y z z := Or.inl (SameCycle.refl _ _)

omit [DecidableEq α] [Fintype α] in
lemma MergeRel.trans {π : Perm α} {x y z w u : α} (h1 : MergeRel π x y z w)
    (h2 : MergeRel π x y w u) : MergeRel π x y z u := by
  rcases h1 with h1 | ⟨hz, hw⟩
  · rcases h2 with h2 | ⟨hw, hu⟩
    · exact Or.inl (h1.trans h2)
    · refine Or.inr ⟨?_, hu⟩
      rcases hw with hw | hw
      · exact Or.inl (h1.trans hw)
      · exact Or.inr (h1.trans hw)
  · rcases h2 with h2 | ⟨_, hu⟩
    · refine Or.inr ⟨hz, ?_⟩
      rcases hw with hw | hw
      · exact Or.inl (h2.symm.trans hw)
      · exact Or.inr (h2.symm.trans hw)
    · exact Or.inr ⟨hz, hu⟩

omit [Fintype α] in
lemma mergeRel_apply (π : Perm α) (x y z : α) : MergeRel π x y z ((swap x y * π) z) := by
  have hstep : π.SameCycle z (π z) := ⟨1, by simp⟩
  by_cases h1 : π z = x
  · have : (swap x y * π) z = y := by simp [Perm.mul_apply, h1]
    rw [this]
    exact Or.inr ⟨Or.inl (h1 ▸ hstep), Or.inr (SameCycle.refl _ _)⟩
  · by_cases h2 : π z = y
    · have : (swap x y * π) z = x := by simp [Perm.mul_apply, h2]
      rw [this]
      exact Or.inr ⟨Or.inr (h2 ▸ hstep), Or.inl (SameCycle.refl _ _)⟩
    · have : (swap x y * π) z = π z := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2]
      rw [this]
      exact Or.inl hstep

omit [Fintype α] in
lemma mergeRel_pow (π : Perm α) (x y z : α) (i : ℕ) :
    MergeRel π x y z (((swap x y * π) ^ i) z) := by
  induction i with
  | zero => simpa using MergeRel.refl π x y z
  | succ n ih =>
      have hrw : ((swap x y * π) ^ (n + 1)) z = (swap x y * π) (((swap x y * π) ^ n) z) := by
        rw [pow_succ']; rfl
      rw [hrw]
      exact ih.trans (mergeRel_apply π x y _)

/-- Complete description of the cycles of `swap x y * π` when `x` and `y` lie in
different `π`-cycles. -/
lemma sameCycle_swap_mul_iff {π : Perm α} {x y : α} (hxy : ¬ π.SameCycle x y) (z w : α) :
    (swap x y * π).SameCycle z w ↔ MergeRel π x y z w := by
  constructor
  · intro h
    obtain ⟨i, _, _, hi⟩ := h.exists_pow_eq _
    exact hi ▸ mergeRel_pow π x y z i
  · intro h
    rcases h with h | ⟨hz, hw⟩
    · by_cases hin : π.SameCycle z x ∨ π.SameCycle z y
      · have hw : π.SameCycle w x ∨ π.SameCycle w y := by
          rcases hin with hin | hin
          · exact Or.inl (h.symm.trans hin)
          · exact Or.inr (h.symm.trans hin)
        exact (sameCycle_swap_mul_of_mem hxy hin).symm.trans (sameCycle_swap_mul_of_mem hxy hw)
      · push_neg at hin
        obtain ⟨i, _, _, hi⟩ := h.exists_pow_eq _
        refine ⟨(i : ℤ), ?_⟩
        have := pow_swap_mul_apply_of_not_mem hin.1 hin.2 i
        simpa [this] using hi
    · exact (sameCycle_swap_mul_of_mem hxy hz).symm.trans (sameCycle_swap_mul_of_mem hxy hw)

/-! ### The orbit count changes by one -/

/-- Multiplying by a transposition whose two points lie in **different** cycles merges
those cycles: the number of orbits drops by one. -/
theorem norb_swap_mul_of_not_sameCycle {π : Perm α} {D : Finset α} {x y : α}
    (hx : x ∈ D) (hy : y ∈ D) (hxy : ¬ π.SameCycle x y) :
    norb (swap x y * π) D + 1 = norb π D := by
  classical
  set In : α → Prop := fun z => π.SameCycle z x ∨ π.SameCycle z y with hIn
  set Din : Finset α := D.filter In with hDin
  set Dout : Finset α := D.filter (fun z => ¬ In z) with hDout
  set S : Finset (Finset α) := Dout.image (cyc π D) with hS
  have hsplit : Din ∪ Dout = D := Finset.filter_union_filter_not_eq _ _
  have himg : ∀ f : α → Finset α, D.image f = Din.image f ∪ Dout.image f := by
    intro f; rw [← Finset.image_union, hsplit]
  have hxDin : x ∈ Din := Finset.mem_filter.2 ⟨hx, Or.inl (SameCycle.refl _ _)⟩
  have hyDin : y ∈ Din := Finset.mem_filter.2 ⟨hy, Or.inr (SameCycle.refl _ _)⟩
  -- (1) outside the two cycles nothing changes
  have h1 : ∀ z ∈ Dout, cyc (swap x y * π) D z = cyc π D z := by
    intro z hz
    have hznot : ¬ In z := (Finset.mem_filter.1 hz).2
    ext w
    simp only [mem_cyc, sameCycle_swap_mul_iff hxy, MergeRel]
    constructor
    · rintro ⟨hwD, hrel | ⟨hzin, -⟩⟩
      · exact ⟨hwD, hrel⟩
      · exact absurd hzin hznot
    · rintro ⟨hwD, hrel⟩
      exact ⟨hwD, Or.inl hrel⟩
  -- (2) the merged class
  have h2 : ∀ z ∈ Din, cyc (swap x y * π) D z = Din := by
    intro z hz
    have hzin : In z := (Finset.mem_filter.1 hz).2
    ext w
    simp only [mem_cyc, sameCycle_swap_mul_iff hxy, MergeRel, hDin, Finset.mem_filter]
    constructor
    · rintro ⟨hwD, hrel | ⟨-, hwin⟩⟩
      · refine ⟨hwD, ?_⟩
        rcases hzin with h | h
        · exact Or.inl (hrel.symm.trans h)
        · exact Or.inr (hrel.symm.trans h)
      · exact ⟨hwD, hwin⟩
    · rintro ⟨hwD, hwin⟩
      exact ⟨hwD, Or.inr ⟨hzin, hwin⟩⟩
  -- (3) classes of the new permutation
  have h3 : D.image (cyc (swap x y * π) D) = insert Din S := by
    rw [himg]
    have e1 : Din.image (cyc (swap x y * π) D) = {Din} := by
      rw [Finset.image_congr (g := fun _ => Din) (fun z hz => h2 z hz),
        Finset.image_const ⟨x, hxDin⟩]
    have e2 : Dout.image (cyc (swap x y * π) D) = S := by
      rw [hS]; exact Finset.image_congr (fun z hz => h1 z hz)
    rw [e1, e2]
    ext C
    simp [Finset.mem_insert]
  -- (4) classes of the old permutation
  have h4 : D.image (cyc π D) = insert (cyc π D x) (insert (cyc π D y) S) := by
    rw [himg]
    have : Din.image (cyc π D) = {cyc π D x, cyc π D y} := by
      apply Finset.Subset.antisymm
      · intro C hC
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hC
        rcases (Finset.mem_filter.1 hz).2 with h | h
        · exact Finset.mem_insert.2 (Or.inl (cyc_eq_of_sameCycle h))
        · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (cyc_eq_of_sameCycle h)))
      · intro C hC
        rcases Finset.mem_insert.1 hC with rfl | hC
        · exact Finset.mem_image.2 ⟨x, hxDin, rfl⟩
        · rw [Finset.mem_singleton.1 hC]
          exact Finset.mem_image.2 ⟨y, hyDin, rfl⟩
    rw [this]
    ext C
    simp [Finset.mem_insert, hS, Finset.mem_image]
  -- (5) the classes involved are distinct and not among the untouched ones
  have hmemS : ∀ C ∈ S, ∃ z ∈ Dout, cyc π D z = C := by
    intro C hC
    obtain ⟨z, hz, hzC⟩ := Finset.mem_image.1 hC
    exact ⟨z, hz, hzC⟩
  have hDinS : Din ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have : z ∈ Din := hzC ▸ self_mem_cyc hzD
    exact (Finset.mem_filter.1 hz).2 (Finset.mem_filter.1 this).2
  have hCxS : cyc π D x ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have hzx : π.SameCycle z x := (cyc_eq_iff hx).1 (by rw [hzC])
    exact (Finset.mem_filter.1 hz).2 (Or.inl hzx)
  have hCyS : cyc π D y ∉ S := by
    intro hcon
    obtain ⟨z, hz, hzC⟩ := hmemS _ hcon
    have hzD : z ∈ D := (Finset.mem_filter.1 hz).1
    have hzy : π.SameCycle z y := (cyc_eq_iff hy).1 (by rw [hzC])
    exact (Finset.mem_filter.1 hz).2 (Or.inr hzy)
  have hCxy : cyc π D x ≠ cyc π D y := fun hcon => hxy ((cyc_eq_iff hy).1 hcon)
  -- conclude
  unfold norb
  rw [h3, h4, Finset.card_insert_of_notMem hDinS,
    Finset.card_insert_of_notMem (by simp [Finset.mem_insert, hCxy, hCxS]),
    Finset.card_insert_of_notMem hCyS]

/-- If `x` and `y` lie in the same `π`-cycle, that cycle is cut into two by `swap x y * π`,
and in particular `x` and `y` are no longer in the same cycle. -/
lemma not_sameCycle_swap_mul_of_sameCycle {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : π.SameCycle x y) : ¬ (swap x y * π).SameCycle x y := by
  classical
  obtain ⟨n, hn0, -, hn⟩ := h.exists_pow_eq π
  set P : ℕ → Prop := fun m => 0 < m ∧ (π ^ m) x = y with hP
  have hex : ∃ m, P m := ⟨n, hn0, hn⟩
  set k := Nat.find hex with hk
  obtain ⟨hk0, hkx⟩ : P k := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < k → ((π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) := by
    intro i hi hik
    constructor
    · intro hcon
      have : (π ^ (k - i)) x = y := by
        have hki : k - i + i = k := by omega
        calc (π ^ (k - i)) x = (π ^ (k - i)) ((π ^ i) x) := by rw [hcon]
          _ = (π ^ (k - i + i)) x := by rw [pow_add, Perm.mul_apply]
          _ = y := by rw [hki, hkx]
      have hle : Nat.find hex ≤ k - i := Nat.find_le (⟨by omega, this⟩ : P (k - i))
      omega
    · intro hcon
      have hle : Nat.find hex ≤ i := Nat.find_le (⟨hi, hcon⟩ : P i)
      omega
  have hfix : ((swap x y * π) ^ k) x = x := by
    rw [pow_swap_mul_apply_last hk0 hmin, hkx, swap_apply_right]
  intro hcon
  obtain ⟨j, hj0, -, hj⟩ := hcon.exists_pow_eq _
  have hjk : ((swap x y * π) ^ (j % k)) x = y := by rw [pow_mod_apply hfix j, hj]
  have hlt : j % k < k := Nat.mod_lt _ hk0
  rw [pow_swap_mul_apply_eq hmin (j % k) hlt] at hjk
  rcases Nat.eq_zero_or_pos (j % k) with h0 | h0
  · rw [h0] at hjk
    simp at hjk
    exact hne hjk
  · exact (hmin (j % k) h0 hlt).2 hjk

/-- Multiplying by a transposition whose two points lie in the **same** cycle splits that
cycle: the number of orbits goes up by one. -/
theorem norb_swap_mul_of_sameCycle {π : Perm α} {D : Finset α} {x y : α}
    (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y) (h : π.SameCycle x y) :
    norb (swap x y * π) D = norb π D + 1 := by
  have hns := not_sameCycle_swap_mul_of_sameCycle hne h
  have key := norb_swap_mul_of_not_sameCycle (π := swap x y * π) hx hy hns
  rw [← mul_assoc, swap_mul_self, one_mul] at key
  omega

/-! ### Adding a new fixed point -/

omit [DecidableEq α] [Fintype α] in
lemma sameCycle_fixed {π : Perm α} {c z : α} (hfix : π c = c) (h : π.SameCycle c z) : z = c := by
  obtain ⟨i, hi⟩ := h
  rw [← hi, Perm.zpow_apply_eq_self_of_apply_eq_self hfix i]

/-- Adjoining a new dart which is a fixed point adds exactly one orbit. -/
theorem norb_insert_of_fixed {π : Perm α} {D : Finset α} {c : α} (hc : c ∉ D) (hfix : π c = c) :
    norb π (insert c D) = norb π D + 1 := by
  classical
  have hcc : cyc π (insert c D) c = {c} := by
    ext w
    simp only [mem_cyc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hsc⟩
      exact sameCycle_fixed hfix hsc
    · rintro rfl
      exact ⟨Or.inl rfl, SameCycle.refl _ _⟩
  have hz : ∀ z ∈ D, cyc π (insert c D) z = cyc π D z := by
    intro z hzD
    ext w
    simp only [mem_cyc, Finset.mem_insert]
    constructor
    · rintro ⟨hw | hw, hsc⟩
      · exfalso
        have hsc' : π.SameCycle c z := (hw ▸ hsc).symm
        have hzc : z = c := sameCycle_fixed hfix hsc'
        exact hc (hzc ▸ hzD)
      · exact ⟨hw, hsc⟩
    · rintro ⟨hw, hsc⟩
      exact ⟨Or.inr hw, hsc⟩
  have himg : (insert c D).image (cyc π (insert c D)) = insert {c} (D.image (cyc π D)) := by
    rw [Finset.image_insert, hcc]
    congr 1
    exact Finset.image_congr (fun z hz' => hz z hz')
  have hnot : ({c} : Finset α) ∉ D.image (cyc π D) := by
    intro hcon
    obtain ⟨z, hzD, hzc⟩ := Finset.mem_image.1 hcon
    have : z ∈ ({c} : Finset α) := hzc ▸ self_mem_cyc hzD
    rw [Finset.mem_singleton] at this
    exact hc (this ▸ hzD)
  unfold norb
  rw [himg, Finset.card_insert_of_notMem hnot]

/-! ### Summing over the orbits -/

/-- `D` is partitioned by the orbits it meets. -/
lemma card_eq_sum_card_cyc (π : Perm α) (D : Finset α) :
    D.card = ∑ C ∈ D.image (cyc π D), C.card := by
  classical
  rw [Finset.card_eq_sum_card_image (cyc π D) D]
  refine Finset.sum_congr rfl ?_
  intro C hC
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hC
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_cyc]
  constructor
  · rintro ⟨hzD, hzc⟩
    exact ⟨hzD, ((cyc_eq_iff hw).1 hzc).symm⟩
  · rintro ⟨hzD, hsc⟩
    exact ⟨hzD, (cyc_eq_iff hw).2 hsc.symm⟩

/-- If every orbit meeting `D` has `k` elements, then `|D| = k * (number of orbits)`. -/
lemma card_eq_mul_norb {π : Perm α} {D : Finset α} {k : ℕ} (h : ∀ z ∈ D, (cyc π D z).card = k) :
    D.card = k * norb π D := by
  classical
  rw [card_eq_sum_card_cyc π D]
  have hk : ∀ C ∈ D.image (cyc π D), C.card = k := by
    intro C hC
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hC
    exact h z hz
  rw [Finset.sum_congr rfl hk]
  simp [norb, mul_comm]

end Chem

import RequestProject.EulerPolyhedron

/-!
# A worked example

A small sanity check that `Chem.IsSphereMap` really describes maps on the sphere: we build the
triangle (a cycle of length three, drawn on the sphere) out of the constructors and check that
its vertex, edge and face counts are `3`, `3` and `2`, so that `V - E + F = 3 - 3 + 2 = 2`.

The six darts are `0, …, 5 : Fin 6`; the construction is: start with the edge `{0,1}`, attach a
pendant edge `{2,3}` at the dart `0`, and finally close the triangle with a chord `{4,5}`
joining the two corners following the darts `1` and `3`.
-/

namespace Chem

open Equiv Equiv.Perm Finset

/-- The triangle is a map on the sphere. -/
theorem triangle_isSphereMap :
    IsSphereMap ({0, 1, 2, 3, 4, 5} : Finset (Fin 6))
      (swap 1 4 * (swap 3 5 * swap 0 2)) (swap 4 5 * (swap 2 3 * swap 0 1)) := by
  have h0 : IsSphereMap ({0, 1} : Finset (Fin 6)) 1 (swap 0 1) := IsSphereMap.edge (by decide)
  have h1 := h0.pendant (x := 0) (c := 2) (d := 3) (by decide) (by decide) (by decide)
  simp only [Equiv.Perm.one_apply, mul_one] at h1
  have hface : ((swap (0 : Fin 6) 2) * (swap 2 3 * swap 0 1)).SameCycle
      ((swap (0 : Fin 6) 2) 1) ((swap (0 : Fin 6) 2) 3) := by decide
  have h2 := h1.chord (x := 1) (y := 3) (c := 4) (d := 5) (by decide) (by decide) (by decide)
    hface (by decide) (by decide)
  have e1 : (swap (0 : Fin 6) 2) 1 = 1 := by decide
  have e2 : (swap (0 : Fin 6) 2) 3 = 3 := by decide
  rw [e1, e2] at h2
  have hD : (insert 4 (insert 5 (insert 2 (insert 3 ({0, 1} : Finset (Fin 6)))))) =
      {0, 1, 2, 3, 4, 5} := by decide
  rw [hD] at h2
  exact h2

theorem triangle_numV :
    numV ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2)) = 3 := by
  decide

theorem triangle_numE :
    numE ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 4 5 * (swap 2 3 * swap 0 1)) = 3 := by
  decide

theorem triangle_numF :
    numF ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
      (swap 4 5 * (swap 2 3 * swap 0 1)) = 2 := by
  decide

/-- Euler's formula, checked on the triangle: `3 - 3 + 2 = 2`. -/
example :
    numV ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
      + numF ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 1 4 * (swap 3 5 * swap 0 2))
        (swap 4 5 * (swap 2 3 * swap 0 1))
      = numE ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) (swap 4 5 * (swap 2 3 * swap 0 1)) + 2 :=
  euler_polyhedron triangle_isSphereMap

end Chem

import RequestProject.PermOrbits

/-!
# Euler's polyhedron formula `V - E + F = 2`

The surface of a convex polyhedron (a fullerene cage, say) is described combinatorially by a
*map on the sphere*.  We use the classical dart (half-edge) model of a map:

* a finite set `D` of **darts** (each edge of the polyhedron contributes two darts,
  one for each of its two ends);
* a permutation `s` (the *rotation*), whose cycles are the **vertices**: `s` rotates a dart
  to the next dart around the same vertex, in the cyclic order induced by the surface;
* a fixed-point-free involution `e`, whose cycles are the **edges**: `e` exchanges the two
  darts of an edge.

The **faces** are then the cycles of `s * e`.  Thus

* `V = norb s D`, `E = norb e D`, `F = norb (s * e) D`.

Being drawn on a *sphere* (as opposed to some surface of higher genus) is the combinatorial
content of Euler's formula, and it has to enter the statement.  We encode it, as is standard,
by the inductive generation of spherical maps: starting from the map consisting of a single
edge, every polyhedral surface is obtained by repeatedly

* attaching a new edge with a new endpoint of degree one at some corner (`pendant`), or
* drawing a new edge inside an existing face, joining two corners of that face (`chord`).

Both moves are drawings on the sphere, and every map drawn on the sphere arises this way.
The main theorem `Chem.euler_polyhedron` states that any such map satisfies

`V + F = E + 2`,  i.e.  `V - E + F = 2`.
-/

namespace Chem

open Equiv Equiv.Perm Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- A map drawn on the sphere, in the dart model: `D` is the set of darts, `s` the rotation
(its cycles are the vertices) and `e` the edge involution (its cycles are the edges).

The three constructors are: a single edge; attaching a pendant edge (a new vertex of degree
one) at the corner following the dart `x`; and drawing a chord inside a face, joining the
corner following `x` to the corner following `y`, both corners lying on a common face.
In the last two cases `c` and `d` are the two new darts of the new edge. -/
inductive IsSphereMap : Finset α → Perm α → Perm α → Prop
  | edge {a b : α} (hab : a ≠ b) : IsSphereMap {a, b} 1 (swap a b)
  | pendant {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {x c d : α} (hx : x ∈ D)
      (hc : c ∉ D) (hd : d ∉ insert c D) :
      IsSphereMap (insert c (insert d D)) (swap (s x) c * s) (swap c d * e)
  | chord {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) {x y c d : α} (hx : x ∈ D)
      (hy : y ∈ D) (hxy : x ≠ y) (hface : (s * e).SameCycle (s x) (s y))
      (hc : c ∉ D) (hd : d ∉ insert c D) :
      IsSphereMap (insert c (insert d D)) (swap (s x) c * (swap (s y) d * s)) (swap c d * e)

/-- The number of vertices of a map: the number of cycles of the rotation. -/
def numV (D : Finset α) (s : Perm α) : ℕ := norb s D

/-- The number of edges of a map: the number of cycles of the edge involution. -/
def numE (D : Finset α) (e : Perm α) : ℕ := norb e D

/-- The number of faces of a map: the number of cycles of `s * e`. -/
def numF (D : Finset α) (s e : Perm α) : ℕ := norb (s * e) D

/-! ### Basic invariants -/

omit [Fintype α] in
lemma swap_apply_mem {S : Finset α} {u v w : α} (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) :
    swap u v w ∈ S := by
  rw [swap_apply_def]
  split_ifs <;> assumption

omit [DecidableEq α] [Fintype α] in
lemma not_sameCycle_of_fixed {π : Perm α} {u v : α} (hfix : π v = v) (hne : u ≠ v) :
    ¬ π.SameCycle u v := fun h => hne (sameCycle_fixed hfix h.symm)

omit [Fintype α] in
/-- Structural invariants: both permutations fix every dart outside `D` and preserve `D`. -/
lemma IsSphereMap.invariants {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    (∀ z ∉ D, s z = z ∧ e z = z) ∧ (∀ z ∈ D, s z ∈ D ∧ e z ∈ D) := by
  induction h with
  | @edge a b hab =>
      constructor
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        exact ⟨rfl, swap_apply_of_ne_of_ne hz.1 hz.2⟩
      · intro z hz
        exact ⟨by simpa using hz, swap_apply_mem (by simp) (by simp) hz⟩
  | @pendant D s e h x c d hx hc hd ih =>
      obtain ⟨ihout, ihin⟩ := ih
      have hsub : D ⊆ insert c (insert d D) := fun w hw => by simp [hw]
      have hcmem : c ∈ insert c (insert d D) := by simp
      have hdmem : d ∈ insert c (insert d D) := by simp
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hsx : s x ∈ D := (ihin x hx).1
      constructor
      · intro z hz
        simp only [Finset.mem_insert, not_or] at hz
        obtain ⟨hzc, hzd, hzD⟩ := hz
        refine ⟨?_, ?_⟩
        · rw [Perm.mul_apply, (ihout z hzD).1,
            swap_apply_of_ne_of_ne (fun hcon => hzD (by rw [hcon]; exact hsx)) hzc]
        · rw [Perm.mul_apply, (ihout z hzD).2, swap_apply_of_ne_of_ne hzc hzd]
      · intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzD
        · refine ⟨?_, ?_⟩
          · rw [Perm.mul_apply, (ihout z hc).1]
            exact swap_apply_mem (hsub hsx) hcmem hcmem
          · rw [Perm.mul_apply, (ihout z hc).2]
            exact swap_apply_mem hcmem hdmem hcmem
        · refine ⟨?_, ?_⟩
          · rw [Perm.mul_apply, (ihout z hdD).1]
            exact swap_apply_mem (hsub hsx) hcmem hdmem
          · rw [Perm.mul_apply, (ihout z hdD).2]
            exact swap_apply_mem hcmem hdmem hdmem
        · refine ⟨?_, ?_⟩
          · rw [Perm.mul_apply]
            exact swap_apply_mem (hsub hsx) hcmem (hsub (ihin z hzD).1)
          · rw [Perm.mul_apply]
            exact swap_apply_mem hcmem hdmem (hsub (ihin z hzD).2)
  | @chord D s e h x y c d hx hy hxy hface hc hd ih =>
      obtain ⟨ihout, ihin⟩ := ih
      have hsub : D ⊆ insert c (insert d D) := fun w hw => by simp [hw]
      have hcmem : c ∈ insert c (insert d D) := by simp
      have hdmem : d ∈ insert c (insert d D) := by simp
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hsx : s x ∈ D := (ihin x hx).1
      have hsy : s y ∈ D := (ihin y hy).1
      have hstep : ∀ w : α, s w ∈ insert c (insert d D) →
          (swap (s x) c * (swap (s y) d * s)) w ∈ insert c (insert d D) := by
        intro w hw
        rw [Perm.mul_apply, Perm.mul_apply]
        exact swap_apply_mem (hsub hsx) hcmem (swap_apply_mem (hsub hsy) hdmem hw)
      constructor
      · intro z hz
        simp only [Finset.mem_insert, not_or] at hz
        obtain ⟨hzc, hzd, hzD⟩ := hz
        refine ⟨?_, ?_⟩
        · rw [Perm.mul_apply, Perm.mul_apply, (ihout z hzD).1,
            swap_apply_of_ne_of_ne (fun hcon => hzD (by rw [hcon]; exact hsy)) hzd,
            swap_apply_of_ne_of_ne (fun hcon => hzD (by rw [hcon]; exact hsx)) hzc]
        · rw [Perm.mul_apply, (ihout z hzD).2, swap_apply_of_ne_of_ne hzc hzd]
      · intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzD
        · exact ⟨hstep z (by rw [(ihout z hc).1]; exact hcmem), by
            rw [Perm.mul_apply, (ihout z hc).2]; exact swap_apply_mem hcmem hdmem hcmem⟩
        · exact ⟨hstep z (by rw [(ihout z hdD).1]; exact hdmem), by
            rw [Perm.mul_apply, (ihout z hdD).2]; exact swap_apply_mem hcmem hdmem hdmem⟩
        · exact ⟨hstep z (hsub (ihin z hzD).1), by
            rw [Perm.mul_apply]; exact swap_apply_mem hcmem hdmem (hsub (ihin z hzD).2)⟩

omit [Fintype α] in
lemma IsSphereMap.fixes_outside {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    ∀ z ∉ D, s z = z ∧ e z = z := h.invariants.1

omit [Fintype α] in
lemma IsSphereMap.maps_into {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    ∀ z ∈ D, s z ∈ D ∧ e z ∈ D := h.invariants.2

/-! ### Euler's formula -/

omit [Fintype α] in
lemma comm_swap_of_fixed {s : Perm α} {c d : α} (hc : s c = c) (hd : s d = d) :
    s * swap c d = swap c d * s := by
  have h := Equiv.swap_apply_apply s c d
  rw [hc, hd] at h
  conv_rhs => rw [h]
  group

lemma norb_insert_two {π : Perm α} {D : Finset α} {c d : α} (hc : c ∉ D) (hd : d ∉ insert c D)
    (hfc : π c = c) (hfd : π d = d) :
    norb π (insert c (insert d D)) = norb π D + 2 := by
  have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
  have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
  have h2 : c ∉ insert d D := by simp [hcd, hc]
  rw [norb_insert_of_fixed h2 hfc, norb_insert_of_fixed hdD hfd]

/-- A dart of the old map is not in the cycle created by gluing two new fixed points. -/
lemma not_sameCycle_swap_mul_fixed {π : Perm α} {u c d : α} (hfc : π c = c) (hfd : π d = d)
    (hcd : c ≠ d) (huc : u ≠ c) (hud : u ≠ d) : ¬ (swap c d * π).SameCycle u c := by
  rw [sameCycle_swap_mul_iff (not_sameCycle_of_fixed hfd hcd)]
  rintro (hcon | ⟨hcon | hcon, -⟩)
  · exact not_sameCycle_of_fixed hfc huc hcon
  · exact not_sameCycle_of_fixed hfc huc hcon
  · exact not_sameCycle_of_fixed hfd hud hcon

lemma not_sameCycle_swap_mul_fixed' {π : Perm α} {u c d : α} (hfc : π c = c) (hfd : π d = d)
    (hcd : c ≠ d) (huc : u ≠ c) (hud : u ≠ d) : ¬ (swap c d * π).SameCycle u d := by
  have h := not_sameCycle_swap_mul_fixed (c := d) (d := c) hfd hfc hcd.symm hud huc
  rwa [swap_comm] at h

lemma norb_singleton (π : Perm α) (z : α) : norb π {z} = 1 := by
  simp [norb]

lemma norb_pair_one {a b : α} (hab : a ≠ b) : norb (1 : Perm α) {a, b} = 2 := by
  have hnotmem : a ∉ ({b} : Finset α) := by simpa using hab
  rw [show ({a, b} : Finset α) = insert a {b} from rfl,
    norb_insert_of_fixed hnotmem (by simp), norb_singleton]

lemma norb_pair_swap {a b : α} (hab : a ≠ b) : norb (swap a b) {a, b} = 1 := by
  have hsame : (swap a b).SameCycle a b := ⟨1, by simp⟩
  have h : ∀ z ∈ ({a, b} : Finset α), cyc (swap a b) {a, b} z = {a, b} := by
    intro z hz
    have : cyc (swap a b) {a, b} a = {a, b} := by
      ext w
      simp only [mem_cyc, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, -⟩; exact hw
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, SameCycle.refl _ _⟩
        · exact ⟨Or.inr rfl, hsame⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact this
    · rw [Finset.mem_singleton] at hz
      subst hz
      rw [← cyc_eq_of_sameCycle hsame]
      exact this
  unfold norb
  rw [Finset.image_congr (g := fun _ => ({a, b} : Finset α)) (fun z hz => h z hz),
    Finset.image_const ⟨a, by simp⟩]
  simp

/-- **Euler's polyhedron formula**: for a map drawn on the sphere (the combinatorial
description of the surface of a convex polyhedron), `V - E + F = 2`. -/
theorem euler_polyhedron {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    numV D s + numF D s e = numE D e + 2 := by
  unfold numV numE numF
  induction h with
  | @edge a b hab =>
      rw [norb_pair_one hab, norb_pair_swap hab, one_mul, norb_pair_swap hab]
  | @pendant D s e h x c d hx hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
      have hsx : s x ∈ D := (h.maps_into x hx).1
      have hsc : s c = c := (h.fixes_outside c hc).1
      have hsd : s d = d := (h.fixes_outside d hdD).1
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      have hphic : (s * e) c = c := by rw [Perm.mul_apply, hec, hsc]
      have hphid : (s * e) d = d := by rw [Perm.mul_apply, hed, hsd]
      have hcmem : c ∈ insert c (insert d D) := by simp
      have hdmem : d ∈ insert c (insert d D) := by simp
      have hsxmem : s x ∈ insert c (insert d D) := by simp [hsx]
      have hsxc : s x ≠ c := fun hcon => hc (hcon ▸ hsx)
      have hsxd : s x ≠ d := fun hcon => hdD (hcon ▸ hsx)
      -- vertices: the new dart `c` joins the vertex of `x`, `d` is a new vertex
      have hV : norb (swap (s x) c * s) (insert c (insert d D)) + 1 = norb s D + 2 := by
        rw [norb_swap_mul_of_not_sameCycle hsxmem hcmem (not_sameCycle_of_fixed hsc hsxc)]
        exact norb_insert_two hc hd hsc hsd
      -- edges: one new edge
      have hE : norb (swap c d * e) (insert c (insert d D)) + 1 = norb e D + 2 := by
        rw [norb_swap_mul_of_not_sameCycle hcmem hdmem (not_sameCycle_of_fixed hed hcd)]
        exact norb_insert_two hc hd hec hed
      -- faces: unchanged
      have hphi : (swap (s x) c * s) * (swap c d * e) = swap (s x) c * (swap c d * (s * e)) := by
        calc (swap (s x) c * s) * (swap c d * e)
            = swap (s x) c * ((s * swap c d) * e) := by group
          _ = swap (s x) c * ((swap c d * s) * e) := by rw [comm_swap_of_fixed hsc hsd]
          _ = swap (s x) c * (swap c d * (s * e)) := by group
      have hF : norb ((swap (s x) c * s) * (swap c d * e)) (insert c (insert d D))
          = norb (s * e) D := by
        rw [hphi]
        have h1 : norb (swap c d * (s * e)) (insert c (insert d D)) + 1 = norb (s * e) D + 2 := by
          rw [norb_swap_mul_of_not_sameCycle hcmem hdmem (not_sameCycle_of_fixed hphid hcd)]
          exact norb_insert_two hc hd hphic hphid
        have h2 : norb (swap (s x) c * (swap c d * (s * e))) (insert c (insert d D)) + 1
            = norb (swap c d * (s * e)) (insert c (insert d D)) :=
          norb_swap_mul_of_not_sameCycle hsxmem hcmem
            (not_sameCycle_swap_mul_fixed hphic hphid hcd hsxc hsxd)
        omega
      omega
  | @chord D s e h x y c d hx hy hxy hface hc hd ih =>
      have hdD : d ∉ D := fun hcon => hd (by simp [hcon])
      have hcd : c ≠ d := fun hcon => hd (by simp [hcon])
      have hsx : s x ∈ D := (h.maps_into x hx).1
      have hsy : s y ∈ D := (h.maps_into y hy).1
      have hsxy : s x ≠ s y := fun hcon => hxy (s.injective hcon)
      have hsc : s c = c := (h.fixes_outside c hc).1
      have hsd : s d = d := (h.fixes_outside d hdD).1
      have hec : e c = c := (h.fixes_outside c hc).2
      have hed : e d = d := (h.fixes_outside d hdD).2
      have hphic : (s * e) c = c := by rw [Perm.mul_apply, hec, hsc]
      have hphid : (s * e) d = d := by rw [Perm.mul_apply, hed, hsd]
      have hcmem : c ∈ insert c (insert d D) := by simp
      have hdmem : d ∈ insert c (insert d D) := by simp
      have hsxmem : s x ∈ insert c (insert d D) := by simp [hsx]
      have hsymem : s y ∈ insert c (insert d D) := by simp [hsy]
      have hsxc : s x ≠ c := fun hcon => hc (hcon ▸ hsx)
      have hsxd : s x ≠ d := fun hcon => hdD (hcon ▸ hsx)
      have hsyc : s y ≠ c := fun hcon => hc (hcon ▸ hsy)
      have hsyd : s y ≠ d := fun hcon => hdD (hcon ▸ hsy)
      -- vertices: unchanged
      have hV : norb (swap (s x) c * (swap (s y) d * s)) (insert c (insert d D))
          = norb s D := by
        have h1 : norb (swap (s y) d * s) (insert c (insert d D)) + 1 = norb s D + 2 := by
          rw [norb_swap_mul_of_not_sameCycle hsymem hdmem (not_sameCycle_of_fixed hsd hsyd)]
          exact norb_insert_two hc hd hsc hsd
        have hnot : ¬ (swap (s y) d * s).SameCycle (s x) c := by
          rw [sameCycle_swap_mul_iff (not_sameCycle_of_fixed hsd hsyd)]
          rintro (hcon | ⟨-, hcon | hcon⟩)
          · exact not_sameCycle_of_fixed hsc hsxc hcon
          · exact hsyc (sameCycle_fixed hsc hcon)
          · exact hcd (sameCycle_fixed hsc hcon).symm
        have h2 : norb (swap (s x) c * (swap (s y) d * s)) (insert c (insert d D)) + 1
            = norb (swap (s y) d * s) (insert c (insert d D)) :=
          norb_swap_mul_of_not_sameCycle hsxmem hcmem hnot
        omega
      -- edges: one new edge
      have hE : norb (swap c d * e) (insert c (insert d D)) + 1 = norb e D + 2 := by
        rw [norb_swap_mul_of_not_sameCycle hcmem hdmem (not_sameCycle_of_fixed hed hcd)]
        exact norb_insert_two hc hd hec hed
      -- faces: the face containing both corners is split in two
      have hphi : (swap (s x) c * (swap (s y) d * s)) * (swap c d * e)
          = swap (s x) c * (swap (s y) d * (swap c d * (s * e))) := by
        calc (swap (s x) c * (swap (s y) d * s)) * (swap c d * e)
            = swap (s x) c * (swap (s y) d * ((s * swap c d) * e)) := by group
          _ = swap (s x) c * (swap (s y) d * ((swap c d * s) * e)) := by
              rw [comm_swap_of_fixed hsc hsd]
          _ = swap (s x) c * (swap (s y) d * (swap c d * (s * e))) := by group
      have hnotcd : ¬ (s * e).SameCycle c d := not_sameCycle_of_fixed hphid hcd
      have hF : norb ((swap (s x) c * (swap (s y) d * s)) * (swap c d * e))
          (insert c (insert d D)) = norb (s * e) D + 1 := by
        rw [hphi]
        have h1 : norb (swap c d * (s * e)) (insert c (insert d D)) + 1 = norb (s * e) D + 2 := by
          rw [norb_swap_mul_of_not_sameCycle hcmem hdmem hnotcd]
          exact norb_insert_two hc hd hphic hphid
        have h2 : norb (swap (s y) d * (swap c d * (s * e))) (insert c (insert d D)) + 1
            = norb (swap c d * (s * e)) (insert c (insert d D)) :=
          norb_swap_mul_of_not_sameCycle hsymem hdmem
            (not_sameCycle_swap_mul_fixed' hphic hphid hcd hsyc hsyd)
        have hsame : (swap (s y) d * (swap c d * (s * e))).SameCycle (s x) c := by
          rw [sameCycle_swap_mul_iff (not_sameCycle_swap_mul_fixed' hphic hphid hcd hsyc hsyd)]
          refine Or.inr ⟨Or.inl ?_, Or.inr ?_⟩
          · rw [sameCycle_swap_mul_iff hnotcd]
            exact Or.inl hface
          · exact sameCycle_swap_mul_xy hnotcd
        have h3 : norb (swap (s x) c * (swap (s y) d * (swap c d * (s * e))))
            (insert c (insert d D))
            = norb (swap (s y) d * (swap c d * (s * e))) (insert c (insert d D)) + 1 :=
          norb_swap_mul_of_sameCycle hsxmem hcmem hsxc hsame
        omega
      omega

/-- Euler's formula in its usual subtracted form over `ℤ`: `V - E + F = 2`. -/
theorem euler_polyhedron_sub {D : Finset α} {s e : Perm α} (h : IsSphereMap D s e) :
    (numV D s : ℤ) - (numE D e : ℤ) + (numF D s e : ℤ) = 2 := by
  have hE := euler_polyhedron h
  omega

end Chem

import Mathlib
import RequestProject.PermOrbits
import RequestProject.EulerPolyhedron
import RequestProject.Fullerene
import RequestProject.Examples

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


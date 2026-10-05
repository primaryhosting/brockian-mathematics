import Mathlib

/-!
# Paris Harrington
Category: Frontier — Set Theory
Target: Frontier.Paris_Harrington
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

set_option grind.warning false

namespace Frontier

namespace ParisHarrington

open Filter

/-- A fixed ultrafilter on `ℕ` refining the filter `atTop`; in particular every cofinite
set belongs to it. -/
noncomputable def Ultra : Ultrafilter ℕ := Ultrafilter.of Filter.atTop

lemma mem_Ultra_of_mem_atTop {s : Set ℕ} (hs : s ∈ (Filter.atTop : Filter ℕ)) :
    s ∈ Ultra := Ultrafilter.of_le _ hs

lemma exists_ulim {k : ℕ} (g : ℕ → Fin k) : ∃ j, {x | g x = j} ∈ Ultra := by
  have h : (⋃ j ∈ (Set.univ : Set (Fin k)), {x | g x = j}) ∈ Ultra := by
    have h2 : (⋃ j ∈ (Set.univ : Set (Fin k)), {x | g x = j}) = Set.univ := by
      ext x; simp
    rw [h2]; exact Filter.univ_mem
  obtain ⟨j, -, hj⟩ := (Ultrafilter.finite_biUnion_mem_iff Set.finite_univ).1 h
  exact ⟨j, hj⟩

/-- The `Ultra`-limit of a function with values in a finite type. -/
noncomputable def ulim {k : ℕ} (g : ℕ → Fin k) : Fin k := (exists_ulim g).choose

lemma ulim_spec {k : ℕ} (g : ℕ → Fin k) : {x | g x = ulim g} ∈ Ultra :=
  (exists_ulim g).choose_spec

section Ramsey

variable {k : ℕ}

/-- Successive ultrafilter-limits of a colouring `c` of finite sets of naturals. -/
noncomputable def D (c : Finset ℕ → Fin k) : ℕ → Finset ℕ → Fin k
  | 0 => c
  | (r + 1) => fun t => ulim (fun x => D c r (insert x t))

lemma D_zero (c : Finset ℕ → Fin k) (t : Finset ℕ) : D c 0 t = c t := rfl

lemma D_succ (c : Finset ℕ → Fin k) (r : ℕ) (t : Finset ℕ) :
    D c (r + 1) t = ulim (fun x => D c r (insert x t)) := rfl

lemma good_mem_Ultra (c : Finset ℕ → Fin k) (r : ℕ) (t : Finset ℕ) :
    {x | D c r (insert x t) = D c (r + 1) t} ∈ Ultra := by
  simpa [D_succ] using ulim_spec (fun x => D c r (insert x t))

lemma pick_exists (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) :
    ∃ x, (∀ y ∈ A, y < x) ∧
      ∀ t ∈ A.powerset, ∀ q ≤ n, D c q (insert x t) = D c (q + 1) t := by
  have h1 : {x : ℕ | ∀ y ∈ A, y < x} ∈ Ultra := by
    refine mem_Ultra_of_mem_atTop ?_
    filter_upwards [eventually_ge_atTop (A.sup id + 1)] with x hx y hy
    have : y ≤ A.sup id := Finset.le_sup (f := id) hy
    omega
  have h2 : (⋂ t ∈ A.powerset, ⋂ q ∈ Finset.range (n + 1),
      {x : ℕ | D c q (insert x t) = D c (q + 1) t}) ∈ Ultra :=
    (Filter.biInter_finset_mem _).2 fun t _ =>
      (Filter.biInter_finset_mem _).2 fun q _ => good_mem_Ultra c q t
  obtain ⟨x, hx1, hx2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  refine ⟨x, hx1, fun t ht q hq => ?_⟩
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx2
  exact hx2 t ht q (Finset.mem_range.2 (by omega))

/-- A choice of a next element of the homogeneous set, given the finite set `A` of already
chosen elements. -/
noncomputable def pick (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) : ℕ :=
  (pick_exists c n A).choose

lemma pick_gt (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) :
    ∀ y ∈ A, y < pick c n A := (pick_exists c n A).choose_spec.1

lemma pick_good (c : Finset ℕ → Fin k) (n : ℕ) (A : Finset ℕ) :
    ∀ t ∈ A.powerset, ∀ q ≤ n, D c q (insert (pick c n A) t) = D c (q + 1) t :=
  (pick_exists c n A).choose_spec.2

/-- The finite set of the first `i` chosen elements. -/
noncomputable def chosen (c : Finset ℕ → Fin k) (n : ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | (i + 1) => insert (pick c n (chosen c n i)) (chosen c n i)

/-- The `i`-th chosen element. -/
noncomputable def seq (c : Finset ℕ → Fin k) (n : ℕ) (i : ℕ) : ℕ :=
  pick c n (chosen c n i)

lemma chosen_eq_image (c : Finset ℕ → Fin k) (n : ℕ) (i : ℕ) :
    chosen c n i = (Finset.range i).image (seq c n) := by
  induction i with
  | zero => simp [chosen]
  | succ i ih =>
      rw [Finset.range_add_one, Finset.image_insert, ← ih]
      rfl

lemma seq_lt_succ (c : Finset ℕ → Fin k) (n i : ℕ) : seq c n i < seq c n (i + 1) := by
  have hmem : seq c n i ∈ chosen c n (i + 1) := by
    rw [chosen]
    exact Finset.mem_insert_self _ _
  exact pick_gt c n (chosen c n (i + 1)) _ hmem

lemma seq_strictMono (c : Finset ℕ → Fin k) (n : ℕ) : StrictMono (seq c n) :=
  strictMono_nat_of_lt_succ (seq_lt_succ c n)

lemma D_of_subset_range (c : Finset ℕ → Fin k) (n : ℕ) :
    ∀ (r q : ℕ), q + r ≤ n → ∀ t : Finset ℕ, (↑t ⊆ Set.range (seq c n)) → t.card = r →
      D c q t = D c (q + r) ∅ := by
  intro r
  induction r with
  | zero =>
      intro q _ t _ hcard
      have ht0 : t = ∅ := Finset.card_eq_zero.1 hcard
      subst ht0
      simp
  | succ r ih =>
      intro q hq t ht hcard
      have hne : t.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨j, hj⟩ : t.max' hne ∈ Set.range (seq c n) :=
        ht (Finset.mem_coe.2 (t.max'_mem hne))
      have hxt : t.max' hne ∈ t := t.max'_mem hne
      have hcard' : (t.erase (t.max' hne)).card = r := by
        rw [Finset.card_erase_of_mem hxt, hcard]
        omega
      have hsub' : ↑(t.erase (t.max' hne)) ⊆ Set.range (seq c n) := by
        intro y hy
        exact ht (Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hy)))
      have hins : insert (t.max' hne) (t.erase (t.max' hne)) = t := Finset.insert_erase hxt
      have hchosen : t.erase (t.max' hne) ⊆ chosen c n j := by
        intro y hy
        have hyt : y ∈ t := Finset.mem_of_mem_erase hy
        obtain ⟨l, hl⟩ : y ∈ Set.range (seq c n) := ht (Finset.mem_coe.2 hyt)
        have hylt : y < t.max' hne :=
          lt_of_le_of_ne (t.le_max' y hyt) (Finset.ne_of_mem_erase hy)
        have hlj : l < j := by
          have : seq c n l < seq c n j := by rw [hl, hj]; exact hylt
          exact (seq_strictMono c n).lt_iff_lt.1 this
        rw [chosen_eq_image]
        exact Finset.mem_image.2 ⟨l, Finset.mem_range.2 hlj, hl⟩
      have hpx : pick c n (chosen c n j) = t.max' hne := hj
      have hgood := pick_good c n (chosen c n j) (t.erase (t.max' hne))
        (Finset.mem_powerset.2 hchosen) q (by omega)
      rw [hpx, hins] at hgood
      rw [hgood, ih (q + 1) (by omega) _ hsub' hcard']
      congr 1
      omega

/-- **Infinite Ramsey theorem** (for `n`-element subsets and `k` colours): for every colouring
`c` of the finite subsets of `ℕ` with `k` colours there is a strictly monotone `f : ℕ → ℕ`
such that all `n`-element subsets of the range of `f` receive the same colour. -/
theorem infinite_ramsey (n : ℕ) (c : Finset ℕ → Fin k) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ j : Fin k,
      ∀ s : Finset ℕ, ↑s ⊆ Set.range f → s.card = n → c s = j := by
  refine ⟨seq c n, seq_strictMono c n, D c n ∅, fun s hs hcard => ?_⟩
  have h := D_of_subset_range c n n 0 (by omega) s hs hcard
  simpa [D_zero] using h

end Ramsey

end ParisHarrington

/-- **The Paris–Harrington theorem** (strengthened finite Ramsey theorem).

For all `n`, `k`, `m` there is `N` such that for every colouring `c` of the `n`-element
subsets of `[m, N]` with `k` colours there is a subset `H ⊆ [m, N]` which is

* homogeneous for `c` (all its `n`-element subsets get the same colour `j`),
* of size at least `m`, and
* *relatively large*: it has a least element `a` with `a ≤ |H|`.

(The colouring is quantified over all colourings of finite subsets of `ℕ`, which is
equivalent since any partial colouring extends.)

This statement is true, as proved here, but it is not provable in first-order Peano
arithmetic; the unprovability half is a metamathematical statement about `PA` and is not
formalized here. -/
theorem Paris_Harrington (n k m : ℕ) :
    ∃ N : ℕ, ∀ c : Finset ℕ → Fin k, ∃ H : Finset ℕ,
      H ⊆ Finset.Icc m N ∧ m ≤ H.card ∧
      (∃ a ∈ H, (∀ b ∈ H, a ≤ b) ∧ a ≤ H.card) ∧
      ∃ j : Fin k, ∀ s ⊆ H, s.card = n → c s = j := by
  classical
  by_contra hcon
  have hbad : ∀ N : ℕ, ∃ c : Finset ℕ → Fin k, ∀ H : Finset ℕ,
      ¬(H ⊆ Finset.Icc m N ∧ m ≤ H.card ∧
        (∃ a ∈ H, (∀ b ∈ H, a ≤ b) ∧ a ≤ H.card) ∧
        ∃ j : Fin k, ∀ s ⊆ H, s.card = n → c s = j) := by
    intro N
    by_contra h
    push_neg at h
    exact hcon ⟨N, h⟩
  choose bad hbadspec using hbad
  set c : Finset ℕ → Fin k := fun s => ParisHarrington.ulim (fun N => bad N s) with hc
  obtain ⟨f, hf, j, hj⟩ := ParisHarrington.infinite_ramsey n c
  have hfm : m ≤ f m := hf.le_apply
  set H : Finset ℕ := (Finset.Ico m (m + f m + 1)).image f with hH
  have hmemH : ∀ x ∈ H, ∃ i, m ≤ i ∧ i ≤ m + f m ∧ f i = x := by
    intro x hx
    rw [hH, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_Ico] at hi
    exact ⟨i, hi.1, by omega, rfl⟩
  have hcardH : H.card = f m + 1 := by
    rw [hH, Finset.card_image_of_injective _ hf.injective, Nat.card_Ico]
    omega
  have hfmH : f m ∈ H := by
    rw [hH]
    exact Finset.mem_image.2 ⟨m, Finset.mem_Ico.2 ⟨le_refl m, by omega⟩, rfl⟩
  have hminH : ∀ b ∈ H, f m ≤ b := by
    intro b hb
    obtain ⟨i, hi, -, rfl⟩ := hmemH b hb
    exact hf.monotone hi
  have hsubrange : (↑H : Set ℕ) ⊆ Set.range f := by
    intro x hx
    obtain ⟨i, -, -, rfl⟩ := hmemH x (Finset.mem_coe.1 hx)
    exact ⟨i, rfl⟩
  -- choose a large index `N` at which the limiting colouring agrees with `bad N`
  have h1 : {N : ℕ | f (m + f m) ≤ N} ∈ ParisHarrington.Ultra := by
    refine ParisHarrington.mem_Ultra_of_mem_atTop ?_
    filter_upwards [Filter.eventually_ge_atTop (f (m + f m))] with N hN using hN
  have h2 : (⋂ s ∈ H.powerset, {N : ℕ | bad N s = c s}) ∈ ParisHarrington.Ultra :=
    (Filter.biInter_finset_mem _).2 fun s _ => ParisHarrington.ulim_spec (fun N => bad N s)
  obtain ⟨N, hN1, hN2⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem h1 h2)
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hN1 hN2
  refine hbadspec N H ⟨?_, ?_, ⟨f m, hfmH, hminH, by omega⟩, j, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hi2, rfl⟩ := hmemH x hx
    exact Finset.mem_Icc.2 ⟨le_trans hi hf.le_apply, le_trans (hf.monotone hi2) hN1⟩
  · omega
  · intro s hs hcard
    rw [hN2 s (Finset.mem_powerset.2 hs)]
    exact hj s (fun x hx => hsubrange (Finset.mem_coe.2 (hs (Finset.mem_coe.1 hx)))) hcard

end Frontier


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

import Mathlib
import RequestProject.RS.Degree

/-!
# Probabilistic polynomial approximation of `AC⁰[q]` circuits

The Razborov–Smolensky approximation lemma: a circuit of size `s` and depth `d` over
`{¬, ∧, ∨, MOD q}` can be approximated over a field of characteristic `q` by a function of
degree `(ℓ (q-1))^d` which errs on at most `s · 2^(n-ℓ)` inputs.
-/

set_option maxHeartbeats 1000000

namespace CS

open Finset

variable {F : Type*} [Field F] {n q : ℕ}

/-- The set of inputs on which `g` differs from the Boolean function `h`. -/
noncomputable def errSet (g : Cube n → F) (h : Cube n → Bool) : Finset (Cube n) :=
  @Finset.filter _ (fun x => g x ≠ boolF F (h x)) (Classical.decPred _) Finset.univ

lemma mem_errSet {g : Cube n → F} {h : Cube n → Bool} {x : Cube n} :
    x ∈ errSet g h ↔ g x ≠ boolF F (h x) := by
  simp [errSet, Finset.mem_filter]

lemma card_errSet_le {g : Cube n → F} {h : Cube n → Bool} {E : Finset (Cube n)}
    (hE : ∀ x, x ∉ E → g x = boolF F (h x)) : (errSet g h).card ≤ E.card := by
  refine Finset.card_le_card fun x hx => ?_
  by_contra hxE
  exact (mem_errSet.1 hx) (hE x hxE)

lemma boolF_not (b : Bool) : boolF F (!b) = 1 - boolF F b := by
  cases b <;> simp [boolF]

lemma errSet_one_sub (g : Cube n → F) (h : Cube n → Bool) :
    errSet (1 - g) (fun x => !(h x)) = errSet g h := by
  ext x
  simp only [mem_errSet, Pi.sub_apply, Pi.one_apply, boolF_not, ne_eq, sub_right_inj]

/-- In characteristic `q`, the `(q-1)`-st power of a natural number is the indicator of
non-divisibility by `q`. -/
lemma natCast_pow_sub_one [CharP F q] (hq : q.Prime) (m : ℕ) :
    ((m : F)) ^ (q - 1) = if q ∣ m then 0 else 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  by_cases h : q ∣ m
  · have h0 : (m : F) = 0 := by rwa [CharP.cast_eq_zero_iff F q]
    rw [h0, if_pos h, zero_pow]
    have := hq.two_le
    omega
  · rw [if_neg h]
    have hz : ((m : ZMod q)) ≠ 0 := fun hc => h ((CharP.cast_eq_zero_iff (ZMod q) q m).1 hc)
    have hone := ZMod.pow_card_sub_one_eq_one hz
    have hmap : ((m : F)) = (ZMod.castHom (dvd_refl q) F) (m : ZMod q) := by simp
    rw [hmap, ← map_pow, hone, map_one]

/-- The approximating polynomial for an `OR` gate given a choice of random subsets `ω`. -/
noncomputable def orPoly (q : ℕ) {n k ℓ : ℕ} (ω : Fin ℓ → Fin k → Bool)
    (u : Fin k → Cube n → F) : Cube n → F :=
  fun x => 1 - ∏ j : Fin ℓ, (1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1))

lemma orPoly_mem_Deg {k ℓ D : ℕ} (ω : Fin ℓ → Fin k → Bool) (u : Fin k → Cube n → F)
    (hu : ∀ i, u i ∈ Deg F n D) : orPoly q ω u ∈ Deg F n (ℓ * ((q - 1) * D)) := by
  have hfac : ∀ j : Fin ℓ,
      (fun x => 1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1)) ∈ Deg F n ((q - 1) * D) := by
    intro j
    have hs : (fun x => ∑ i, if ω j i then u i x else 0) ∈ Deg F n D := by
      have hrw : (fun x => ∑ i, if ω j i then u i x else 0)
          = ∑ i : Fin k, (fun x => if ω j i then u i x else 0) := by
        funext x; simp
      rw [hrw]
      refine Deg_sum _ _ _ fun i _ => ?_
      cases h : ω j i
      · simpa [h] using Submodule.zero_mem (Deg F n D)
      · simpa [h] using hu i
    have hpow := Deg_pow (t := q - 1) hs
    rw [show ((fun x => ∑ i, if ω j i then u i x else 0) : Cube n → F) ^ (q - 1)
        = (fun x => (∑ i, if ω j i then u i x else 0) ^ (q - 1)) from by funext x; simp] at hpow
    exact Submodule.sub_mem _ (Deg_mono (Nat.zero_le _) (one_mem_Deg 0)) hpow
  have h := Deg_prod (F := F) (n := n) Finset.univ
    (fun j : Fin ℓ => fun x => 1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1))
    (fun _ => (q - 1) * D) (fun j _ => hfac j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [show (∏ j : Fin ℓ, (fun x => 1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1)))
      = (fun x => ∏ j : Fin ℓ, (1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1))) from by
    funext x; simp] at h
  exact Submodule.sub_mem _ (Deg_mono (Nat.zero_le _) (one_mem_Deg 0)) h

/-- Evaluation of a selected sum at a point where all `u i` take the correct Boolean values. -/
lemma sel_sum_eq {k : ℕ} (u : Fin k → Cube n → F) (b : Fin k → Cube n → Bool) (x : Cube n)
    (hx : ∀ i, u i x = boolF F (b i x)) (S : Fin k → Bool) :
    (∑ i, if S i then u i x else 0) = ((cnt fun i => S i && b i x : ℕ) : F) := by
  classical
  rw [cnt, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hx i]
  cases hS : S i <;> cases hb : b i x <;> simp [boolF]

lemma cnt_eq_sum {k : ℕ} (g : Fin k → Bool) : cnt g = ∑ i, (if g i then 1 else 0) := by
  rw [cnt, Finset.card_filter]

/-- For a nonempty `T`, at most half of the subsets `S` satisfy `q ∣ |S ∩ T|`. -/
lemma card_bad_subsets_le {k : ℕ} (hq : 2 ≤ q) (T : Fin k → Bool) (i₀ : Fin k)
    (hi₀ : T i₀ = true) :
    2 * #{S : Fin k → Bool | q ∣ cnt fun i => S i && T i} ≤ 2 ^ k := by
  classical
  set A : Finset (Fin k → Bool) := {S : Fin k → Bool | q ∣ cnt fun i => S i && T i} with hA
  set σ : (Fin k → Bool) → (Fin k → Bool) := fun S i => if i = i₀ then !(S i) else S i with hσ
  have hsplit : ∀ g : Fin k → Bool,
      cnt g = (if g i₀ then 1 else 0) + ∑ i ∈ univ.erase i₀, (if g i then 1 else 0) := by
    intro g
    rw [cnt_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have htail : ∀ S : Fin k → Bool,
      (∑ i ∈ univ.erase i₀, (if σ S i && T i then 1 else 0))
        = ∑ i ∈ univ.erase i₀, (if S i && T i then 1 else 0) := by
    intro S
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ i₀ := (Finset.mem_erase.1 hi).1
    simp [hσ, hne]
  have hcnt : ∀ S : Fin k → Bool,
      (cnt fun i => σ S i && T i) = (cnt fun i => S i && T i) + 1 ∨
      (cnt fun i => σ S i && T i) + 1 = (cnt fun i => S i && T i) := by
    intro S
    rw [hsplit (fun i => σ S i && T i), hsplit (fun i => S i && T i), htail S]
    cases h : S i₀
    · left; simp [hσ, h, hi₀]
    · right; simp [hσ, h, hi₀]
  have hnodvd : ∀ m : ℕ, q ∣ m → ¬ q ∣ (m + 1) := by
    intro m h1 h2
    have h3 : q ∣ 1 := by simpa using Nat.dvd_sub' h2 h1
    have := Nat.le_of_dvd one_pos h3
    omega
  have hmaps : ∀ S ∈ A, σ S ∈ Aᶜ := by
    intro S hS
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_compl, hA, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcnt S with h | h
    · rw [h]; exact hnodvd _ hS
    · intro hdvd
      exact hnodvd _ hdvd (by rw [h]; exact hS)
  have hinj : Set.InjOn σ (A : Set (Fin k → Bool)) := by
    intro S _ S' _ h
    funext i
    have hi' := congrFun h i
    by_cases hi : i = i₀
    · subst hi
      simp only [hσ, if_pos rfl] at hi'
      simpa using hi'
    · simpa [hσ, hi] using hi'
  have hcard : A.card ≤ Aᶜ.card := Finset.card_le_card_of_injOn σ (fun S hS => hmaps S hS) hinj
  have htot : A.card + Aᶜ.card = 2 ^ k := by
    rw [Finset.card_add_card_compl]
    simp [Fintype.card_fun]
  omega

/-- The core probabilistic estimate: for a fixed input `x` at which all children are computed
correctly, at most a `2^{-ℓ}` fraction of the choices `ω` give a wrong answer. -/
lemma card_bad_omega_le {k ℓ : ℕ} (hq : q.Prime) [CharP F q] (u : Fin k → Cube n → F)
    (b : Fin k → Cube n → Bool) (x : Cube n) (hx : ∀ i, u i x = boolF F (b i x))
    (W : Finset (Fin ℓ → Fin k → Bool))
    (hW : ∀ ω ∈ W, orPoly q ω u x ≠ boolF F (decide (∃ i, b i x = true))) :
    W.card * 2 ^ ℓ ≤ 2 ^ (k * ℓ) := by
  classical
  by_cases hT : ∃ i, b i x = true
  · obtain ⟨i₀, hi₀⟩ := hT
    set BadS : Finset (Fin k → Bool) := {S : Fin k → Bool | q ∣ cnt fun i => S i && b i x}
      with hBadS
    have hsub : W ⊆ Fintype.piFinset (fun _ : Fin ℓ => BadS) := by
      intro ω hω
      simp only [Fintype.mem_piFinset, hBadS, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hc
      push_neg at hc
      obtain ⟨j, hj⟩ := hc
      apply hW ω hω
      have hprod : ∏ j' : Fin ℓ, (1 - (∑ i, if ω j' i then u i x else 0) ^ (q - 1)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        rw [sel_sum_eq u b x hx (ω j), natCast_pow_sub_one hq, if_neg hj]
        ring
      simp only [orPoly, hprod, sub_zero]
      rw [decide_eq_true (⟨i₀, hi₀⟩ : ∃ i, b i x = true)]
      simp [boolF]
    refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)) ?_
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc BadS.card ^ ℓ * 2 ^ ℓ = (2 * BadS.card) ^ ℓ := by rw [mul_pow]; ring
      _ ≤ (2 ^ k) ^ ℓ := Nat.pow_le_pow_left (card_bad_subsets_le hq.two_le _ i₀ hi₀) ℓ
      _ = 2 ^ (k * ℓ) := by rw [← pow_mul]
  · push_neg at hT
    have hWe : W = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun ω hω => ?_
      refine hW ω hω ?_
      have hz : ∀ j : Fin ℓ, (∑ i, if ω j i then u i x else 0) = 0 := by
        intro j
        rw [sel_sum_eq u b x hx (ω j)]
        have hc0 : (cnt fun i => ω j i && b i x) = 0 := by
          simp only [cnt, Finset.card_eq_zero]
          refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
          simp [hT i]
        rw [hc0]
        simp
      have hprod : ∏ j : Fin ℓ, (1 - (∑ i, if ω j i then u i x else 0) ^ (q - 1)) = 1 := by
        refine Finset.prod_eq_one fun j _ => ?_
        rw [hz j, zero_pow (by have := hq.two_le; omega), sub_zero]
      simp only [orPoly, hprod, sub_self]
      have hnex : ¬ ∃ i, b i x = true := by push_neg; exact hT
      rw [decide_eq_false hnex]
      simp [boolF]
    rw [hWe]
    simp

/-- Existence of a good choice of random subsets for an `OR` gate. -/
lemma exists_or_approx {k ℓ : ℕ} (hq : q.Prime) [CharP F q] (u : Fin k → Cube n → F)
    (b : Fin k → Cube n → Bool) (Bad : Finset (Cube n))
    (hgood : ∀ x, x ∉ Bad → ∀ i, u i x = boolF F (b i x)) :
    ∃ ω : Fin ℓ → Fin k → Bool,
      (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ
        ≤ Bad.card * 2 ^ ℓ + 2 ^ n := by
  classical
  set Ω := (Finset.univ : Finset (Fin ℓ → Fin k → Bool)) with hΩ
  set bad : (Fin ℓ → Fin k → Bool) → Cube n → Prop := fun ω x =>
    orPoly q ω u x ≠ boolF F (decide (∃ i, b i x = true)) with hbad
  have hcardΩ : Ω.card = 2 ^ (k * ℓ) := by
    simp only [hΩ, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      pow_mul]
  have hsplit : ∀ ω : Fin ℓ → Fin k → Bool,
      (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card
        ≤ Bad.card + #{x ∈ Finset.univ \ Bad | bad ω x} := by
    intro ω
    have hs : errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))
        ⊆ Bad ∪ {x ∈ Finset.univ \ Bad | bad ω x} := by
      intro x hx
      by_cases hxB : x ∈ Bad
      · exact Finset.mem_union_left _ hxB
      · refine Finset.mem_union_right _ ?_
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨hxB, mem_errSet.1 hx⟩
    exact le_trans (Finset.card_le_card hs) (Finset.card_union_le _ _)
  have hswap : ∑ ω ∈ Ω, #{x ∈ Finset.univ \ Bad | bad ω x}
      = ∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hpt : ∀ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ ≤ 2 ^ (k * ℓ) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
    refine card_bad_omega_le hq u b x (hgood x hx) _ ?_
    intro ω hω
    simp only [Finset.mem_filter] at hω
    exact hω.2
  have hsum : (∑ ω ∈ Ω, (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ)
      ≤ ∑ _ω ∈ Ω, (Bad.card * 2 ^ ℓ + 2 ^ n) := by
    have h1 : (∑ ω ∈ Ω, (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card
          * 2 ^ ℓ)
        ≤ ∑ ω ∈ Ω, (Bad.card * 2 ^ ℓ + #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ) := by
      refine Finset.sum_le_sum fun ω _ => ?_
      calc (errSet (orPoly q ω u) (fun x => decide (∃ i, b i x = true))).card * 2 ^ ℓ
          ≤ (Bad.card + #{x ∈ Finset.univ \ Bad | bad ω x}) * 2 ^ ℓ :=
            Nat.mul_le_mul_right _ (hsplit ω)
        _ = Bad.card * 2 ^ ℓ + #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ := by ring
    refine le_trans h1 ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    refine Nat.add_le_add_left ?_ _
    have h2 : ∑ ω ∈ Ω, #{x ∈ Finset.univ \ Bad | bad ω x} * 2 ^ ℓ
        = (∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hswap]
    rw [h2]
    calc (∑ x ∈ Finset.univ \ Bad, #{ω ∈ Ω | bad ω x} * 2 ^ ℓ)
        ≤ ∑ _x ∈ Finset.univ \ Bad, 2 ^ (k * ℓ) := Finset.sum_le_sum hpt
      _ ≤ ∑ _x ∈ (Finset.univ : Finset (Cube n)), 2 ^ (k * ℓ) :=
          Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
      _ = 2 ^ n * 2 ^ (k * ℓ) := by
          simp [Finset.sum_const, Fintype.card_fun]
      _ = ∑ _ω ∈ Ω, 2 ^ n := by rw [Finset.sum_const, hcardΩ, smul_eq_mul, mul_comm]
  have hne : Ω.Nonempty := ⟨fun _ _ => false, Finset.mem_univ _⟩
  obtain ⟨ω, -, hω⟩ := Finset.exists_le_of_sum_le hne hsum
  exact ⟨ω, hω⟩

/-- **The approximation lemma.**  Every circuit of depth `d` and size `s` over
`{¬, ∧, ∨, MOD q}` is approximated, over a field of characteristic `q`, by a function of
degree at most `(ℓ (q-1))^d` which errs on at most `s · 2^n / 2^ℓ` inputs. -/
theorem exists_approx (hq : q.Prime) [CharP F q] {ℓ : ℕ} (hl : 1 ≤ ℓ) (C : Circuit n) :
    ∃ g : Cube n → F, g ∈ Deg F n ((ℓ * (q - 1)) ^ C.depth) ∧
      (errSet g (C.eval q)).card * 2 ^ ℓ ≤ C.size * 2 ^ n := by
  classical
  have hq2 := hq.two_le
  have hbase : 1 ≤ ℓ * (q - 1) := by
    have h1 : 1 ≤ q - 1 := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ ℓ * (q - 1) := Nat.mul_le_mul hl h1
  induction C with
  | var i =>
    refine ⟨xmon F {i}, ?_, ?_⟩
    · simpa [Circuit.depth] using xmon_mem_Deg (F := F) (A := ({i} : Finset (Fin n))) (by simp)
    · have h0 : errSet (xmon F {i}) ((Circuit.var i).eval q) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        refine (mem_errSet.1 hx) ?_
        simp only [Circuit.eval, xmon, gmon, Finset.prod_singleton]
        cases h : x i <;> simp [h, boolF]
      rw [h0]
      simp [Circuit.size]
  | const c =>
    refine ⟨fun _ => boolF F c, ?_, ?_⟩
    · have hc : (fun _ : Cube n => boolF F c) = boolF F c • (1 : Cube n → F) := by
        funext x; simp
      rw [hc]
      exact Submodule.smul_mem _ _ (one_mem_Deg _)
    · have h0 : errSet (fun _ : Cube n => boolF F c) ((Circuit.const c).eval q) = ∅ :=
        Finset.eq_empty_of_forall_notMem fun x hx => (mem_errSet.1 hx) rfl
      rw [h0]
      simp [Circuit.size]
  | not C ih =>
    obtain ⟨g, hgD, hgerr⟩ := ih
    refine ⟨1 - g, ?_, ?_⟩
    · exact Submodule.sub_mem _ (Deg_mono (Nat.zero_le _) (one_mem_Deg 0)) hgD
    · have hset : errSet (1 - g) ((Circuit.not C).eval q) = errSet g (C.eval q) := by
        have hev : ((Circuit.not C).eval q) = fun x => !(C.eval q x) := rfl
        rw [hev, errSet_one_sub]
      rw [hset]
      exact le_trans hgerr (Nat.mul_le_mul_right _ (by simp [Circuit.size]))
  | gate gt k f ih =>
    choose g hgD hgerr using ih
    set d0 : ℕ := Finset.univ.sup fun i => (f i).depth with hd0
    set D0 : ℕ := (ℓ * (q - 1)) ^ d0 with hD0
    have hgD0 : ∀ i, g i ∈ Deg F n D0 := by
      intro i
      refine Deg_mono ?_ (hgD i)
      exact Nat.pow_le_pow_right hbase
        (Finset.le_sup (f := fun i => (f i).depth) (Finset.mem_univ i))
    set Bad : Finset (Cube n) := Finset.univ.biUnion fun i => errSet (g i) ((f i).eval q)
      with hBad
    have hgood : ∀ x, x ∉ Bad → ∀ i, g i x = boolF F ((f i).eval q x) := by
      intro x hx i
      by_contra hc
      exact hx (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, mem_errSet.2 hc⟩)
    have hBadcard : Bad.card * 2 ^ ℓ ≤ (∑ i, (f i).size) * 2 ^ n := by
      calc Bad.card * 2 ^ ℓ
          ≤ (∑ i, (errSet (g i) ((f i).eval q)).card) * 2 ^ ℓ :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ i, (errSet (g i) ((f i).eval q)).card * 2 ^ ℓ := by rw [Finset.sum_mul]
        _ ≤ ∑ i, (f i).size * 2 ^ n := Finset.sum_le_sum fun i _ => hgerr i
        _ = (∑ i, (f i).size) * 2 ^ n := by rw [Finset.sum_mul]
    have hdepth : (Circuit.gate gt k f).depth = d0 + 1 := by rw [Circuit.depth]
    have hsize : (Circuit.gate gt k f).size = (∑ i, (f i).size) + 1 := by rw [Circuit.size]
    have hDegTarget : (ℓ * (q - 1)) ^ (Circuit.gate gt k f).depth = ℓ * ((q - 1) * D0) := by
      rw [hdepth, hD0, pow_succ]
      ring
    cases gt with
    | and =>
      set u : Fin k → Cube n → F := fun i => 1 - g i with hu
      set b : Fin k → Cube n → Bool := fun i x => !((f i).eval q x) with hb
      have hu' : ∀ i, u i ∈ Deg F n D0 := fun i =>
        Submodule.sub_mem _ (Deg_mono (Nat.zero_le _) (one_mem_Deg 0)) (hgD0 i)
      have hgood' : ∀ x, x ∉ Bad → ∀ i, u i x = boolF F (b i x) := by
        intro x hx i
        simp only [hu, hb, Pi.sub_apply, Pi.one_apply, boolF_not, hgood x hx i]
      obtain ⟨ω, hω⟩ := exists_or_approx (ℓ := ℓ) hq u b Bad hgood'
      refine ⟨1 - orPoly q ω u, ?_, ?_⟩
      · rw [hDegTarget]
        exact Submodule.sub_mem _ (Deg_mono (Nat.zero_le _) (one_mem_Deg 0))
          (orPoly_mem_Deg ω u hu')
      · have hev : ((Circuit.gate GateType.and k f).eval q)
            = fun x => !(decide (∃ i, b i x = true)) := by
          funext x
          simp only [Circuit.eval, hb]
          by_cases h : ∀ i, (f i).eval q x = true
          · have hnex : ¬ ∃ i, (!((f i).eval q x)) = true := by
              push_neg
              intro i
              simp [h i]
            rw [decide_eq_true h, decide_eq_false hnex]
            rfl
          · obtain ⟨i, hi⟩ : ∃ i, ¬ (f i).eval q x = true := by
              by_contra hc
              push_neg at hc
              exact h hc
            have hex : ∃ i, (!((f i).eval q x)) = true := ⟨i, by simp [hi]⟩
            rw [decide_eq_false h, decide_eq_true hex]
            rfl
        rw [hev, errSet_one_sub]
        refine le_trans hω ?_
        rw [hsize, add_mul, one_mul]
        exact Nat.add_le_add_right hBadcard _
    | or =>
      obtain ⟨ω, hω⟩ := exists_or_approx (ℓ := ℓ) hq g (fun i x => (f i).eval q x) Bad hgood
      refine ⟨orPoly q ω g, ?_, ?_⟩
      · rw [hDegTarget]
        exact orPoly_mem_Deg ω g hgD0
      · have hev : ((Circuit.gate GateType.or k f).eval q)
            = fun x => decide (∃ i, (f i).eval q x = true) := rfl
        rw [hev]
        refine le_trans hω ?_
        rw [hsize, add_mul, one_mul]
        exact Nat.add_le_add_right hBadcard _
    | mod =>
      refine ⟨fun x => (∑ i, g i x) ^ (q - 1), ?_, ?_⟩
      · rw [hDegTarget]
        have hs : (fun x => ∑ i, g i x) ∈ Deg F n D0 := by
          have hrw : (fun x => ∑ i, g i x) = ∑ i : Fin k, g i := by funext x; simp
          rw [hrw]
          exact Deg_sum _ _ _ fun i _ => hgD0 i
        have hpow := Deg_pow (t := q - 1) hs
        rw [show ((fun x => ∑ i, g i x) : Cube n → F) ^ (q - 1)
            = (fun x => (∑ i, g i x) ^ (q - 1)) from by funext x; simp] at hpow
        exact Deg_mono (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by omega))) hpow
      · have hev : ((Circuit.gate GateType.mod k f).eval q)
            = fun x => decide (¬ q ∣ cnt fun i => (f i).eval q x) := rfl
        have herr : (errSet (fun x => (∑ i, g i x) ^ (q - 1))
            ((Circuit.gate GateType.mod k f).eval q)).card ≤ Bad.card := by
          refine card_errSet_le fun x hx => ?_
          have hval : (∑ i, g i x) = ((cnt fun i => (f i).eval q x : ℕ) : F) := by
            have := sel_sum_eq g (fun i x => (f i).eval q x) x (hgood x hx) (fun _ => true)
            simpa using this
          rw [hval, natCast_pow_sub_one hq, hev]
          by_cases h : q ∣ cnt fun i => (f i).eval q x <;> simp [h, boolF]
        calc (errSet (fun x => (∑ i, g i x) ^ (q - 1))
              ((Circuit.gate GateType.mod k f).eval q)).card * 2 ^ ℓ
            ≤ Bad.card * 2 ^ ℓ := Nat.mul_le_mul_right _ herr
          _ ≤ (∑ i, (f i).size) * 2 ^ n := hBadcard
          _ ≤ (Circuit.gate GateType.mod k f).size * 2 ^ n := by
              rw [hsize]
              exact Nat.mul_le_mul_right _ (by omega)

end CS

import Mathlib

/-!
# Elementary counting estimates

* a bound on the central binomial coefficient, `centralBinom k ^ 2 * (2 * k + 1) ≤ 16 ^ k`;
* a bound on partial sums of binomial coefficients;
* the fact that a polynomial is eventually dominated by `2 ^ j`.
-/

namespace CS

open Finset

/-- `2 ^ a ≥ a + 1`. -/
lemma succ_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self

/-- A linear function is eventually dominated by `2 ^ i`. -/
lemma linear_le_two_pow (C i : ℕ) (hi : C ^ 2 + C ≤ i) : C * (i + 1) ≤ 2 ^ i := by
  have hCi : C ≤ i := le_trans (Nat.le_add_left C (C ^ 2)) hi
  have h1 : 2 ^ i = 2 ^ C * 2 ^ (i - C) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : (C + 1) * (i - C + 1) ≤ 2 ^ C * 2 ^ (i - C) :=
    Nat.mul_le_mul (succ_le_two_pow C) (succ_le_two_pow (i - C))
  have h3 : C * (i + 1) ≤ (C + 1) * (i - C + 1) := by
    have : i - C + C = i := by omega
    nlinarith [this, hi, sq_nonneg C]
  omega

/-- A polynomial is eventually dominated by `2 ^ j`. -/
lemma poly_le_two_pow (M e : ℕ) :
    ∃ J : ℕ, ∀ j ≥ J, (M * (j + 1)) ^ e ≤ 2 ^ j := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨0, fun j _ => by simpa using Nat.one_le_two_pow⟩
  set C := M * e with hC
  refine ⟨e * (C ^ 2 + C + 1), fun j hj => ?_⟩
  set i := j / e with hi
  have hmod : e * i + j % e = j := by rw [hi]; exact Nat.div_add_mod j e
  have hlt : j % e < e := Nat.mod_lt j he
  have hei : e * i ≤ j := by omega
  have hiC : C ^ 2 + C ≤ i := by
    have h5 : C ^ 2 + C + 1 ≤ j / e := (Nat.le_div_iff_mul_le he).2 (by rw [mul_comm]; exact hj)
    omega
  have hje : j < e * (i + 1) := by
    have hexp : e * (i + 1) = e * i + e := by ring
    omega
  have h1 : M * (j + 1) ≤ C * (i + 1) := by
    have : j + 1 ≤ e * (i + 1) := hje
    calc M * (j + 1) ≤ M * (e * (i + 1)) := Nat.mul_le_mul_left _ this
      _ = C * (i + 1) := by rw [hC]; ring
  calc (M * (j + 1)) ^ e ≤ (C * (i + 1)) ^ e := Nat.pow_le_pow_left h1 e
    _ ≤ (2 ^ i) ^ e := Nat.pow_le_pow_left (linear_le_two_pow C i hiC) e
    _ = 2 ^ (i * e) := by rw [← pow_mul]
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hei)

/-- The central binomial coefficient satisfies `C(2k,k)^2 * (2k+1) ≤ 16^k`. -/
lemma centralBinom_sq_mul_le (k : ℕ) : (Nat.centralBinom k) ^ 2 * (2 * k + 1) ≤ 16 ^ k := by
  induction k with
  | zero => simp [Nat.centralBinom]
  | succ k ih =>
    have hrec := Nat.succ_mul_centralBinom_succ k
    have hpos : 0 < (k + 1) ^ 2 := by positivity
    have key : ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
        ≤ 16 ^ (k + 1) * (k + 1) ^ 2 := by
      have e1 : (Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2
          = (2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2 := by
        have : ((k + 1) * Nat.centralBinom (k + 1)) ^ 2
            = (2 * (2 * k + 1) * Nat.centralBinom k) ^ 2 := by rw [hrec]
        calc (Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2
            = ((k + 1) * Nat.centralBinom (k + 1)) ^ 2 := by ring
          _ = (2 * (2 * k + 1) * Nat.centralBinom k) ^ 2 := this
          _ = (2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2 := by ring
      have e2 : ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
          = (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2 := by
        calc ((Nat.centralBinom (k + 1)) ^ 2 * (2 * (k + 1) + 1)) * (k + 1) ^ 2
            = ((Nat.centralBinom (k + 1)) ^ 2 * (k + 1) ^ 2) * (2 * k + 3) := by ring
          _ = ((2 * (2 * k + 1)) ^ 2 * (Nat.centralBinom k) ^ 2) * (2 * k + 3) := by rw [e1]
          _ = (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2 := by ring
      rw [e2]
      have e3 : (2 * (2 * k + 1)) ^ 2 * (2 * k + 3) * (Nat.centralBinom k) ^ 2
          = (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.centralBinom k) ^ 2 * (2 * k + 1)) := by
        ring
      rw [e3]
      have e4 : (4 * (2 * k + 1) * (2 * k + 3)) * ((Nat.centralBinom k) ^ 2 * (2 * k + 1))
          ≤ (4 * (2 * k + 1) * (2 * k + 3)) * 16 ^ k := Nat.mul_le_mul_left _ ih
      refine le_trans e4 ?_
      have e5 : 4 * (2 * k + 1) * (2 * k + 3) ≤ 16 * (k + 1) ^ 2 := by nlinarith
      calc (4 * (2 * k + 1) * (2 * k + 3)) * 16 ^ k
          ≤ (16 * (k + 1) ^ 2) * 16 ^ k := Nat.mul_le_mul_right _ e5
        _ = 16 ^ (k + 1) * (k + 1) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right key hpos

/-- Half of the binomial coefficients of an odd row sum to `4 ^ m`. -/
lemma sum_range_choose_halfway' (m : ℕ) : ∑ i ∈ range (m + 1), (2 * m + 1).choose i = 4 ^ m :=
  Nat.sum_range_choose_halfway m

/-- Partial sums of an odd row of Pascal's triangle. -/
lemma sum_choose_le (m D : ℕ) :
    ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i ≤ 4 ^ m + D * (2 * m + 1).choose m := by
  have hsplit : ∑ i ∈ range (m + D + 1), (2 * m + 1).choose i
      = (∑ i ∈ range (m + 1), (2 * m + 1).choose i)
        + ∑ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i := by
    simp only [range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (by omega) (by omega)).symm
  rw [hsplit, sum_range_choose_halfway' m]
  have hb : ∀ i ∈ Ico (m + 1) (m + D + 1), (2 * m + 1).choose i ≤ (2 * m + 1).choose m := by
    intro i _
    have := Nat.choose_le_middle i (2 * m + 1)
    simpa [Nat.mul_div_cancel_left, show (2 * m + 1) / 2 = m by omega] using this
  refine Nat.add_le_add_left ?_ _
  have h2 := Finset.sum_le_card_nsmul (Ico (m + 1) (m + D + 1)) _ ((2 * m + 1).choose m) hb
  simp only [Nat.card_Ico, smul_eq_mul] at h2
  have hcard : m + D + 1 - (m + 1) = D := by omega
  rw [hcard] at h2
  exact h2

/-- `2 * C(2m+1, m) = centralBinom (m+1)`. -/
lemma two_mul_choose_eq_centralBinom (m : ℕ) :
    2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) := by
  have h : (2 * (m + 1)).choose (m + 1) = (2 * m + 1).choose m + (2 * m + 1).choose (m + 1) := by
    have h' : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h', Nat.choose_succ_succ]
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have := Nat.choose_symm (n := 2 * m + 1) (k := m + 1) (by omega)
    simpa [show 2 * m + 1 - (m + 1) = m by omega] using this.symm
  rw [Nat.centralBinom, h, hsymm]
  ring

end CS

import Mathlib
import RequestProject.RS.Circuits
import RequestProject.RS.Counting

/-!
# Low degree functions on the Boolean cube

We work with functions `Cube n → F` for a field `F`, and define `Deg F n k` to be the
`F`-subspace spanned by the multilinear monomials `∏ i ∈ A, x i` with `#A ≤ k`.

The main result of this file is `CS.card_le_of_approx`: Smolensky's dimension argument.
-/

namespace CS

open Finset

variable {F : Type*} [Field F] {n : ℕ}

/-- `boolF b` is `1` if `b` is true and `0` otherwise. -/
def boolF (F : Type*) [Field F] (b : Bool) : F := if b then 1 else 0

@[simp] lemma boolF_true : boolF F true = 1 := rfl
@[simp] lemma boolF_false : boolF F false = 0 := rfl

/-- A generalized monomial: the product over `A` of two-valued functions of a single
coordinate. -/
def gmon (F : Type*) [Field F] {n : ℕ} (a b : Fin n → F) (A : Finset (Fin n)) : Cube n → F :=
  fun x => ∏ i ∈ A, (if x i then b i else a i)

/-- The multilinear monomial `∏ i ∈ A, x i`. -/
def xmon (F : Type*) [Field F] {n : ℕ} (A : Finset (Fin n)) : Cube n → F :=
  gmon F (fun _ => 0) (fun _ => 1) A

/-- The monomial `∏ i ∈ A, y i` where `y i = z` if `x i` is true and `1` otherwise. -/
def ymon (F : Type*) [Field F] {n : ℕ} (z : F) (A : Finset (Fin n)) : Cube n → F :=
  gmon F (fun _ => 1) (fun _ => z) A

lemma gmon_empty (a b : Fin n → F) : gmon F a b ∅ = 1 := by
  funext x; simp [gmon]

lemma xmon_apply (A : Finset (Fin n)) (x : Cube n) :
    xmon F A x = if ∀ i ∈ A, x i = true then 1 else 0 := by
  classical
  simp only [xmon, gmon]
  induction A using Finset.induction with
  | empty => simp
  | insert j A hj ih =>
    rw [Finset.prod_insert hj, ih]
    by_cases hall : ∀ i ∈ A, x i = true
    · cases h : x j <;> simp [h, hall]
    · have : ¬ ∀ i ∈ insert j A, x i = true := fun hc => hall fun i hi => hc i (by simp [hi])
      cases h : x j <;> simp [h, hall, this]

lemma xmon_mul (A B : Finset (Fin n)) : xmon F A * xmon F B = xmon F (A ∪ B) := by
  funext x
  simp only [Pi.mul_apply, xmon_apply]
  by_cases hA : ∀ i ∈ A, x i = true <;> by_cases hB : ∀ i ∈ B, x i = true <;>
    simp_all [Finset.mem_union] <;> aesop

/-- The set of monomials of degree at most `k`. -/
def monSet (F : Type*) [Field F] (n k : ℕ) : Set (Cube n → F) :=
  {f | ∃ A : Finset (Fin n), A.card ≤ k ∧ f = xmon F A}

/-- The space of functions of degree at most `k` on the Boolean cube. -/
def Deg (F : Type*) [Field F] (n k : ℕ) : Submodule F (Cube n → F) :=
  Submodule.span F (monSet F n k)

lemma xmon_mem_Deg {A : Finset (Fin n)} {k : ℕ} (h : A.card ≤ k) : xmon F A ∈ Deg F n k :=
  Submodule.subset_span ⟨A, h, rfl⟩

lemma Deg_mono {k k' : ℕ} (h : k ≤ k') : Deg F n k ≤ Deg F n k' := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨A, hA, rfl⟩
  exact Submodule.subset_span ⟨A, hA.trans h, rfl⟩

lemma one_mem_Deg (k : ℕ) : (1 : Cube n → F) ∈ Deg F n k := by
  have : (1 : Cube n → F) = xmon F (∅ : Finset (Fin n)) := (gmon_empty _ _).symm
  rw [this]
  exact xmon_mem_Deg (by simp)

lemma Deg_mul {k₁ k₂ : ℕ} {f g : Cube n → F} (hf : f ∈ Deg F n k₁) (hg : g ∈ Deg F n k₂) :
    f * g ∈ Deg F n (k₁ + k₂) := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨A, hA, rfl⟩ := hu
    induction hg using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨B, hB, rfl⟩ := hv
      rw [xmon_mul]
      exact xmon_mem_Deg (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA hB))
    | zero => simp
    | add u v _ _ ihu ihv => rw [mul_add]; exact Submodule.add_mem _ ihu ihv
    | smul c v _ ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add u v _ _ ihu ihv => rw [add_mul]; exact Submodule.add_mem _ ihu ihv
  | smul c v _ ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ih

lemma Deg_pow {k t : ℕ} {f : Cube n → F} (hf : f ∈ Deg F n k) : f ^ t ∈ Deg F n (t * k) := by
  induction t with
  | zero => simpa using one_mem_Deg 0
  | succ t ih =>
    have : f ^ (t + 1) = f ^ t * f := by ring
    rw [this]
    have := Deg_mul ih hf
    exact Deg_mono (by ring_nf; omega) this

lemma Deg_prod {ι : Type*} (s : Finset ι) (f : ι → Cube n → F) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg F n (k i)) : (∏ i ∈ s, f i) ∈ Deg F n (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg 0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact Deg_mul (hf j (by simp)) (ih fun i hi => hf i (by simp [hi]))

lemma Deg_sum {ι : Type*} (s : Finset ι) (f : ι → Cube n → F) (k : ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg F n k) : (∑ i ∈ s, f i) ∈ Deg F n k :=
  Submodule.sum_mem _ hf

/-- **Key spanning lemma**: a product of arbitrary single-coordinate functions over `A`
lies in the span of the `gmon a b B` with `B ⊆ A`, provided `a i ≠ b i` for all `i`. -/
lemma gmon_mem_span_gmon (a b : Fin n → F) (hab : ∀ i, a i ≠ b i) (a' b' : Fin n → F)
    (A : Finset (Fin n)) :
    gmon F a' b' A ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ A, f = gmon F a b B} := by
  classical
  induction A using Finset.induction with
  | empty =>
    have h0 : gmon F a' b' ∅ = gmon F a b ∅ := by rw [gmon_empty, gmon_empty]
    rw [h0]
    exact Submodule.subset_span ⟨∅, by simp, rfl⟩
  | insert j A hj ih =>
    set w : Cube n → F := fun x => if x j then b' j else a' j with hwdef
    have hne : b j - a j ≠ 0 := sub_ne_zero.2 (hab j).symm
    obtain ⟨β, hbeta⟩ : ∃ β : F, β * (b j - a j) = b' j - a' j :=
      ⟨(b' j - a' j) / (b j - a j), div_mul_cancel₀ _ hne⟩
    have hw : ∀ x : Cube n, w x = (a' j - β * a j) + β * (if x j then b j else a j) := by
      intro x
      cases h : x j
      · simp only [hwdef, h, Bool.false_eq_true, if_false]
        ring
      · simp only [hwdef, h, if_true]
        linear_combination -hbeta
    have hfac : gmon F a' b' (insert j A) = w * gmon F a' b' A := by
      funext x
      simp [gmon, Finset.prod_insert hj, hwdef]
    have main : ∀ g ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ A, f = gmon F a b B},
        w * g ∈ Submodule.span F {f : Cube n → F | ∃ B ⊆ insert j A, f = gmon F a b B} := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨B, hBA, rfl⟩ := hf
        have hjB : j ∉ B := fun h => hj (hBA h)
        have hsplit : w * gmon F a b B
            = (a' j - β * a j) • gmon F a b B + β • gmon F a b (insert j B) := by
          funext x
          simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, gmon,
            Finset.prod_insert hjB, hw x]
          ring
        rw [hsplit]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨B, hBA.trans (Finset.subset_insert _ _), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨insert j B, Finset.insert_subset_insert _ hBA, rfl⟩))
      | zero => simp
      | add u v _ _ ihu ihv => rw [mul_add]; exact Submodule.add_mem _ ihu ihv
      | smul c v _ ih' => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ ih'
    rw [hfac]
    exact main _ ih

/-- Any product of single-coordinate functions over `A` has degree at most `#A`. -/
lemma gmon_mem_Deg (a' b' : Fin n → F) (A : Finset (Fin n)) :
    gmon F a' b' A ∈ Deg F n A.card := by
  have h := gmon_mem_span_gmon (F := F) (fun _ => (0 : F)) (fun _ => 1)
    (fun i => by norm_num) a' b' A
  refine Submodule.span_le.2 ?_ h
  rintro f ⟨B, hBA, rfl⟩
  exact xmon_mem_Deg (Finset.card_le_card hBA)

lemma ymon_mem_Deg (z : F) (A : Finset (Fin n)) : ymon F z A ∈ Deg F n A.card :=
  gmon_mem_Deg _ _ A

/-- The indicator function of a point of the cube. -/
lemma indicator_eq_gmon (x₀ : Cube n) :
    (fun x : Cube n => if x = x₀ then (1 : F) else 0)
      = gmon F (fun i => if x₀ i then 0 else 1) (fun i => if x₀ i then 1 else 0) univ := by
  funext x
  simp only [gmon]
  rw [show (∏ i : Fin n, (if x i then (if x₀ i then (1 : F) else 0)
      else (if x₀ i then 0 else 1)))
      = ∏ i : Fin n, (if x i = x₀ i then (1 : F) else 0) from
    Finset.prod_congr rfl fun i _ => by cases h : x i <;> cases h₀ : x₀ i <;> simp [h, h₀]]
  rw [Finset.prod_boole]
  by_cases h : x = x₀
  · subst h; simp
  · have hnot : ¬ ∀ i ∈ univ, x i = x₀ i := fun hc => h (funext fun i => hc i (mem_univ i))
    rw [if_neg h, if_neg hnot]

/-- Every function on the cube is a combination of the `ymon`'s. -/
lemma mem_span_ymon (z : F) (hz : z ≠ 1) (f : Cube n → F) :
    f ∈ Submodule.span F {g : Cube n → F | ∃ A : Finset (Fin n), g = ymon F z A} := by
  classical
  have hdecomp : f = ∑ x₀ : Cube n, f x₀ • (fun x : Cube n => if x = x₀ then (1 : F) else 0) := by
    funext x
    rw [Finset.sum_apply]
    simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun x₀ _ => Submodule.smul_mem _ _ ?_
  rw [indicator_eq_gmon]
  have h := gmon_mem_span_gmon (F := F) (fun _ => (1 : F)) (fun _ => z)
    (fun i => fun hc => hz hc.symm) (fun i => if x₀ i then 0 else 1)
    (fun i => if x₀ i then 1 else 0) univ
  refine Submodule.span_le.2 ?_ h
  rintro g ⟨B, -, rfl⟩
  exact Submodule.subset_span ⟨B, rfl⟩

section Finrank

variable (F n)

/-- The number of monomials of degree at most `k`. -/
lemma card_monomials_le (k : ℕ) :
    #{A : Finset (Fin n) | A.card ≤ k} ≤ ∑ i ∈ range (k + 1), n.choose i := by
  classical
  have hsub : ({A : Finset (Fin n) | A.card ≤ k} : Finset (Finset (Fin n)))
      ⊆ (range (k + 1)).biUnion fun i => Finset.powersetCard i (univ : Finset (Fin n)) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨A.card, by omega, Finset.subset_univ _, rfl⟩
  refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.card_powersetCard, Finset.card_fin]

lemma finrank_Deg_le (k : ℕ) :
    Module.finrank F (Deg F n k) ≤ ∑ i ∈ range (k + 1), n.choose i := by
  classical
  set s : Finset (Cube n → F) :=
    ({A : Finset (Fin n) | A.card ≤ k} : Finset (Finset (Fin n))).image (xmon F) with hs
  have hset : monSet F n k = (s : Set (Cube n → F)) := by
    ext f
    simp only [monSet, Set.mem_setOf_eq, hs, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩
  have h1 : Module.finrank F (Deg F n k) ≤ s.card := by
    rw [Deg, hset]
    exact finrank_span_finset_le_card s
  refine le_trans h1 (le_trans (Finset.card_image_le) (card_monomials_le n k))

end Finrank

/-- **Smolensky's dimension argument.**
If a function of degree at most `D` agrees with `∏ i, y i` on a set `S`, where
`y i = z` if `x i` and `1` otherwise (with `z ≠ 0, 1`), then `S` has at most
`∑_{i ≤ m + D} C(n,i)` elements, where `n = 2m+1`. -/
theorem card_le_of_approx {m D : ℕ} (hn : n = 2 * m + 1) (z : F) (hz1 : z ≠ 1) (hz0 : z ≠ 0)
    (S : Finset (Cube n)) (P : Cube n → F) (hP : P ∈ Deg F n D)
    (hS : ∀ x ∈ S, P x = ymon F z Finset.univ x) :
    S.card ≤ ∑ i ∈ range (m + D + 1), n.choose i := by
  classical
  set T : (Cube n → F) →ₗ[F] (S → F) := LinearMap.funLeft F F (fun s : S => (s : Cube n)) with hT
  -- every restriction to `S` comes from a function of degree at most `m + D`
  have hkey : ∀ f : Cube n → F, T f ∈ Submodule.map T (Deg F n (m + D)) := by
    intro f
    have hspan : Submodule.span F {g : Cube n → F | ∃ A : Finset (Fin n), g = ymon F z A}
        ≤ Submodule.comap T (Submodule.map T (Deg F n (m + D))) := by
      refine Submodule.span_le.2 ?_
      rintro g ⟨A, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      by_cases hA : A.card ≤ m
      · exact Submodule.mem_map_of_mem (Deg_mono (by omega) (ymon_mem_Deg z A))
      · push_neg at hA
        have hcompl : (Aᶜ : Finset (Fin n)).card ≤ m := by
          have := Finset.card_compl A
          simp only [Fintype.card_fin] at this
          omega
        refine ⟨P * ymon F z⁻¹ Aᶜ, ?_, ?_⟩
        · exact Deg_mono (by omega) (Deg_mul hP (ymon_mem_Deg z⁻¹ Aᶜ))
        · funext s
          obtain ⟨x, hx⟩ := s
          simp only [hT, LinearMap.funLeft_apply, Pi.mul_apply]
          rw [hS x hx]
          have hsplit : ymon F z (univ : Finset (Fin n)) x = ymon F z A x * ymon F z Aᶜ x := by
            simp only [ymon, gmon]
            rw [← Finset.prod_union (disjoint_compl_right), Finset.union_compl]
          rw [hsplit, mul_assoc]
          have hinv : ymon F z Aᶜ x * ymon F z⁻¹ Aᶜ x = 1 := by
            simp only [ymon, gmon, ← Finset.prod_mul_distrib]
            refine Finset.prod_eq_one fun i _ => ?_
            cases h : x i <;> simp [h, hz0]
          rw [hinv, mul_one]
    exact hspan (mem_span_ymon z hz1 f)
  have hmap : Submodule.map T (Deg F n (m + D)) = ⊤ := by
    rw [eq_top_iff]
    rintro φ -
    have : T (fun x => if h : x ∈ S then φ ⟨x, h⟩ else 0) = φ := by
      funext s
      obtain ⟨x, hx⟩ := s
      simp [hT, hx]
    rw [← this]
    exact hkey _
  have h1 : Module.finrank F (S → F) ≤ Module.finrank F (Deg F n (m + D)) := by
    have h2 : Module.finrank F ((⊤ : Submodule F (S → F))) ≤
        Module.finrank F (Deg F n (m + D)) := by
      rw [← hmap]
      exact Submodule.finrank_map_le T _
    simpa using h2
  have h3 : Module.finrank F (S → F) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [h3] at h1
  exact le_trans h1 (finrank_Deg_le F n (m + D))

end CS

import Mathlib

/-!
# Circuits over the basis `{¬, ∧, ∨, MOD q}`

Unbounded fan-in Boolean circuits with `AND`, `OR`, `NOT` and `MOD q` gates,
i.e. the circuits underlying the class `AC⁰[q]`.
-/

namespace CS

open Finset

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- The number of `true` coordinates of a Boolean vector. -/
def cnt {k : ℕ} (b : Fin k → Bool) : ℕ := #{i | b i = true}

/-- The unbounded fan-in gate types: `AND`, `OR` and `MOD q`. -/
inductive GateType
  | and
  | or
  | mod
  deriving DecidableEq

/-- Boolean circuits with `n` inputs over the basis `{¬, ∧, ∨, MOD q}`,
with unbounded fan-in `∧`, `∨` and `MOD q` gates. -/
inductive Circuit (n : ℕ) : Type
  | var : Fin n → Circuit n
  | const : Bool → Circuit n
  | not : Circuit n → Circuit n
  | gate : GateType → (k : ℕ) → (Fin k → Circuit n) → Circuit n

namespace Circuit

variable {n m : ℕ}

/-- The number of gates of a circuit (negations included). -/
def size : Circuit n → ℕ
  | var _ => 1
  | const _ => 1
  | not c => c.size + 1
  | gate _ _ f => (∑ i, (f i).size) + 1

/-- The depth of a circuit: the maximal number of `∧`/`∨`/`MOD` gates on a path from the
output to an input.  Negations are free (they can be pushed to the inputs). -/
def depth : Circuit n → ℕ
  | var _ => 0
  | const _ => 0
  | not c => c.depth
  | gate _ _ f => (Finset.univ.sup fun i => (f i).depth) + 1

/-- Evaluation of a circuit, where `MOD q` gates output `true` iff the number of `true`
inputs is *not* divisible by `q`. -/
def eval (q : ℕ) : Circuit n → Cube n → Bool
  | var i, x => x i
  | const b, _ => b
  | not c, x => !(eval q c x)
  | gate g _ f, x =>
    match g with
    | .and => decide (∀ i, eval q (f i) x = true)
    | .or => decide (∃ i, eval q (f i) x = true)
    | .mod => decide (¬ q ∣ cnt fun i => eval q (f i) x)

/-- Substitution of inputs: each input of the circuit is replaced either by an input
of the new circuit or by a constant. -/
def subst (σ : Fin n → Fin m ⊕ Bool) : Circuit n → Circuit m
  | var i => match σ i with
    | .inl j => var j
    | .inr b => const b
  | const b => const b
  | not c => not (subst σ c)
  | gate g k f => gate g k fun i => subst σ (f i)

/-- The input to the original circuit induced by a substitution. -/
def substInput (σ : Fin n → Fin m ⊕ Bool) (x : Cube m) : Cube n := fun i =>
  match σ i with
  | .inl j => x j
  | .inr b => b

@[simp] lemma eval_subst (q : ℕ) (σ : Fin n → Fin m ⊕ Bool) (C : Circuit n) (x : Cube m) :
    eval q (subst σ C) x = eval q C (substInput σ x) := by
  induction C with
  | var i =>
    simp only [subst]
    cases h : σ i with
    | inl j => simp [substInput, h, eval]
    | inr b => simp [substInput, h, eval]
  | const b => simp [subst, eval]
  | not c ih => simp [subst, eval, ih]
  | gate g k f ih =>
    cases g <;> simp [subst, eval, ih]

@[simp] lemma size_subst (σ : Fin n → Fin m ⊕ Bool) (C : Circuit n) :
    (subst σ C).size = C.size := by
  induction C with
  | var i =>
    simp only [subst]
    cases h : σ i with
    | inl j => simp [size]
    | inr b => simp [size]
  | const b => simp [subst, size]
  | not c ih => simp [subst, size, ih]
  | gate g k f ih => simp [subst, size, ih]

@[simp] lemma depth_subst (σ : Fin n → Fin m ⊕ Bool) (C : Circuit n) :
    (subst σ C).depth = C.depth := by
  induction C with
  | var i =>
    simp only [subst]
    cases h : σ i with
    | inl j => simp [depth]
    | inr b => simp [depth]
  | const b => simp [subst, depth]
  | not c ih => simp [subst, depth, ih]
  | gate g k f ih => simp [subst, depth, ih]

end Circuit

/-- The `MOD p` function: `true` iff the number of ones is *not* divisible by `p`. -/
def modFn (p n : ℕ) (x : Cube n) : Bool := decide (¬ p ∣ cnt x)

end CS


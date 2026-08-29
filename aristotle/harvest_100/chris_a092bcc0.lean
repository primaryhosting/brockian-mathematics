/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace QI

/-- The `n`-bit state space, an `n`-dimensional vector space over `ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟪y, x⟫ = ∑ i, y i * x i`. -/
def ip {n : ℕ} (y x : Vec n) : ZMod 2 := ∑ i, y i * x i

/-- The character `(-1) ^ a` of `ZMod 2`, valued in `ℤ`. -/
def chi (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

/-- `f` is a Simon function with hidden shift `s`: it is `s`-periodic, and `f x = f y`
only if `y = x` or `y = x + s`. -/
def SimonFn {n : ℕ} (s : Vec n) (f : Vec n → Vec n) : Prop :=
  (∀ x, f (x + s) = f x) ∧ (∀ x y, f x = f y → y = x ∨ y = x + s)

/-- Deterministic classical query algorithms: decision trees of depth at most `d` that
query an oracle `Vec n → Vec n` (adaptively) and finally output an element of `Vec n`. -/
inductive DTree (n : ℕ) : ℕ → Type
  | leaf {d : ℕ} (out : Vec n) : DTree n d
  | node {d : ℕ} (x : Vec n) (k : Vec n → DTree n d) : DTree n (d + 1)

/-- The output of the decision tree on oracle `f`. -/
def DTree.run {n : ℕ} : {d : ℕ} → DTree n d → (Vec n → Vec n) → Vec n
  | _, .leaf o, _ => o
  | _, .node x k, f => (k (f x)).run f

/-- The set of points the decision tree queries when run on oracle `f`. -/
def DTree.queries {n : ℕ} : {d : ℕ} → DTree n d → (Vec n → Vec n) → Finset (Vec n)
  | _, .leaf _, _ => ∅
  | _, .node x k, f => insert x ((k (f x)).queries f)

/-! ## Basic arithmetic in `Vec n` -/

lemma vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  funext i
  simpa using (by decide : ∀ a : ZMod 2, a + a = 0) (v i)

lemma ip_add {n : ℕ} (y x s : Vec n) : ip y (x + s) = ip y x + ip y s := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma chi_add_one (a : ZMod 2) : chi (a + 1) = -chi a := by revert a; decide

/-! ## Basic facts about decision trees -/

lemma DTree.card_queries_le {n : ℕ} :
    ∀ {d : ℕ} (T : DTree n d) (f : Vec n → Vec n), (T.queries f).card ≤ d := by
  intro d T
  induction T with
  | leaf o => intro f; simp [DTree.queries]
  | node x k ih =>
      intro f
      refine le_trans (Finset.card_insert_le _ _) ?_
      have := ih (f x) f
      omega

/-- A decision tree cannot distinguish two oracles that agree on the points it queries. -/
lemma DTree.run_congr {n : ℕ} :
    ∀ {d : ℕ} (T : DTree n d) (f h : Vec n → Vec n),
      (∀ x ∈ T.queries h, f x = h x) → T.run f = T.run h := by
  intro d T
  induction T with
  | leaf o => intro f h _; rfl
  | node x k ih =>
      intro f h hagree
      have hx : f x = h x := hagree x (by simp [DTree.queries])
      have hrest : ∀ y ∈ (k (h x)).queries h, f y = h y := by
        intro y hy
        exact hagree y (by simp [DTree.queries, hy])
      calc (DTree.node x k).run f = (k (f x)).run f := rfl
        _ = (k (h x)).run f := by rw [hx]
        _ = (k (h x)).run h := ih (h x) f h hrest
        _ = (DTree.node x k).run h := rfl

/-! ## Quantum side: interference kills every `y` with `⟪y, s⟫ ≠ 0` -/

/-- **Simon's interference lemma.**  For an `s`-periodic oracle `f`, the amplitude of the
measurement outcome `y` after the Hadamard–oracle–Hadamard step is proportional to
`∑_{x : f x = z} (-1) ^ ⟪y, x⟫`, and this sum vanishes whenever `⟪y, s⟫ ≠ 0`.
Hence every observed outcome `y` satisfies `⟪y, s⟫ = 0`. -/
theorem simon_interference {n : ℕ} (s y : Vec n) (f : Vec n → Vec n)
    (hf : ∀ x, f (x + s) = f x) (hy : ip y s ≠ 0) (z : Vec n) :
    ∑ x ∈ Finset.univ.filter (fun x => f x = z), chi (ip y x) = 0 := by
  have hys : ip y s = 1 := by revert hy; generalize ip y s = a; revert a; decide
  have hss : ∀ x : Vec n, x + s + s = x := by
    intro x; rw [add_assoc, vec_add_self, add_zero]
  set A := Finset.univ.filter (fun x => f x = z) with hA
  have hmemA : ∀ x, x ∈ A → x + s ∈ A := by
    intro x hx
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hf x]; exact hx
  have key : ∑ x ∈ A, chi (ip y x) = ∑ x ∈ A, -chi (ip y x) := by
    refine Finset.sum_nbij' (i := fun x => x + s) (j := fun x => x + s) ?_ ?_ ?_ ?_ ?_
    · intro a ha; exact hmemA a ha
    · intro b hb; exact hmemA b hb
    · intro a _; exact hss a
    · intro b _; exact hss b
    · intro a _
      rw [ip_add, hys, chi_add_one, neg_neg]
  rw [Finset.sum_neg_distrib] at key
  linarith

/-! ## Quantum side: `n` measurement outcomes determine the hidden shift -/

lemma ip_Y {n : ℕ} (s t : Vec n) (i k : Fin n) :
    ip (fun j => (if j = i then (1 : ZMod 2) else 0) + s i * (if j = k then 1 else 0)) t
      = t i + s i * t k := by
  simp [ip, add_mul, Finset.sum_add_distrib]

/-- **Recovery from `O(n)` samples.**  For every nonzero shift `s` there are `n` vectors
`Y i`, all orthogonal to `s`, such that `s` is the *unique* nonzero vector orthogonal to
all of them.  Thus `n` outcomes of Simon's quantum subroutine suffice to pin down `s`. -/
theorem simon_recovery {n : ℕ} (s : Vec n) (hs : s ≠ 0) :
    ∃ Y : Fin n → Vec n, (∀ i, ip (Y i) s = 0) ∧
      ∀ t : Vec n, t ≠ 0 → (∀ i, ip (Y i) t = 0) → t = s := by
  obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hs (funext hcon)
  have hk1 : s k = 1 := by revert hk; generalize s k = a; revert a; decide
  refine ⟨fun i => (fun j => (if j = i then 1 else 0) + s i * (if j = k then 1 else 0)), ?_, ?_⟩
  · intro i
    rw [ip_Y, hk1, mul_one]
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (s i)
  · intro t ht h
    have h' : ∀ i, t i = s i * t k := by
      intro i
      have hi := h i
      rw [ip_Y] at hi
      have := congrArg (fun z => z + s i * t k) hi
      simpa [add_assoc, (by decide : ∀ a : ZMod 2, a + a = 0)] using this
    have htk : t k = 1 := by
      by_contra hc
      refine ht (funext fun i => ?_)
      have h0 : t k = 0 := by revert hc; generalize t k = a; revert a; decide
      simp [h' i, h0]
    funext i
    simp [h' i, htk]

/-! ## Classical side: `Ω(2 ^ (n / 2))` queries are necessary -/

/-- A canonical two-to-one map with period `s`: it picks, out of `{x, x + s}`, the element
that comes first in some fixed enumeration of `Vec n`. -/
noncomputable def pick {n : ℕ} (s x : Vec n) : Vec n :=
  if (Fintype.equivFin (Vec n)) x ≤ (Fintype.equivFin (Vec n)) (x + s) then x else x + s

lemma pick_eq_or {n : ℕ} (s x : Vec n) : pick s x = x ∨ pick s x = x + s := by
  unfold pick; split
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma pick_add {n : ℕ} (s x : Vec n) (hs : s ≠ 0) : pick s (x + s) = pick s x := by
  have hxs : x + s + s = x := by rw [add_assoc, vec_add_self, add_zero]
  have hne : x + s ≠ x := fun hcon => hs (by simpa using hcon)
  have hE : (Fintype.equivFin (Vec n)) x ≠ (Fintype.equivFin (Vec n)) (x + s) := fun hcon =>
    hne ((Fintype.equivFin (Vec n)).injective hcon).symm
  rcases lt_or_gt_of_ne hE with h | h
  · rw [pick, pick, hxs, if_pos h.le, if_neg (not_le.mpr h)]
  · rw [pick, pick, hxs, if_neg (not_le.mpr h), if_pos h.le]

lemma pick_fiber {n : ℕ} (s x y : Vec n) (h : pick s x = pick s y) : y = x ∨ y = x + s := by
  have hss : ∀ v : Vec n, v + s + s = v := by
    intro v; rw [add_assoc, vec_add_self, add_zero]
  rcases pick_eq_or s x with hx | hx <;> rcases pick_eq_or s y with hy | hy <;>
    rw [hx, hy] at h
  · exact Or.inl h.symm
  · right
    have := congrArg (fun v => v + s) h
    simpa [hss] using this.symm
  · exact Or.inr h.symm
  · exact Or.inl (add_right_cancel h).symm

/-- **Classical lower bound.**  A deterministic classical decision tree of depth `d` that
outputs the hidden shift of every Simon function must satisfy `2 ^ n ≤ d ^ 2 + 2`.

The argument is the standard adversary/birthday argument: run the tree on the injective
oracle `id`; if the tree is shallow, some nonzero shift `s` is neither the produced answer
nor a difference of two queried points, and then an actual Simon function with shift `s`
can be built which agrees with `id` on all queried points, fooling the tree. -/
theorem classical_lower_bound {n d : ℕ} (T : DTree n d)
    (hT : ∀ s : Vec n, s ≠ 0 → ∀ f, SimonFn s f → T.run f = s) :
    2 ^ n ≤ d ^ 2 + 2 := by
  by_contra hcon
  push_neg at hcon
  set Q := T.queries id with hQdef
  set out := T.run id with houtdef
  have hQcard : Q.card ≤ d := T.card_queries_le id
  set B : Finset (Vec n) := ((Q ×ˢ Q).image (fun p => p.1 + p.2)) ∪ {out, 0} with hBdef
  have hcard : Fintype.card (Vec n) = 2 ^ n := by simp
  have h1 : ((Q ×ˢ Q).image (fun p => p.1 + p.2)).card ≤ d ^ 2 := by
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, pow_two]
    exact Nat.mul_le_mul hQcard hQcard
  have h2 : B.card ≤ d ^ 2 + 2 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have hpair : ({out, 0} : Finset (Vec n)).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  obtain ⟨s, hs⟩ : ∃ s : Vec n, s ∉ B := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (Vec n)) ⊆ B := fun x _ => h x
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcard] at this
    omega
  have hs0 : s ≠ 0 := fun h => hs (by simp [hBdef, h])
  have hsout : s ≠ out := fun h => hs (by simp [hBdef, h])
  have hsdiff : ∀ x ∈ Q, ∀ y ∈ Q, x + y ≠ s := by
    intro x hx y hy hxy
    refine hs ?_
    simp only [hBdef, Finset.mem_union, Finset.mem_image, Finset.mem_product]
    exact Or.inl ⟨(x, y), ⟨hx, hy⟩, hxy⟩
  -- `pick s` is injective on the queried set, so it can be corrected by a permutation
  have hginj : ∀ x ∈ Q, ∀ y ∈ Q, pick s x = pick s y → x = y := by
    intro x hx y hy h
    rcases pick_fiber s x y h with h1 | h1
    · exact h1.symm
    · exact absurd (by rw [h1, ← add_assoc, vec_add_self, zero_add]) (hsdiff x hx y hy)
  set A : Finset (Vec n) := Q.image (pick s) with hAdef
  let F : {x // x ∈ Q} → {y // y ∈ A} := fun x => ⟨pick s x.1, Finset.mem_image_of_mem _ x.2⟩
  have hFbij : Function.Bijective F := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      exact Subtype.ext (hginj x hx y hy (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, hgx⟩ := Finset.mem_image.mp hy
      exact ⟨⟨x, hx⟩, Subtype.ext hgx⟩
  let e : {x // x ∈ Q} ≃ {y // y ∈ A} := Equiv.ofBijective F hFbij
  let perm : Equiv.Perm (Vec n) := (e.symm).extendSubtype
  have hperm : ∀ x ∈ Q, perm (pick s x) = x := by
    intro x hx
    have hmem : pick s x ∈ A := Finset.mem_image_of_mem _ hx
    have hap := Equiv.extendSubtype_apply_of_mem e.symm (pick s x) hmem
    have he : e ⟨x, hx⟩ = ⟨pick s x, hmem⟩ := rfl
    show (e.symm).extendSubtype (pick s x) = x
    rw [hap, ← he, Equiv.symm_apply_apply]
  set f : Vec n → Vec n := fun x => perm (pick s x) with hfdef
  have hSimon : SimonFn s f := by
    constructor
    · intro x
      show perm (pick s (x + s)) = perm (pick s x)
      rw [pick_add s x hs0]
    · intro x y hxy
      exact pick_fiber s x y (perm.injective hxy)
  have hrun : T.run f = T.run id := T.run_congr f id fun x hx => hperm x hx
  have hfin := hT s hs0 f hSimon
  rw [hrun] at hfin
  exact hsout hfin.symm

lemma sqrt_bound {n d : ℕ} (h : 2 ^ n ≤ d ^ 2 + 2) : 2 ^ (n / 2) ≤ d + 2 := by
  by_contra hc
  push_neg at hc
  have h1 : (2 : ℕ) ^ (n / 2) * 2 ^ (n / 2) ≤ 2 ^ n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (d + 2) * (d + 2) < 2 ^ (n / 2) * 2 ^ (n / 2) := Nat.mul_lt_mul_of_lt_of_lt hc hc
  nlinarith [h, h1, h2]

/-- **Simon's problem.**

1. *(Quantum, interference)* For an `s`-periodic oracle every measurement outcome `y` of the
   Hadamard–oracle–Hadamard subroutine satisfies `⟪y, s⟫ = 0`: the signed sum giving the
   amplitude of any `y` with `⟪y, s⟫ ≠ 0` cancels exactly.
2. *(Quantum, `O(n)` queries suffice)* For every nonzero `s` there are `n` such outcomes that
   determine `s` uniquely among nonzero vectors.
3. *(Classical, `Ω(2 ^ (n / 2))` queries needed)* Every deterministic classical decision tree
   of depth `d` that solves Simon's problem obeys `2 ^ n ≤ d ^ 2 + 2`, and hence
   `2 ^ (n / 2) ≤ d + 2`.
-/
theorem simon_algorithm :
    (∀ (n : ℕ) (s y : Vec n) (f : Vec n → Vec n), (∀ x, f (x + s) = f x) → ip y s ≠ 0 →
        ∀ z : Vec n, ∑ x ∈ Finset.univ.filter (fun x => f x = z), chi (ip y x) = 0) ∧
    (∀ (n : ℕ) (s : Vec n), s ≠ 0 →
        ∃ Y : Fin n → Vec n, (∀ i, ip (Y i) s = 0) ∧
          ∀ t : Vec n, t ≠ 0 → (∀ i, ip (Y i) t = 0) → t = s) ∧
    (∀ (n d : ℕ) (T : DTree n d),
        (∀ s : Vec n, s ≠ 0 → ∀ f, SimonFn s f → T.run f = s) →
        2 ^ n ≤ d ^ 2 + 2 ∧ 2 ^ (n / 2) ≤ d + 2) := by
  refine ⟨fun n s y f hf hy z => simon_interference s y f hf hy z,
    fun n s hs => simon_recovery s hs, fun n d T hT => ?_⟩
  have h := classical_lower_bound T hT
  exact ⟨h, sqrt_bound h⟩

end QI

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


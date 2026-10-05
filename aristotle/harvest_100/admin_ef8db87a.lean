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

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/
def reachB : ℕ → ℕ → Bool
  | 0, v => v == s
  | i + 1, v =>
      decide (v < n) && (List.range n).any (fun u => reachB i u && ((u == v) || g u v))

variable {n g s}

@[simp] lemma reachB_zero (v : ℕ) : reachB n g s 0 v = (v == s) := rfl

lemma reachB_succ_iff (i v : ℕ) :
    reachB n g s (i + 1) v = true ↔
      v < n ∧ ∃ u, u < n ∧ reachB n g s i u = true ∧ (u = v ∨ g u v = true) := by
  constructor
  · intro h
    rw [reachB] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨hv, u, hu, h1, h2⟩ := h
    exact ⟨hv, u, hu, h1, h2⟩
  · rintro ⟨hv, u, hu, h1, h2⟩
    rw [reachB]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, Bool.or_eq_true]
    exact ⟨hv, u, hu, h1, h2⟩

lemma reachB_lt (hs : s < n) {i v : ℕ} (h : reachB n g s i v = true) : v < n := by
  cases i with
  | zero => simp only [reachB_zero, beq_iff_eq] at h; omega
  | succ i => exact ((reachB_succ_iff i v).1 h).1

lemma reachB_mono (hs : s < n) {i v : ℕ} (h : reachB n g s i v = true) :
    reachB n g s (i + 1) v = true := by
  have hv : v < n := reachB_lt hs h
  exact (reachB_succ_iff i v).2 ⟨hv, v, hv, h, Or.inl rfl⟩

lemma reachB_mono_le (hs : s < n) {i j v : ℕ} (hij : i ≤ j) (h : reachB n g s i v = true) :
    reachB n g s j v = true := by
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact h
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · exact reachB_mono hs (ih (by omega))
      · have : i = j + 1 := by omega
        subst this; exact h

/-- The set of vertices reachable in at most `i` steps. -/
def Rset (i : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun v => reachB n g s i v = true)

lemma mem_Rset {i v : ℕ} : v ∈ Rset (n := n) (g := g) (s := s) i ↔ v < n ∧ reachB n g s i v = true := by
  simp [Rset]

/-- The number of vertices reachable in at most `i` steps. -/
def cnt (i : ℕ) : ℕ := (Rset (n := n) (g := g) (s := s) i).card

lemma Rset_subset_succ (hs : s < n) (i : ℕ) :
    Rset (n := n) (g := g) (s := s) i ⊆ Rset (n := n) (g := g) (s := s) (i + 1) := by
  intro v hv
  rw [mem_Rset] at hv ⊢
  exact ⟨hv.1, reachB_mono hs hv.2⟩

lemma Rset_mono (hs : s < n) {i j : ℕ} (hij : i ≤ j) :
    Rset (n := n) (g := g) (s := s) i ⊆ Rset (n := n) (g := g) (s := s) j := by
  intro v hv
  rw [mem_Rset] at hv ⊢
  exact ⟨hv.1, reachB_mono_le hs hij hv.2⟩

lemma Rset_succ_congr {a b : ℕ}
    (h : Rset (n := n) (g := g) (s := s) a = Rset (n := n) (g := g) (s := s) b) :
    Rset (n := n) (g := g) (s := s) (a + 1) = Rset (n := n) (g := g) (s := s) (b + 1) := by
  have key : ∀ u, u < n → (reachB n g s a u = true ↔ reachB n g s b u = true) := by
    intro u hu
    constructor
    · intro hau
      have : u ∈ Rset (n := n) (g := g) (s := s) b := by rw [← h, mem_Rset]; exact ⟨hu, hau⟩
      exact (mem_Rset.1 this).2
    · intro hbu
      have : u ∈ Rset (n := n) (g := g) (s := s) a := by rw [h, mem_Rset]; exact ⟨hu, hbu⟩
      exact (mem_Rset.1 this).2
  ext v
  simp only [mem_Rset, reachB_succ_iff]
  constructor
  · rintro ⟨hv, -, u, hu, h1, h2⟩
    exact ⟨hv, hv, u, hu, (key u hu).1 h1, h2⟩
  · rintro ⟨hv, -, u, hu, h1, h2⟩
    exact ⟨hv, hv, u, hu, (key u hu).2 h1, h2⟩

lemma Rset_stab {k : ℕ}
    (h : Rset (n := n) (g := g) (s := s) (k + 1) = Rset (n := n) (g := g) (s := s) k) :
    ∀ m, Rset (n := n) (g := g) (s := s) (k + m) = Rset (n := n) (g := g) (s := s) k := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      have : Rset (n := n) (g := g) (s := s) (k + m + 1)
          = Rset (n := n) (g := g) (s := s) (k + 1) := Rset_succ_congr ih
      rw [show k + (m + 1) = k + m + 1 from rfl, this, h]

lemma cnt_le_n (i : ℕ) : cnt (n := n) (g := g) (s := s) i ≤ n := by
  have := Finset.card_filter_le (Finset.range n) (fun v => reachB n g s i v = true)
  simpa [cnt, Rset] using this

lemma cnt_zero (hs : s < n) : cnt (n := n) (g := g) (s := s) 0 = 1 := by
  have : Rset (n := n) (g := g) (s := s) 0 = {s} := by
    ext v; simp [mem_Rset]
    intro hv; omega
  simp [cnt, this]

/-- The reachability sets stabilise by step `n`. -/
lemma Rset_subset_n (hs : s < n) (m : ℕ) :
    Rset (n := n) (g := g) (s := s) m ⊆ Rset (n := n) (g := g) (s := s) n := by
  -- either some level repeats early, or the counts grow strictly
  have main : ∀ i : ℕ, (∃ k, k ≤ i ∧ Rset (n := n) (g := g) (s := s) (k + 1)
      = Rset (n := n) (g := g) (s := s) k) ∨ i + 1 ≤ cnt (n := n) (g := g) (s := s) i := by
    intro i
    induction i with
    | zero => right; rw [cnt_zero hs]
    | succ i ih =>
        rcases ih with ⟨k, hk, hkk⟩ | hcnt
        · exact Or.inl ⟨k, by omega, hkk⟩
        · by_cases hstep : Rset (n := n) (g := g) (s := s) (i + 1)
              = Rset (n := n) (g := g) (s := s) i
          · exact Or.inl ⟨i, by omega, hstep⟩
          · right
            have hsub := Rset_subset_succ hs (n := n) (g := g) (s := s) i
            have hlt : cnt (n := n) (g := g) (s := s) i < cnt (n := n) (g := g) (s := s) (i + 1) := by
              rcases lt_or_eq_of_le (Finset.card_le_card hsub) with h | h
              · exact h
              · exact absurd (Finset.eq_of_subset_of_card_le hsub (le_of_eq h.symm)).symm hstep
            omega
  rcases main n with ⟨k, hk, hkk⟩ | hbad
  · rcases Nat.lt_or_ge m n with hm | hm
    · exact Rset_mono hs (le_of_lt hm)
    · have h1 : Rset (n := n) (g := g) (s := s) m = Rset (n := n) (g := g) (s := s) k := by
        have := Rset_stab (n := n) (g := g) (s := s) hkk (m - k)
        rwa [show k + (m - k) = m by omega] at this
      have h2 : Rset (n := n) (g := g) (s := s) n = Rset (n := n) (g := g) (s := s) k := by
        have := Rset_stab (n := n) (g := g) (s := s) hkk (n - k)
        rwa [show k + (n - k) = n by omega] at this
      rw [h1, h2]
  · have := cnt_le_n (n := n) (g := g) (s := s) n
    omega

lemma reachB_le_n (hs : s < n) {m v : ℕ} (h : reachB n g s m v = true) :
    reachB n g s n v = true := by
  have hv : v < n := reachB_lt hs h
  have : v ∈ Rset (n := n) (g := g) (s := s) n :=
    Rset_subset_n hs m (mem_Rset.2 ⟨hv, h⟩)
  exact (mem_Rset.1 this).2

/-! ### Comparison with the usual reflexive-transitive-closure reachability -/

lemma reachB_of_reflTransGen (hs : s < n) (hg : ∀ u v, g u v = true → u < n ∧ v < n)
    {v : ℕ} (h : Relation.ReflTransGen (fun a b => g a b = true) s v) :
    reachB n g s n v = true := by
  have : ∃ m, reachB n g s m v = true := by
    induction h with
    | refl => exact ⟨0, by simp⟩
    | @tail b c _ hbc ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, (reachB_succ_iff m c).2
          ⟨(hg _ _ hbc).2, b, (hg _ _ hbc).1, hm, Or.inr hbc⟩⟩
  obtain ⟨m, hm⟩ := this
  exact reachB_le_n hs hm

lemma reflTransGen_of_reachB {m v : ℕ} (h : reachB n g s m v = true) :
    Relation.ReflTransGen (fun a b => g a b = true) s v := by
  induction m generalizing v with
  | zero => simp only [reachB_zero, beq_iff_eq] at h; subst h; exact Relation.ReflTransGen.refl
  | succ m ih =>
      obtain ⟨-, u, -, hu, huv⟩ := (reachB_succ_iff m v).1 h
      rcases huv with rfl | huv
      · exact ih hu
      · exact Relation.ReflTransGen.tail (ih hu) huv

end Graph

/-! ## The Immerman-Szelepcsenyi machine

The configurations below are those of the nondeterministic *inductive counting* machine.
All the numeric components of a configuration stay bounded by `n + 1`, so the machine has only
polynomially many (in `n`) reachable configurations, i.e. it runs in space `O(log n)`; each
transition inspects the graph in at most one place.  The machine accepts (i.e. `St.acc` is
reachable from the initial configuration) if and only if `t` is *not* reachable from `s`.
This is exactly the Immerman-Szelepcsenyi theorem `NL = coNL`, since `s-t` reachability is
`NL`-complete and the configuration graph of an arbitrary `NL` machine is a graph of this kind. -/

/-- Configurations of the Immerman-Szelepcsenyi machine.

* `levelStart i c`: the count `c = |R_i|` of vertices reachable in `≤ i` steps has been
  established; start working on level `i + 1`.
* `outer i c d j`: computing `|R_{i+1}|`; vertices `< j` have been processed and `d` of them
  were found in `R_{i+1}`.
* `walkYes i c d j w r`: certifying `j ∈ R_{i+1}` by guessing a walk; currently at vertex `w`
  with `r` steps to go.
* `inner i c d j u e`: certifying `j ∉ R_{i+1}`; scanning candidate members `u` of `R_i`, of
  which `e` have been certified so far (all of them different from `j` and non-adjacent to `j`).
* `walkIn i c d j u e w r`: certifying `u ∈ R_i` by guessing a walk.
* `acc`: the accepting configuration. -/
inductive St where
  | levelStart (i c : ℕ)
  | outer (i c d j : ℕ)
  | walkYes (i c d j w r : ℕ)
  | inner (i c d j u e : ℕ)
  | walkIn (i c d j u e w r : ℕ)
  | acc
  deriving DecidableEq

section Machine

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s t : ℕ)

/-- The transition relation of the machine.  Every transition is a local test:
comparing two numbers `< n + 2`, or a single query to the adjacency function `g`. -/
inductive Step : St → St → Prop
  | startLevel {i c : ℕ} (h : i < n) : Step (.levelStart i c) (.outer i c 0 0)
  | startFinal {c : ℕ} : Step (.levelStart n c) (.inner n c 0 t 0 0)
  | outerYes {i c d j : ℕ} (h : j < n) : Step (.outer i c d j) (.walkYes i c d j s (i + 1))
  | outerNo {i c d j : ℕ} (h : j < n) : Step (.outer i c d j) (.inner i c d j 0 0)
  | outerDone {i c d : ℕ} : Step (.outer i c d n) (.levelStart (i + 1) d)
  | walkYesStep {i c d j w r w' : ℕ} (h : w' < n) (hg : w = w' ∨ g w w' = true) :
      Step (.walkYes i c d j w (r + 1)) (.walkYes i c d j w' r)
  | walkYesDone {i c d j w : ℕ} (hw : w = j) :
      Step (.walkYes i c d j w 0) (.outer i c (d + 1) (j + 1))
  | innerSkip {i c d j u e : ℕ} (h : u < n) : Step (.inner i c d j u e) (.inner i c d j (u + 1) e)
  | innerCert {i c d j u e : ℕ} (h : u < n) : Step (.inner i c d j u e) (.walkIn i c d j u e s i)
  | walkInStep {i c d j u e w r w' : ℕ} (h : w' < n) (hg : w = w' ∨ g w w' = true) :
      Step (.walkIn i c d j u e w (r + 1)) (.walkIn i c d j u e w' r)
  | walkInDone {i c d j u e w : ℕ} (hw : w = u) (hne : u ≠ j) (hgj : g u j = false) :
      Step (.walkIn i c d j u e w 0) (.inner i c d j (u + 1) (e + 1))
  | innerDone {i c d j e : ℕ} (h : i < n) (he : e = c) :
      Step (.inner i c d j n e) (.outer i c d (j + 1))
  | innerAccept {c d j e : ℕ} (he : e = c) : Step (.inner n c d j n e) .acc

/-- The initial configuration: `|R_0| = 1`. -/
def init : St := .levelStart 0 1

/-- The machine accepts iff the accepting configuration is reachable. -/
def Accepts : Prop := Relation.ReflTransGen (Step n g s t) (init) .acc

/-- Number of vertices `< j` that are reachable in at most `k` steps. -/
def cntUpto (k j : ℕ) : ℕ := ((Finset.range j).filter (fun v => reachB n g s k v = true)).card

/-- Number of vertices `x < u` reachable in at most `i` steps which are different from `j` and
not adjacent to `j`. -/
def cntPhi (i j u : ℕ) : ℕ :=
  ((Finset.range u).filter (fun x => reachB n g s i x = true ∧ x ≠ j ∧ g x j = false)).card

/-- The soundness invariant of the machine. -/
def Inv : St → Prop
  | .levelStart i c => i ≤ n ∧ c = cnt (n := n) (g := g) (s := s) i
  | .outer i c d j =>
      i < n ∧ c = cnt (n := n) (g := g) (s := s) i ∧ j ≤ n ∧ d = cntUpto n g s (i + 1) j
  | .walkYes i c d j w r =>
      i < n ∧ c = cnt (n := n) (g := g) (s := s) i ∧ j < n ∧ d = cntUpto n g s (i + 1) j ∧
        r ≤ i + 1 ∧ reachB n g s (i + 1 - r) w = true
  | .inner i c d j u e =>
      i ≤ n ∧ c = cnt (n := n) (g := g) (s := s) i ∧ u ≤ n ∧ e ≤ cntPhi n g s i j u ∧
        (i < n → j < n ∧ d = cntUpto n g s (i + 1) j) ∧ (i = n → j = t) ∧ d ≤ n
  | .walkIn i c d j u e w r =>
      i ≤ n ∧ c = cnt (n := n) (g := g) (s := s) i ∧ u < n ∧ e ≤ cntPhi n g s i j u ∧
        (i < n → j < n ∧ d = cntUpto n g s (i + 1) j) ∧ (i = n → j = t) ∧
        r ≤ i ∧ reachB n g s (i - r) w = true ∧ d ≤ n
  | .acc => reachB n g s n t = false

/-! ### Elementary facts about the counters -/

lemma card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (j : ℕ) :
    ((Finset.range (j + 1)).filter p).card
      = ((Finset.range j).filter p).card + (if p j then 1 else 0) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : p j
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h, add_zero]

variable {n g s t}

@[simp] lemma cntUpto_zero (k : ℕ) : cntUpto n g s k 0 = 0 := by simp [cntUpto]

lemma cntUpto_succ_pos {k j : ℕ} (h : reachB n g s k j = true) :
    cntUpto n g s k (j + 1) = cntUpto n g s k j + 1 := by
  simp [cntUpto, card_filter_range_succ, h]

lemma cntUpto_succ_neg {k j : ℕ} (h : ¬ reachB n g s k j = true) :
    cntUpto n g s k (j + 1) = cntUpto n g s k j := by
  simp [cntUpto, card_filter_range_succ, h]

lemma cntUpto_n (k : ℕ) : cntUpto n g s k n = cnt (n := n) (g := g) (s := s) k := rfl

lemma cntUpto_le (k j : ℕ) : cntUpto n g s k j ≤ j := by
  simpa [cntUpto] using (Finset.card_filter_le (Finset.range j)
    (fun v => reachB n g s k v = true)).trans_eq (Finset.card_range j)

lemma cntPhi_le (i j u : ℕ) : cntPhi n g s i j u ≤ u := by
  simpa [cntPhi] using (Finset.card_filter_le (Finset.range u)
    (fun x => reachB n g s i x = true ∧ x ≠ j ∧ g x j = false)).trans_eq (Finset.card_range u)

lemma cntPhi_le_succ (i j u : ℕ) : cntPhi n g s i j u ≤ cntPhi n g s i j (u + 1) := by
  simp [cntPhi, card_filter_range_succ]

lemma cntPhi_succ_pos {i j u : ℕ} (h1 : reachB n g s i u = true) (h2 : u ≠ j)
    (h3 : g u j = false) : cntPhi n g s i j (u + 1) = cntPhi n g s i j u + 1 := by
  simp [cntPhi, card_filter_range_succ, h1, h2, h3]

/-- The key counting step: if we have certified `|R_i|` many vertices of `R_i`, all different
from `j` and non-adjacent to `j`, then *every* vertex of `R_i` has this property. -/
lemma phi_full {i j : ℕ} (h : cnt (n := n) (g := g) (s := s) i ≤ cntPhi n g s i j n)
    {x : ℕ} (hx : x < n) (hrx : reachB n g s i x = true) : x ≠ j ∧ g x j = false := by
  set A := (Finset.range n).filter
    (fun y => reachB n g s i y = true ∧ y ≠ j ∧ g y j = false) with hA
  set B := Rset (n := n) (g := g) (s := s) i with hB
  have hsub : A ⊆ B := by
    intro y hy
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hy
    exact mem_Rset.2 ⟨hy.1, hy.2.1⟩
  have hcard : B.card ≤ A.card := h
  have : A = B := Finset.eq_of_subset_of_card_le hsub hcard
  have hxB : x ∈ B := mem_Rset.2 ⟨hx, hrx⟩
  rw [← this] at hxB
  simp only [hA, Finset.mem_filter, Finset.mem_range] at hxB
  exact hxB.2.2

/-- If all of `R_i` avoids `j` and is non-adjacent to `j`, then `j ∉ R_{i+1}`. -/
lemma not_reachB_succ {i j : ℕ}
    (h : ∀ x, x < n → reachB n g s i x = true → x ≠ j ∧ g x j = false) :
    ¬ reachB n g s (i + 1) j = true := by
  intro hc
  obtain ⟨-, u, hu, hru, hstep⟩ := (reachB_succ_iff i j).1 hc
  obtain ⟨hne, hgj⟩ := h u hu hru
  rcases hstep with rfl | hstep
  · exact hne rfl
  · rw [hstep] at hgj; exact Bool.noConfusion hgj

/-! ### Soundness: the invariant is preserved by every transition -/

lemma Inv_init (hs : s < n) : Inv n g s t init := by
  refine ⟨Nat.zero_le _, ?_⟩
  rw [cnt_zero hs]

lemma Inv_step (hs : s < n) {a b : St} (hstep : Step n g s t a b) (ha : Inv n g s t a) :
    Inv n g s t b := by
  cases hstep with
  | @startLevel i c h =>
      obtain ⟨-, hc⟩ := ha
      exact ⟨h, hc, Nat.zero_le _, (cntUpto_zero _).symm⟩
  | @startFinal c =>
      obtain ⟨-, hc⟩ := ha
      exact ⟨le_rfl, hc, Nat.zero_le _, Nat.zero_le _, fun h => absurd h (lt_irrefl n),
        fun _ => rfl, Nat.zero_le _⟩
  | @outerYes i c d j h =>
      obtain ⟨hi, hc, -, hd⟩ := ha
      exact ⟨hi, hc, h, hd, le_rfl, by simp⟩
  | @outerNo i c d j h =>
      obtain ⟨hi, hc, -, hd⟩ := ha
      refine ⟨le_of_lt hi, hc, Nat.zero_le _, Nat.zero_le _, fun _ => ⟨h, hd⟩,
        fun he => absurd he (by omega), ?_⟩
      rw [hd]
      exact le_trans (cntUpto_le _ _) (le_of_lt h)
  | @outerDone i c d =>
      obtain ⟨hi, hc, -, hd⟩ := ha
      exact ⟨hi, by rw [hd, cntUpto_n]⟩
  | @walkYesStep i c d j w r w' h hg =>
      obtain ⟨hi, hc, hj, hd, hr, hrw⟩ := ha
      refine ⟨hi, hc, hj, hd, by omega, ?_⟩
      have hw : w < n := reachB_lt hs hrw
      have hkey : reachB n g s (i + 1 - (r + 1) + 1) w' = true :=
        (reachB_succ_iff _ _).2 ⟨h, w, hw, hrw, hg⟩
      rwa [show i + 1 - (r + 1) + 1 = i + 1 - r by omega] at hkey
  | @walkYesDone i c d j w hw =>
      obtain ⟨hi, hc, hj, hd, -, hrw⟩ := ha
      subst hw
      refine ⟨hi, hc, by omega, ?_⟩
      rw [cntUpto_succ_pos (by simpa using hrw), hd]
  | @innerSkip i c d j u e h =>
      obtain ⟨hi, hc, -, he, h1, h2, hdn⟩ := ha
      exact ⟨hi, hc, by omega, le_trans he (cntPhi_le_succ _ _ _), h1, h2, hdn⟩
  | @innerCert i c d j u e h =>
      obtain ⟨hi, hc, -, he, h1, h2, hdn⟩ := ha
      exact ⟨hi, hc, h, he, h1, h2, le_rfl, by simp, hdn⟩
  | @walkInStep i c d j u e w r w' h hg =>
      obtain ⟨hi, hc, hu, he, h1, h2, hr, hrw, hdn⟩ := ha
      refine ⟨hi, hc, hu, he, h1, h2, by omega, ?_, hdn⟩
      have hw : w < n := reachB_lt hs hrw
      have hkey : reachB n g s (i - (r + 1) + 1) w' = true :=
        (reachB_succ_iff _ _).2 ⟨h, w, hw, hrw, hg⟩
      rwa [show i - (r + 1) + 1 = i - r by omega] at hkey
  | @walkInDone i c d j u e w hw hne hgj =>
      obtain ⟨hi, hc, hu, he, h1, h2, -, hrw, hdn⟩ := ha
      subst hw
      refine ⟨hi, hc, by omega, ?_, h1, h2, hdn⟩
      rw [cntPhi_succ_pos (by simpa using hrw) hne hgj]
      omega
  | @innerDone i c d j e h he =>
      obtain ⟨hi, hc, -, hphi, h1, -, -⟩ := ha
      obtain ⟨hj, hd⟩ := h1 h
      refine ⟨h, hc, by omega, ?_⟩
      have hle : cnt (n := n) (g := g) (s := s) i ≤ cntPhi n g s i j n := by
        rw [← hc, ← he]; exact hphi
      rw [cntUpto_succ_neg (not_reachB_succ (fun x hx hrx => phi_full hle hx hrx)), hd]
  | @innerAccept c d j e he =>
      obtain ⟨-, hc, -, hphi, -, h2, -⟩ := ha
      have hj : j = t := h2 rfl
      have hle : cnt (n := n) (g := g) (s := s) n ≤ cntPhi n g s n t n := by
        rw [← hj, ← hc, ← he]; exact hphi
      by_contra hcon
      have hrt : reachB n g s n t = true := by
        cases hb : reachB n g s n t
        · exact absurd hb hcon
        · rfl
      exact (phi_full hle (reachB_lt hs hrt) hrt).1 rfl

lemma Inv_of_reachable (hs : s < n) {b : St}
    (h : Relation.ReflTransGen (Step n g s t) init b) : Inv n g s t b := by
  induction h with
  | refl => exact Inv_init hs
  | tail _ hstep ih => exact Inv_step hs hstep ih

/-- **Soundness**: if the machine accepts then `t` is not reachable from `s`. -/
lemma soundness (hs : s < n) (h : Accepts n g s t) : reachB n g s n t = false :=
  Inv_of_reachable hs h

/-! ### Completeness: if `t` is not reachable, an accepting run exists -/

/-- Guessing a walk certifying membership in `R_r`, inside the `walkYes` phase. -/
lemma walkYes_run (i c d j : ℕ) :
    ∀ (r a m : ℕ), reachB n g s r a = true →
      Relation.ReflTransGen (Step n g s t) (.walkYes i c d j s (r + m)) (.walkYes i c d j a m) := by
  intro r
  induction r with
  | zero =>
      intro a m h
      simp only [reachB_zero, beq_iff_eq] at h
      subst h
      rw [Nat.zero_add]
  | succ r ih =>
      intro a m h
      obtain ⟨ha, u, -, hru, hstep⟩ := (reachB_succ_iff r a).1 h
      have h1 := ih u (m + 1) hru
      rw [show r + (m + 1) = r + 1 + m by omega] at h1
      exact h1.tail (Step.walkYesStep ha hstep)

/-- Guessing a walk certifying membership in `R_r`, inside the `walkIn` phase. -/
lemma walkIn_run (i c d j u e : ℕ) :
    ∀ (r a m : ℕ), reachB n g s r a = true →
      Relation.ReflTransGen (Step n g s t) (.walkIn i c d j u e s (r + m))
        (.walkIn i c d j u e a m) := by
  intro r
  induction r with
  | zero =>
      intro a m h
      simp only [reachB_zero, beq_iff_eq] at h
      subst h
      rw [Nat.zero_add]
  | succ r ih =>
      intro a m h
      obtain ⟨ha, u', -, hru, hstep⟩ := (reachB_succ_iff r a).1 h
      have h1 := ih u' (m + 1) hru
      rw [show r + (m + 1) = r + 1 + m by omega] at h1
      exact h1.tail (Step.walkInStep ha hstep)

/-- The inner loop can certify all of `R_i` when every element of `R_i` differs from `j` and is
not adjacent to `j`. -/
lemma inner_run {i j : ℕ} (c d : ℕ)
    (hphi : ∀ x, x < n → reachB n g s i x = true → x ≠ j ∧ g x j = false) :
    ∀ (k u : ℕ), u + k = n →
      Relation.ReflTransGen (Step n g s t) (.inner i c d j u (cntUpto n g s i u))
        (.inner i c d j n (cnt (n := n) (g := g) (s := s) i)) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      obtain rfl : u = n := by omega
      rw [cntUpto_n]
  | succ k ih =>
      intro u hu
      have hun : u < n := by omega
      by_cases hr : reachB n g s i u = true
      · obtain ⟨hne, hgj⟩ := hphi u hun hr
        have s1 : Step n g s t (.inner i c d j u (cntUpto n g s i u))
            (.walkIn i c d j u (cntUpto n g s i u) s i) := Step.innerCert hun
        have s2 := walkIn_run (t := t) i c d j u (cntUpto n g s i u) i u 0 hr
        rw [Nat.add_zero] at s2
        have s3 : Step n g s t (.walkIn i c d j u (cntUpto n g s i u) u 0)
            (.inner i c d j (u + 1) (cntUpto n g s i u + 1)) := Step.walkInDone rfl hne hgj
        have s4 := ih (u + 1) (by omega)
        rw [cntUpto_succ_pos hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4
      · have s1 : Step n g s t (.inner i c d j u (cntUpto n g s i u))
            (.inner i c d j (u + 1) (cntUpto n g s i u)) := Step.innerSkip hun
        have s4 := ih (u + 1) (by omega)
        rw [cntUpto_succ_neg hr] at s4
        exact (Relation.ReflTransGen.single s1).trans s4

/-- One pass of the outer loop computes `|R_{i+1}|` from `|R_i|`. -/
lemma outer_run (hs : s < n) {i : ℕ} (hi : i < n) :
    ∀ (k j : ℕ), j + k = n →
      Relation.ReflTransGen (Step n g s t)
        (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
        (.levelStart (i + 1) (cnt (n := n) (g := g) (s := s) (i + 1))) := by
  intro k
  induction k with
  | zero =>
      intro j hj
      obtain rfl : j = n := by omega
      rw [cntUpto_n]
      exact Relation.ReflTransGen.single Step.outerDone
  | succ k ih =>
      intro j hj
      have hjn : j < n := by omega
      by_cases hr : reachB n g s (i + 1) j = true
      · have s1 : Step n g s t
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
            (.walkYes i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j s (i + 1)) :=
          Step.outerYes hjn
        have s2 := walkYes_run (t := t) i (cnt (n := n) (g := g) (s := s) i)
          (cntUpto n g s (i + 1) j) j (i + 1) j 0 hr
        rw [Nat.add_zero] at s2
        have s3 : Step n g s t
            (.walkYes i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j j 0)
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j + 1) (j + 1)) :=
          Step.walkYesDone rfl
        have s4 := ih (j + 1) (by omega)
        rw [cntUpto_succ_pos hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4
      · have hphi : ∀ x, x < n → reachB n g s i x = true → x ≠ j ∧ g x j = false := by
          intro x hx hrx
          constructor
          · rintro rfl
            exact hr (reachB_mono hs hrx)
          · cases hgx : g x j with
            | false => rfl
            | true =>
                exact absurd ((reachB_succ_iff i j).2 ⟨hjn, x, hx, hrx, Or.inr hgx⟩) hr
        have s1 : Step n g s t
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j)
            (.inner i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j 0 0) :=
          Step.outerNo hjn
        have s2 := inner_run (t := t) (i := i) (j := j) (cnt (n := n) (g := g) (s := s) i)
          (cntUpto n g s (i + 1) j) hphi n 0 (by omega)
        rw [cntUpto_zero] at s2
        have s3 : Step n g s t
            (.inner i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) j n
              (cnt (n := n) (g := g) (s := s) i))
            (.outer i (cnt (n := n) (g := g) (s := s) i) (cntUpto n g s (i + 1) j) (j + 1)) :=
          Step.innerDone hi rfl
        have s4 := ih (j + 1) (by omega)
        rw [cntUpto_succ_neg hr] at s4
        exact ((Relation.ReflTransGen.single s1).trans s2).tail s3 |>.trans s4

/-- All the level counts can be computed, one level at a time. -/
lemma levels_run (hs : s < n) :
    ∀ (k i : ℕ), i + k = n →
      Relation.ReflTransGen (Step n g s t) (.levelStart i (cnt (n := n) (g := g) (s := s) i))
        (.levelStart n (cnt (n := n) (g := g) (s := s) n)) := by
  intro k
  induction k with
  | zero =>
      intro i hi
      obtain rfl : i = n := by omega
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro i hi
      have hin : i < n := by omega
      have s1 : Step n g s t (.levelStart i (cnt (n := n) (g := g) (s := s) i))
          (.outer i (cnt (n := n) (g := g) (s := s) i) 0 0) := Step.startLevel hin
      have s2 := outer_run (g := g) (t := t) hs hin n 0 (by omega)
      rw [cntUpto_zero] at s2
      exact ((Relation.ReflTransGen.single s1).trans s2).trans (ih (i + 1) (by omega))

/-- **Completeness**: if `t` is not reachable from `s` then the machine accepts. -/
lemma completeness (hs : s < n) (hg : ∀ u v, g u v = true → u < n ∧ v < n)
    (h : reachB n g s n t = false) : Accepts n g s t := by
  have hphi : ∀ x, x < n → reachB n g s n x = true → x ≠ t ∧ g x t = false := by
    intro x hx hrx
    constructor
    · rintro rfl
      rw [h] at hrx
      exact Bool.noConfusion hrx
    · cases hgx : g x t with
      | false => rfl
      | true =>
          have ht : t < n := (hg _ _ hgx).2
          have : reachB n g s (n + 1) t = true :=
            (reachB_succ_iff n t).2 ⟨ht, x, hx, hrx, Or.inr hgx⟩
          rw [reachB_le_n hs this] at h
          exact Bool.noConfusion h
  have r1 : Relation.ReflTransGen (Step n g s t) init
      (.levelStart n (cnt (n := n) (g := g) (s := s) n)) := by
    have h0 : (init : St) = .levelStart 0 (cnt (n := n) (g := g) (s := s) 0) := by
      rw [cnt_zero hs]; rfl
    rw [h0]
    exact levels_run hs n 0 (by omega)
  have s1 : Step n g s t (.levelStart n (cnt (n := n) (g := g) (s := s) n))
      (.inner n (cnt (n := n) (g := g) (s := s) n) 0 t 0 0) := Step.startFinal
  have r2 := inner_run (t := t) (i := n) (j := t) (cnt (n := n) (g := g) (s := s) n) 0 hphi n 0
    (by omega)
  rw [cntUpto_zero] at r2
  have s2 : Step n g s t
      (.inner n (cnt (n := n) (g := g) (s := s) n) 0 t n (cnt (n := n) (g := g) (s := s) n))
      .acc := Step.innerAccept rfl
  exact ((r1.tail s1).trans r2).tail s2

end Machine

/-! ### Space bound: only polynomially many configurations are reachable

Every numeric component of a reachable configuration is `< n + 2`, so all reachable
configurations lie in a set of size at most `6 * (n + 2) ^ 8`; a machine with that many
configurations runs in space `O(log n)`. -/

/-- Assemble a configuration out of a tag and eight numbers. -/
def mkSt : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → St
  | 0, x => .levelStart x.1 x.2.1
  | 1, x => .outer x.1 x.2.1 x.2.2.1 x.2.2.2.1
  | 2, x => .walkYes x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
  | 3, x => .inner x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1
  | 4, x => .walkIn x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
      x.2.2.2.2.2.2.2
  | _, _ => .acc

/-- All eight-tuples of numbers `< m`. -/
def Tuple8 (m : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ
    Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m ×ˢ Finset.range m

/-- All configurations whose numeric components are `< m`. -/
def Box (m : ℕ) : Finset St := (Finset.range 6 ×ˢ Tuple8 m).image (fun p => mkSt p.1 p.2)

lemma card_Box_le (m : ℕ) : (Box m).card ≤ 6 * m ^ 8 := by
  refine le_trans Finset.card_image_le ?_
  rw [Finset.card_product, Finset.card_range]
  have : (Tuple8 m).card = m ^ 8 := by
    simp only [Tuple8, Finset.card_product, Finset.card_range]
    ring
  rw [this]

lemma mem_Tuple8 {m a b c d e f h k : ℕ} (ha : a < m) (hb : b < m) (hc : c < m) (hd : d < m)
    (he : e < m) (hf : f < m) (hh : h < m) (hk : k < m) :
    (a, b, c, d, e, f, h, k) ∈ Tuple8 m := by
  simp only [Tuple8, Finset.mem_product, Finset.mem_range]
  exact ⟨ha, hb, hc, hd, he, hf, hh, hk⟩

lemma mem_Box {m tag : ℕ} {x : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (htag : tag < 6)
    (hx : x ∈ Tuple8 m) : mkSt tag x ∈ Box m :=
  Finset.mem_image.2 ⟨(tag, x), Finset.mem_product.2 ⟨Finset.mem_range.2 htag, hx⟩, rfl⟩

section Bound

variable {n : ℕ} {g : ℕ → ℕ → Bool} {s t : ℕ}

lemma mem_Box_of_Inv (hs : s < n) (ht : t < n) {w : St} (h : Inv n g s t w) :
    w ∈ Box (n + 2) := by
  cases w with
  | levelStart i c =>
      obtain ⟨hi, hc⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      exact mem_Box (m := n + 2) (tag := 0) (x := (i, c, 0, 0, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | outer i c d j =>
      obtain ⟨hi, hc, hj, hd⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hdn : d ≤ n := by rw [hd]; exact le_trans (cntUpto_le _ _) hj
      exact mem_Box (m := n + 2) (tag := 1) (x := (i, c, d, j, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | walkYes i c d j w r =>
      obtain ⟨hi, hc, hj, hd, hr, hrw⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hdn : d ≤ n := by rw [hd]; exact le_trans (cntUpto_le _ _) (le_of_lt hj)
      have hwn : w < n := reachB_lt hs hrw
      exact mem_Box (m := n + 2) (tag := 2) (x := (i, c, d, j, w, r, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | inner i c d j u e =>
      obtain ⟨hi, hc, hu, he, h1, h2, hdn⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hen : e ≤ n := le_trans he (le_trans (cntPhi_le _ _ _) hu)
      have hjn : j < n := by
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact (h1 hlt).1
        · have : i = n := by omega
          rw [h2 this]; exact ht
      exact mem_Box (m := n + 2) (tag := 3) (x := (i, c, d, j, u, e, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | walkIn i c d j u e w r =>
      obtain ⟨hi, hc, hu, he, h1, h2, hr, hrw, hdn⟩ := h
      have hcn : c ≤ n := by rw [hc]; exact cnt_le_n _
      have hen : e ≤ n := le_trans he (le_trans (cntPhi_le _ _ _) (le_of_lt hu))
      have hwn : w < n := reachB_lt hs hrw
      have hjn : j < n := by
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact (h1 hlt).1
        · have : i = n := by omega
          rw [h2 this]; exact ht
      exact mem_Box (m := n + 2) (tag := 4) (x := (i, c, d, j, u, e, w, r)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))
  | acc =>
      exact mem_Box (m := n + 2) (tag := 5) (x := (0, 0, 0, 0, 0, 0, 0, 0)) (by norm_num)
        (mem_Tuple8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega))

end Bound

/-! ## The Immerman-Szelepcsenyi theorem: `NL = coNL` -/

/-- **Immerman-Szelepcsenyi theorem** (`NL = coNL`).

Let `g` be (the adjacency function of) a directed graph on the vertex set `{0, …, n-1}` — for
instance the configuration graph of a nondeterministic space-bounded machine — and let `s`, `t`
be two vertices.  The nondeterministic machine `Step n g s t` (the inductive counting machine of
Immerman and Szelepcsenyi, whose transitions are local: each of them compares numbers `< n + 2`
and performs at most one query to `g`) satisfies:

1. it accepts, i.e. it has a run from the initial configuration to the accepting configuration,
   if and only if `t` is **not** reachable from `s` in the graph;
2. every configuration reachable from the initial one lies in the explicit set `Box (n + 2)`,
   whose cardinality is at most `6 * (n + 2) ^ 8`, i.e. the machine only uses `O(log n)` bits of
   workspace.

Applied to the configuration graph of a nondeterministic machine running in space `S(m) ≥ log m`
(which has `n = 2 ^ O(S(m))` configurations), this says that the complement of its language is
accepted by a nondeterministic machine that runs in space `O(S(m))`: nondeterministic space is
closed under complementation, `NL = coNL`. -/
theorem immerman_szelepcsenyi {n : ℕ} {g : ℕ → ℕ → Bool} {s t : ℕ}
    (hs : s < n) (ht : t < n) (hgr : ∀ u v, g u v = true → u < n ∧ v < n) :
    (Accepts n g s t ↔ ¬ Relation.ReflTransGen (fun a b => g a b = true) s t) ∧
      (∀ w, Relation.ReflTransGen (Step n g s t) init w → w ∈ Box (n + 2)) ∧
      (Box (n + 2)).card ≤ 6 * (n + 2) ^ 8 := by
  refine ⟨⟨?_, ?_⟩, ?_, card_Box_le _⟩
  · intro hacc hreach
    have h1 : reachB n g s n t = false := soundness hs hacc
    have h2 : reachB n g s n t = true := reachB_of_reflTransGen hs hgr hreach
    rw [h1] at h2
    exact Bool.noConfusion h2
  · intro hno
    refine completeness hs hgr ?_
    cases hb : reachB n g s n t with
    | false => rfl
    | true => exact absurd (reflTransGen_of_reachB hb) hno
  · intro w hw
    exact mem_Box_of_Inv hs ht (Inv_of_reachable hs hw)

/-! ## Complementing an arbitrary finite configuration graph

The same statement for a nondeterministic machine whose configurations form an arbitrary finite
type (rather than an initial segment of `ℕ`). -/

section ConfigGraph

variable {V : Type} [Fintype V]

/-- Encoding of a configuration as a number `< Fintype.card V`. -/
noncomputable def enc (v : V) : ℕ := ((Fintype.equivFin V) v : ℕ)

/-- The transition relation of a finite configuration graph, transported to
`{0, …, Fintype.card V - 1}`. -/
noncomputable def gOf (stepV : V → V → Bool) (u v : ℕ) : Bool :=
  if hu : u < Fintype.card V then
    if hv : v < Fintype.card V then
      stepV ((Fintype.equivFin V).symm ⟨u, hu⟩) ((Fintype.equivFin V).symm ⟨v, hv⟩)
    else false
  else false

lemma enc_lt (v : V) : enc v < Fintype.card V := (Fintype.equivFin V v).isLt

@[simp] lemma enc_symm {u : ℕ} (h : u < Fintype.card V) :
    enc ((Fintype.equivFin V).symm ⟨u, h⟩) = u := by
  simp [enc]

@[simp] lemma symm_enc (v : V) (h : enc v < Fintype.card V) :
    (Fintype.equivFin V).symm ⟨enc v, h⟩ = v := by
  simp [enc]

lemma gOf_lt (stepV : V → V → Bool) {u v : ℕ} (h : gOf stepV u v = true) :
    u < Fintype.card V ∧ v < Fintype.card V := by
  unfold gOf at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

@[simp] lemma gOf_enc (stepV : V → V → Bool) (x y : V) :
    gOf stepV (enc x) (enc y) = stepV x y := by
  rw [gOf, dif_pos (enc_lt x), dif_pos (enc_lt y), symm_enc, symm_enc]

lemma reflTransGen_gOf {stepV : V → V → Bool} {x y : V}
    (h : Relation.ReflTransGen (fun a b => stepV a b = true) x y) :
    Relation.ReflTransGen (fun a b => gOf stepV a b = true) (enc x) (enc y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail (by simpa using hbc)

lemma reflTransGen_of_gOf {stepV : V → V → Bool} {x : V} {m : ℕ}
    (h : Relation.ReflTransGen (fun a b => gOf stepV a b = true) (enc x) m) :
    ∃ y : V, m = enc y ∧ Relation.ReflTransGen (fun a b => stepV a b = true) x y := by
  induction h with
  | refl => exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
      obtain ⟨y, rfl, hy⟩ := ih
      obtain ⟨-, hc⟩ := gOf_lt stepV hbc
      refine ⟨(Fintype.equivFin V).symm ⟨c, hc⟩, (enc_symm hc).symm, hy.tail ?_⟩
      show stepV y ((Fintype.equivFin V).symm ⟨c, hc⟩) = true
      rw [← gOf_enc stepV y ((Fintype.equivFin V).symm ⟨c, hc⟩), enc_symm hc]
      exact hbc

/-- **Immerman-Szelepcsenyi theorem for an arbitrary finite configuration graph.**
Given a nondeterministic machine whose configuration graph is `stepV` on the finite type `V`,
with initial configuration `v₀` and accepting configuration `v₁`, the inductive counting machine
run on the encoded graph accepts exactly when `v₁` is *not* reachable from `v₀`, and it visits at
most `6 * (|V| + 2) ^ 8` configurations. -/
theorem immerman_szelepcsenyi_configGraph (stepV : V → V → Bool) (v₀ v₁ : V) :
    (Accepts (Fintype.card V) (gOf stepV) (enc v₀) (enc v₁) ↔
        ¬ Relation.ReflTransGen (fun a b => stepV a b = true) v₀ v₁) ∧
      (∀ w, Relation.ReflTransGen (Step (Fintype.card V) (gOf stepV) (enc v₀) (enc v₁)) init w →
        w ∈ Box (Fintype.card V + 2)) ∧
      (Box (Fintype.card V + 2)).card ≤ 6 * (Fintype.card V + 2) ^ 8 := by
  obtain ⟨hiff, hbox, hcard⟩ :=
    immerman_szelepcsenyi (g := gOf stepV) (enc_lt v₀) (enc_lt v₁) (fun u v h => gOf_lt stepV h)
  refine ⟨?_, hbox, hcard⟩
  rw [hiff]
  constructor
  · intro h hreach
    exact h (reflTransGen_gOf hreach)
  · intro h hreach
    obtain ⟨y, hy, hy2⟩ := reflTransGen_of_gOf hreach
    have : y = v₁ := (Fintype.equivFin V).injective (Fin.ext hy.symm)
    exact h (this ▸ hy2)

end ConfigGraph

end CS


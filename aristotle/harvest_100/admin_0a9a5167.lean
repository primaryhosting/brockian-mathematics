/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset

/-- `RamseyProp N p q` says: for every red/blue colouring of the edges of a complete graph
(the red edges being the edges of a simple graph `G`), every set `t` of at least `N` vertices
contains a red clique of size `p` or a blue clique of size `q`.
Here "blue" means an edge of the complement `Gᶜ`. -/
def RamseyProp (N p q : ℕ) : Prop :=
  ∀ {V : Type} (G : SimpleGraph V) (t : Finset V), N ≤ t.card →
    (∃ s ⊆ t, G.IsNClique p s) ∨ (∃ s ⊆ t, Gᶜ.IsNClique q s)

section UpperBound

open scoped Classical

theorem RamseyProp.mono {N M p q : ℕ} (h : RamseyProp N p q) (hNM : N ≤ M) :
    RamseyProp M p q := fun G t ht => h G t (hNM.trans ht)

theorem RamseyProp.symm {N p q : ℕ} (h : RamseyProp N p q) : RamseyProp N q p := by
  intro V G t ht
  rcases h Gᶜ t ht with ⟨s, hs, hc⟩ | ⟨s, hs, hc⟩
  · exact Or.inr ⟨s, hs, hc⟩
  · rw [compl_compl] at hc
    exact Or.inl ⟨s, hs, hc⟩

/-- `R(2, q) ≤ q`. -/
theorem ramsey_two_left (q : ℕ) : RamseyProp q 2 q := by
  intro V G t ht
  by_cases h : ∃ x ∈ t, ∃ y ∈ t, G.Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := h
    refine Or.inl ⟨{x, y}, ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · have h1 : G.IsNClique 1 {y} := by simp
      have h2 := h1.insert (a := x) (fun b hb => by
        simp only [Finset.mem_singleton] at hb
        subst hb
        exact hxy)
      simpa using h2
  · push_neg at h
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq ht
    refine Or.inr ⟨s, hs, ⟨?_, hcard⟩⟩
    intro x hx y hy hne
    simp only [Finset.mem_coe] at hx hy
    exact ⟨hne, h x (hs hx) y (hs hy)⟩

/-- The number of ordered pairs of adjacent vertices inside a finite set is even
(the handshake lemma). -/
theorem even_sum_degrees {V : Type} (G : SimpleGraph V) (t : Finset V) :
    Even (∑ v ∈ t, {u ∈ t.erase v | G.Adj v u}.card) := by
  have hE : ∀ v ∈ t, {u ∈ t.erase v | G.Adj v u} = {u ∈ t | G.Adj v u} := by
    intro v _
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hu⟩, h⟩
      exact ⟨hu, h⟩
    · rintro ⟨hu, h⟩
      exact ⟨⟨(G.ne_of_adj h).symm, hu⟩, h⟩
  rw [Finset.sum_congr rfl (fun v hv => by rw [hE v hv]), ← ZMod.natCast_eq_zero_iff_even]
  push_cast
  have h1 : ∀ v ∈ t, (({u ∈ t | G.Adj v u}.card : ℕ) : ZMod 2)
      = ∑ u ∈ t, (if G.Adj v u then (1 : ZMod 2) else 0) := by
    intro v _
    rw [Finset.card_filter]
    push_cast
    simp
  rw [Finset.sum_congr rfl h1, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
  · intro a _
    simp only [Prod.fst_swap, Prod.snd_swap]
    by_cases h : G.Adj a.1 a.2
    · rw [if_pos h, if_pos (G.symm h)]
      decide
    · rw [if_neg h, if_neg (fun hh => h (G.symm hh))]
      simp
  · intro a _ hne heq
    apply hne
    have h : a.1 = a.2 := by
      have := congrArg Prod.fst heq
      simpa using this.symm
    rw [if_neg (by rw [h]; exact G.irrefl)]
  · intro a ha
    simp only [Finset.mem_product, Prod.fst_swap, Prod.snd_swap] at ha ⊢
    exact ⟨ha.2, ha.1⟩
  · intro a _
    exact Prod.swap_swap a

/-- If a vertex `v` of `t` has at least `m` red neighbours in `t` and `R(p, q+1) ≤ m`, then `t`
contains a red `(p+1)`-clique or a blue `(q+1)`-clique. -/
theorem exists_clique_of_card_neighbors {V : Type} {m p q : ℕ} (hm : RamseyProp m p (q + 1))
    (G : SimpleGraph V) (t : Finset V) (v : V) (hv : v ∈ t) (A : Finset V) (hAt : A ⊆ t)
    (hAadj : ∀ u ∈ A, G.Adj v u) (hcard : m ≤ A.card) :
    (∃ s ⊆ t, G.IsNClique (p + 1) s) ∨ (∃ s ⊆ t, Gᶜ.IsNClique (q + 1) s) := by
  rcases hm G A hcard with ⟨s, hs, hclique⟩ | ⟨s, hs, hclique⟩
  · refine Or.inl ⟨insert v s, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hv
      · exact hAt (hs hx)
    · exact hclique.insert (fun b hb => hAadj b (hs hb))
  · exact Or.inr ⟨s, fun x hx => hAt (hs hx), hclique⟩

/-- Red degree plus blue degree of a vertex inside `t` is `#t - 1`. -/
theorem card_red_add_card_blue {V : Type} (G : SimpleGraph V) (t : Finset V) (v : V) (hv : v ∈ t) :
    {u ∈ t.erase v | G.Adj v u}.card + {u ∈ t.erase v | Gᶜ.Adj v u}.card = t.card - 1 := by
  have h : {u ∈ t.erase v | Gᶜ.Adj v u} = {u ∈ t.erase v | ¬ G.Adj v u} := by
    refine Finset.filter_congr ?_
    intro u hu
    have hne : v ≠ u := ((Finset.mem_erase.mp hu).1).symm
    simp [SimpleGraph.compl_adj, hne]
  rw [h, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]

/-- Both the red degree and the blue degree of any vertex are bounded, if there is no red
`(p+1)`-clique and no blue `(q+1)`-clique. -/
theorem degree_bounds {V : Type} {m n p q : ℕ} (hm : RamseyProp m p (q + 1))
    (hn : RamseyProp n (p + 1) q) (G : SimpleGraph V) (t : Finset V)
    (h1 : ¬ ∃ s ⊆ t, G.IsNClique (p + 1) s) (h2 : ¬ ∃ s ⊆ t, Gᶜ.IsNClique (q + 1) s)
    (v : V) (hv : v ∈ t) :
    {u ∈ t.erase v | G.Adj v u}.card < m ∧ {u ∈ t.erase v | Gᶜ.Adj v u}.card < n := by
  constructor
  · by_contra hA
    push_neg at hA
    rcases exists_clique_of_card_neighbors hm G t v hv _
      (fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1)
      (fun u hu => (Finset.mem_filter.mp hu).2) hA with h | h
    · exact h1 h
    · exact h2 h
  · by_contra hB
    push_neg at hB
    rcases exists_clique_of_card_neighbors (RamseyProp.symm hn) Gᶜ t v hv _
      (fun x hx => Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1)
      (fun u hu => (Finset.mem_filter.mp hu).2) hB with h | h
    · exact h2 h
    · rw [compl_compl] at h
      exact h1 h

/-- `R(p+1, q+1) ≤ R(p, q+1) + R(p+1, q)`. -/
theorem RamseyProp.step {m n p q : ℕ} (hm : RamseyProp m p (q + 1)) (hn : RamseyProp n (p + 1) q)
    (hpos : 0 < m + n) : RamseyProp (m + n) (p + 1) (q + 1) := by
  intro V G t ht
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨v, hv⟩ : t.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hpos ht)
  obtain ⟨hA, hB⟩ := degree_bounds hm hn G t h1 h2 v hv
  have hsum := card_red_add_card_blue G t v hv
  omega

/-- If `R(p, q+1) ≤ m` and `R(p+1, q) ≤ n` with `m`, `n` both even and positive, then
`R(p+1, q+1) ≤ m + n - 1`. -/
theorem RamseyProp.even_step {m n p q : ℕ} (hm : RamseyProp m p (q + 1))
    (hn : RamseyProp n (p + 1) q) (hme : Even m) (hne : Even n) (hm0 : 0 < m) (hn0 : 0 < n) :
    RamseyProp (m + n - 1) (p + 1) (q + 1) := by
  intro V G t ht
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨v0, hv0⟩ : t.Nonempty := Finset.card_pos.mp (by omega)
  have hcardt : t.card = m + n - 1 := by
    obtain ⟨hA, hB⟩ := degree_bounds hm hn G t h1 h2 v0 hv0
    have hsum := card_red_add_card_blue G t v0 hv0
    omega
  have key : ∀ v ∈ t, {u ∈ t.erase v | G.Adj v u}.card = m - 1 := by
    intro v hv
    obtain ⟨hA, hB⟩ := degree_bounds hm hn G t h1 h2 v hv
    have hsum := card_red_add_card_blue G t v hv
    omega
  have hsum : ∑ v ∈ t, {u ∈ t.erase v | G.Adj v u}.card = t.card * (m - 1) := by
    rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]
  have heven := even_sum_degrees G t
  rw [hsum, hcardt, Nat.even_mul] at heven
  have hm2 : m % 2 = 0 := Nat.even_iff.mp hme
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hne
  rcases heven with h | h <;> rw [Nat.even_iff] at h <;> omega

/-- `R(3,3) ≤ 6`. -/
theorem ramsey_3_3 : RamseyProp 6 3 3 :=
  RamseyProp.step (ramsey_two_left 3) (RamseyProp.symm (ramsey_two_left 3)) (by norm_num)

/-- `R(3,4) ≤ 9`. -/
theorem ramsey_3_4 : RamseyProp 9 3 4 :=
  RamseyProp.even_step (ramsey_two_left 4) ramsey_3_3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `R(4,4) ≤ 18`. -/
theorem ramsey_4_4_le : RamseyProp 18 4 4 :=
  RamseyProp.step ramsey_3_4 (RamseyProp.symm ramsey_3_4) (by norm_num)

end UpperBound

section LowerBound

/-- The nonzero quadratic residues modulo `17`. -/
def qr17 (n : Fin 17) : Bool :=
  n = 1 || n = 2 || n = 4 || n = 8 || n = 9 || n = 13 || n = 15 || n = 16

/-- The Paley graph on `17` vertices: `x` and `y` are adjacent iff `x - y` is a nonzero
quadratic residue modulo `17`. -/
def paley : SimpleGraph (Fin 17) where
  Adj x y := qr17 (x - y) = true
  symm := by
    have h : ∀ x y : Fin 17, qr17 (x - y) = true → qr17 (y - x) = true := by decide
    exact fun {x y} hxy => h x y hxy
  loopless := by
    have h : ∀ x : Fin 17, qr17 (x - x) = false := by decide
    refine ⟨fun x hx => ?_⟩
    rw [h x] at hx
    exact Bool.false_ne_true hx

instance : DecidableRel paley.Adj := fun x y => inferInstanceAs (Decidable (qr17 (x - y) = true))

/-- Exhaustive check: no four distinct vertices of the Paley graph on `17` vertices are
pairwise adjacent, nor pairwise non-adjacent. -/
theorem paley_check : ∀ a b c d : Fin 17, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬(qr17 (a - b) ∧ qr17 (a - c) ∧ qr17 (a - d) ∧ qr17 (b - c) ∧ qr17 (b - d) ∧ qr17 (c - d)) ∧
    ¬(qr17 (a - b) = false ∧ qr17 (a - c) = false ∧ qr17 (a - d) = false ∧
        qr17 (b - c) = false ∧ qr17 (b - d) = false ∧ qr17 (c - d) = false) := by
  decide

/-- Any `4`-element set is of the form `{a, b, c, d}` with the four elements distinct. -/
theorem card_eq_four {V : Type} [DecidableEq V] {s : Finset V} (hs : s.card = 4) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ s = {a, b, c, d} := by
  obtain ⟨a, s1, ha, rfl, hs1⟩ := Finset.card_eq_succ.mp hs
  obtain ⟨b, c, d, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_three.mp hs1
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, b, c, d, ha.1, ha.2.1, ha.2.2, hbc, hbd, hcd, rfl⟩

theorem paley_no_clique (s : Finset (Fin 17)) : ¬ paley.IsNClique 4 s := by
  intro h
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four h.2
  have hcl := h.1
  simp only [Finset.coe_insert, Finset.coe_singleton] at hcl
  refine (paley_check a b c d hab hac had hbc hbd hcd).1 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcl (by simp) (by simp) hab
  · exact hcl (by simp) (by simp) hac
  · exact hcl (by simp) (by simp) had
  · exact hcl (by simp) (by simp) hbc
  · exact hcl (by simp) (by simp) hbd
  · exact hcl (by simp) (by simp) hcd

theorem paley_compl_no_clique (s : Finset (Fin 17)) : ¬ paleyᶜ.IsNClique 4 s := by
  intro h
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := card_eq_four h.2
  have hcl := h.1
  simp only [Finset.coe_insert, Finset.coe_singleton] at hcl
  have hstep : ∀ x y : Fin 17, paleyᶜ.Adj x y → qr17 (x - y) = false := by
    intro x y hxy
    have := (SimpleGraph.compl_adj _ x y).mp hxy
    simpa [paley] using this.2
  refine (paley_check a b c d hab hac had hbc hbd hcd).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hstep _ _ (hcl (by simp) (by simp) hab)
  · exact hstep _ _ (hcl (by simp) (by simp) hac)
  · exact hstep _ _ (hcl (by simp) (by simp) had)
  · exact hstep _ _ (hcl (by simp) (by simp) hbc)
  · exact hstep _ _ (hcl (by simp) (by simp) hbd)
  · exact hstep _ _ (hcl (by simp) (by simp) hcd)

/-- Pulling a clique back along an injection. -/
theorem IsNClique.comap_image {V W : Type} [DecidableEq V] [DecidableEq W] {k : ℕ} (f : V ↪ W)
    (G : SimpleGraph W) {s : Finset V} (h : (SimpleGraph.comap f G).IsNClique k s) :
    G.IsNClique k (s.image f) := by
  constructor
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact h.1 (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) (fun hab => hxy (by rw [hab]))
  · rw [Finset.card_image_of_injective _ f.injective, h.2]

theorem comap_compl {V W : Type} (f : V ↪ W) (G : SimpleGraph W) :
    (SimpleGraph.comap f G)ᶜ = SimpleGraph.comap f Gᶜ := by
  ext x y
  simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj, f.injective.ne_iff]

end LowerBound

/-- The set of numbers `N` such that every red/blue colouring of the edges of the complete
graph on `N` vertices contains a monochromatic clique of size `4`. -/
def RamseySet : Set ℕ :=
  {N : ℕ | ∀ G : SimpleGraph (Fin N),
    (∃ s : Finset (Fin N), G.IsNClique 4 s) ∨ (∃ s : Finset (Fin N), Gᶜ.IsNClique 4 s)}

/-- **The Ramsey number `R(4,4)` equals `18`**: every two-colouring of the edges of the
complete graph on `18` vertices contains a monochromatic `K₄`, and `18` is the least such
number (the Paley graph on `17` vertices witnesses that `17` vertices are not enough). -/
theorem ramsey_4_4 : IsLeast RamseySet 18 := by
  constructor
  · intro G
    have h : (18 : ℕ) ≤ (Finset.univ : Finset (Fin 18)).card := by simp
    rcases ramsey_4_4_le G Finset.univ h with ⟨s, _, hs⟩ | ⟨s, _, hs⟩
    · exact Or.inl ⟨s, hs⟩
    · exact Or.inr ⟨s, hs⟩
  · intro N hN
    by_contra hlt
    push_neg at hlt
    have hle : N ≤ 17 := by omega
    classical
    let f : Fin N ↪ Fin 17 := ⟨fun i => Fin.castLE hle i, fun a b hab => by
      simpa [Fin.ext_iff] using hab⟩
    rcases hN (SimpleGraph.comap f paley) with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact paley_no_clique _ (IsNClique.comap_image f paley hs)
    · rw [comap_compl] at hs
      exact paley_compl_no_clique _ (IsNClique.comap_image f paleyᶜ hs)

end Math

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


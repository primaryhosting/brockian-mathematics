import Mathlib

/-!
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

/-- A comparison-based decision tree on `n` elements with results in `α`.
An internal node compares the elements at two positions and branches on the answer. -/
inductive DTree (n : ℕ) (α : Type u) where
  | leaf : α → DTree n α
  | node : Fin n → Fin n → DTree n α → DTree n α → DTree n α

namespace DTree

variable {n : ℕ} {α : Type u}

/-- Worst-case number of comparisons performed by the tree. -/
def depth : DTree n α → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- The list of results at the leaves, read left to right. -/
def outs : DTree n α → List α
  | leaf a => [a]
  | node _ _ l r => l.outs ++ r.outs

/-- Running the algorithm against a comparison oracle `o`. -/
def run : DTree n α → (Fin n → Fin n → Bool) → α
  | leaf a, _ => a
  | node i j l r, o => if o i j then l.run o else r.run o

theorem run_mem_outs (t : DTree n α) (o : Fin n → Fin n → Bool) : t.run o ∈ t.outs := by
  induction t with
  | leaf a => simp [run, outs]
  | node i j l r ihl ihr =>
      by_cases h : o i j <;> simp [run, outs, h, ihl, ihr]

/-- A tree of depth `d` has at most `2 ^ d` leaves. -/
theorem length_outs_le (t : DTree n α) : t.outs.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp [outs, depth]
  | node i j l r ihl ihr =>
      have hl : l.outs.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.outs.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [outs, depth, List.length_append, pow_succ]
      omega

/-- Relabel the results at the leaves. -/
def mapOut {β : Type u} (f : α → β) : DTree n α → DTree n β
  | leaf a => leaf (f a)
  | node i j l r => node i j (l.mapOut f) (r.mapOut f)

theorem run_mapOut {β : Type u} (f : α → β) (t : DTree n α) (o : Fin n → Fin n → Bool) :
    (t.mapOut f).run o = f (t.run o) := by
  induction t with
  | leaf a => rfl
  | node i j l r ihl ihr => by_cases h : o i j <;> simp [mapOut, run, h, ihl, ihr]

/-- The tree that simply performs, in order, all the comparisons in `ps`,
returning the list of answers. -/
def probe : List (Fin n × Fin n) → DTree n (List Bool)
  | [] => leaf []
  | p :: ps => node p.1 p.2 ((probe ps).mapOut (true :: ·)) ((probe ps).mapOut (false :: ·))

theorem run_probe (ps : List (Fin n × Fin n)) (o : Fin n → Fin n → Bool) :
    (probe ps).run o = ps.map (fun p => o p.1 p.2) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      by_cases h : o p.1 p.2 <;> simp [probe, run, run_mapOut, h, ih]

end DTree

/-- The comparison oracle induced by an ordering `σ` of the `n` input positions:
the answer to "is the element at position `i` at most the element at position `j`?". -/
def cmpOracle {n : ℕ} (σ : Equiv.Perm (Fin n)) : Fin n → Fin n → Bool :=
  fun i j => decide (σ i ≤ σ j)

/-- **Comparison-sort lower bound for 5 elements.**
If a comparison decision tree on 5 elements is correct, in the sense that its output
determines the input ordering (distinct orderings of the input yield distinct outputs),
then its worst-case number of comparisons is at least `⌈log₂ (5!)⌉ = 7`. -/
theorem sorting_lb_5 {α : Type u} (t : DTree 5 α)
    (h : Function.Injective fun σ : Equiv.Perm (Fin 5) => t.run (cmpOracle σ)) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  classical
  have hcard : (Nat.factorial 5) ≤ t.outs.toFinset.card := by
    have hle : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card ≤ t.outs.toFinset.card := by
      refine Finset.card_le_card_of_injOn (fun σ => t.run (cmpOracle σ)) ?_ (h.injOn)
      intro σ _
      simp [DTree.run_mem_outs]
    simpa [Nat.factorial] using hle
  have h2 : Nat.factorial 5 ≤ 2 ^ t.depth :=
    hcard.trans ((List.toFinset_card_le _).trans (t.length_outs_le))
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 h2

/-- A permutation of `Fin n` is determined by the ordering it induces on the positions. -/
theorem perm_eq_of_le_iff {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∀ i j, σ i ≤ σ j ↔ τ i ≤ τ j) : σ = τ := by
  have cardlt : ∀ a : Fin n, (Finset.univ.filter (fun m : Fin n => m < a)).card = a.val := by
    intro a
    rw [show (Finset.univ.filter (fun m : Fin n => m < a)) = Finset.Iio a by ext m; simp]
    exact Fin.card_Iio a
  have key : ∀ (ρ : Equiv.Perm (Fin n)) (i : Fin n),
      (Finset.univ.filter (fun k => ρ k < ρ i)).card = (ρ i).val := by
    intro ρ i
    have himg : (Finset.univ.filter (fun k => ρ k < ρ i))
        = (Finset.univ.filter (fun m : Fin n => m < ρ i)).image ρ.symm := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · exact fun hk => ⟨ρ k, hk, by simp⟩
      · rintro ⟨m, hm, rfl⟩; simpa using hm
    rw [himg, Finset.card_image_of_injective _ ρ.symm.injective, cardlt]
  ext i
  have hlt : ∀ k, σ k < σ i ↔ τ k < τ i := by
    intro k
    constructor <;> intro hk
    · exact lt_of_not_ge fun hc => absurd ((h i k).2 hc) (not_le.2 hk)
    · exact lt_of_not_ge fun hc => absurd ((h i k).1 hc) (not_le.2 hk)
  have h1 := key σ i
  rw [Finset.filter_congr (fun k _ => by simpa using hlt k), key τ i] at h1
  exact h1.symm

/-- The hypothesis of `sorting_lb_5` is satisfiable: the (wasteful) algorithm that performs
all 25 comparisons and returns the list of answers does determine the input ordering.
Hence the lower bound is not vacuous. -/
theorem exists_distinguishing_tree :
    ∃ t : DTree 5 (List Bool),
      Function.Injective fun σ : Equiv.Perm (Fin 5) => t.run (cmpOracle σ) := by
  refine ⟨DTree.probe ((List.finRange 5) ×ˢ (List.finRange 5)), ?_⟩
  intro σ τ hst
  simp only [DTree.run_probe, List.map_inj_left] at hst
  refine perm_eq_of_le_iff (fun i j => ?_)
  have := hst (i, j) (by simp)
  simpa [cmpOracle] using this

/-- The bound is literally `7` comparisons. -/
theorem sorting_lb_5' {α : Type u} (t : DTree 5 α)
    (h : Function.Injective fun σ : Equiv.Perm (Fin 5) => t.run (cmpOracle σ)) :
    7 ≤ t.depth := by
  have := sorting_lb_5 t h
  have hc : Nat.clog 2 (Nat.factorial 5) = 7 := by decide
  omega

end CS




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


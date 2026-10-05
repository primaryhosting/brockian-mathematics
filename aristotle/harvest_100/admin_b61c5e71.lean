import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/
theorem permanent_eq_card_perm {V : Type} [DecidableEq V] [Fintype V] (A : Matrix V V ℕ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, A i (σ i) = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h : ∀ i, A i (σ i) = 1
  · simp [h, Matrix.transpose_apply]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (by simpa using ⟨i, hi⟩)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases h01 i (σ i) with h0 | h1
    · simpa [Matrix.transpose_apply] using h0
    · exact absurd h1 hi

/-! ## Part B: Boolean circuits, `#P`, and membership of the permanent -/

/-- Boolean circuits (formulas) over a type of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | tru : Circuit ι
  | fls : Circuit ι
  | neg : Circuit ι → Circuit ι
  | conj : Circuit ι → Circuit ι → Circuit ι
  | disj : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Semantics of a circuit under an assignment of its variables. -/
def eval : Circuit ι → (ι → Bool) → Bool
  | var i, v => v i
  | tru, _ => true
  | fls, _ => false
  | neg c, v => !(c.eval v)
  | conj c d, v => (c.eval v) && (d.eval v)
  | disj c d, v => (c.eval v) || (d.eval v)

/-- The size (number of gates) of a circuit. -/
def size : Circuit ι → ℕ
  | var _ => 1
  | tru => 1
  | fls => 1
  | neg c => 1 + c.size
  | conj c d => 1 + c.size + d.size
  | disj c d => 1 + c.size + d.size

/-- Conjunction of a list of circuits. -/
def bigAnd : List (Circuit ι) → Circuit ι
  | [] => tru
  | c :: cs => conj c (bigAnd cs)

/-- Disjunction of a list of circuits. -/
def bigOr : List (Circuit ι) → Circuit ι
  | [] => fls
  | c :: cs => disj c (bigOr cs)

lemma eval_bigAnd (l : List (Circuit ι)) (v : ι → Bool) :
    (bigAnd l).eval v = true ↔ ∀ c ∈ l, c.eval v = true := by
  induction l with
  | nil => simp [bigAnd, eval]
  | cons c cs ih => simp [bigAnd, eval, ih]

lemma eval_bigOr (l : List (Circuit ι)) (v : ι → Bool) :
    (bigOr l).eval v = true ↔ ∃ c ∈ l, c.eval v = true := by
  induction l with
  | nil => simp [bigOr, eval]
  | cons c cs ih => simp [bigOr, eval, ih]

lemma size_bigAnd_le (l : List (Circuit ι)) (B : ℕ) (h : ∀ c ∈ l, c.size ≤ B) :
    (bigAnd l).size ≤ 1 + l.length * (1 + B) := by
  induction l with
  | nil => simp [bigAnd, size]
  | cons c cs ih =>
    have h1 : c.size ≤ B := h c (by simp)
    have h2 := ih (fun d hd => h d (by simp [hd]))
    have h3 : (cs.length + 1) * (1 + B) = cs.length * (1 + B) + (1 + B) := by ring
    simp only [bigAnd, size, List.length_cons]
    omega

lemma size_bigOr_le (l : List (Circuit ι)) (B : ℕ) (h : ∀ c ∈ l, c.size ≤ B) :
    (bigOr l).size ≤ 1 + l.length * (1 + B) := by
  induction l with
  | nil => simp [bigOr, size]
  | cons c cs ih =>
    have h1 : c.size ≤ B := h c (by simp)
    have h2 := ih (fun d hd => h d (by simp [hd]))
    have h3 : (cs.length + 1) * (1 + B) = cs.length * (1 + B) + (1 + B) := by ring
    simp only [bigOr, size, List.length_cons]
    omega

/-- "At least one of `f a` holds". -/
def atLeastOne (m : ℕ) (f : Fin m → Circuit ι) : Circuit ι := bigOr ((List.finRange m).map f)

/-- "At most one of `f a` holds". -/
def atMostOne (m : ℕ) (f : Fin m → Circuit ι) : Circuit ι :=
  bigAnd ((List.finRange m).flatMap fun a => (List.finRange m).map fun b =>
    if a = b then tru else neg (conj (f a) (f b)))

/-- "Exactly one of `f a` holds". -/
def exactlyOne (m : ℕ) (f : Fin m → Circuit ι) : Circuit ι :=
  conj (atLeastOne m f) (atMostOne m f)

lemma eval_atLeastOne (m : ℕ) (f : Fin m → Circuit ι) (v : ι → Bool) :
    (atLeastOne m f).eval v = true ↔ ∃ a, (f a).eval v = true := by
  rw [atLeastOne, eval_bigOr]
  simp

lemma eval_atMostOne (m : ℕ) (f : Fin m → Circuit ι) (v : ι → Bool) :
    (atMostOne m f).eval v = true ↔ ∀ a b, (f a).eval v = true → (f b).eval v = true → a = b := by
  rw [atMostOne, eval_bigAnd]
  constructor
  · intro h a b ha hb
    by_contra hab
    have := h (neg (conj (f a) (f b))) (by
      simp only [List.mem_flatMap]
      exact ⟨a, List.mem_finRange a, by
        simp only [List.mem_map]
        exact ⟨b, List.mem_finRange b, by rw [if_neg hab]⟩⟩)
    simp [eval, ha, hb] at this
  · intro h c hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨a, -, b, -, rfl⟩ := hc
    by_cases hab : a = b
    · simp [hab, eval]
    · simp only [if_neg hab, eval, Bool.not_eq_true', Bool.and_eq_false_iff]
      by_cases ha : (f a).eval v = true
      · by_cases hb : (f b).eval v = true
        · exact absurd (h a b ha hb) hab
        · simp [hb]
      · simp [ha]

lemma eval_exactlyOne (m : ℕ) (f : Fin m → Circuit ι) (v : ι → Bool) :
    (exactlyOne m f).eval v = true ↔ ∃! a, (f a).eval v = true := by
  rw [exactlyOne, eval, Bool.and_eq_true, eval_atLeastOne, eval_atMostOne]
  constructor
  · rintro ⟨⟨a, ha⟩, h2⟩
    exact ⟨a, ha, fun b hb => h2 b a hb ha⟩
  · rintro ⟨a, ha, h2⟩
    exact ⟨⟨a, ha⟩, fun b c hb hc => by rw [h2 b hb, h2 c hc]⟩

lemma size_atLeastOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (atLeastOne m f).size ≤ 1 + m * (1 + B) := by
  refine le_trans (size_bigOr_le _ B ?_) ?_
  · intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨a, -, rfl⟩ := hc
    exact hf a
  · simp

lemma size_atMostOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (atMostOne m f).size ≤ 1 + (m * m) * (3 + 2 * B) := by
  refine le_trans (size_bigAnd_le _ (2 + 2 * B) ?_) ?_
  · intro c hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨a, -, b, -, rfl⟩ := hc
    by_cases hab : a = b
    · simp only [if_pos hab, size]
      omega
    · have ha := hf a
      have hb := hf b
      simp only [if_neg hab, size]
      omega
  · have hlen : ((List.finRange m).flatMap fun a => (List.finRange m).map fun b =>
        if a = b then (tru : Circuit ι) else neg (conj (f a) (f b))).length = m * m := by
      simp [List.length_flatMap]
    have h4 : (1 : ℕ) + (2 + 2 * B) = 3 + 2 * B := by ring
    rw [hlen, h4]

lemma size_exactlyOne_le (m : ℕ) (f : Fin m → Circuit ι) (B : ℕ) (hf : ∀ a, (f a).size ≤ B) :
    (exactlyOne m f).size ≤ 3 + m * (1 + B) + (m * m) * (3 + 2 * B) := by
  have h1 := size_atLeastOne_le m f B hf
  have h2 := size_atMostOne_le m f B hf
  simp only [exactlyOne, size]
  omega

end Circuit

/-- A counting problem: for each size parameter `n` the instances are bit strings of length
`isize n`, and `count n x` is the number to be computed. -/
structure CountingProblem where
  isize : ℕ → ℕ
  count : (n : ℕ) → (Fin (isize n) → Bool) → ℕ

/-- Polynomial boundedness of a function `ℕ → ℕ`. -/
def IsPolyBounded (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

/-- Membership in `#P`: there is a polynomially bounded witness length and a polynomial-size
family of verifier circuits (given by an explicit construction) so that the value of the
counting problem is the number of accepted witnesses. -/
def CountingProblem.InSharpP (P : CountingProblem) : Prop :=
  ∃ (wlen : ℕ → ℕ) (C : ∀ n, Circuit (Fin (P.isize n) ⊕ Fin (wlen n))),
    IsPolyBounded wlen ∧ IsPolyBounded (fun n => (C n).size) ∧
      ∀ (n : ℕ) (x : Fin (P.isize n) → Bool),
        P.count n x = Nat.card {y : Fin (wlen n) → Bool // (C n).eval (Sum.elim x y) = true}

/-- The 0/1 matrix encoded by a bit string of length `n * n`. -/
def decodeMatrix (n : ℕ) (x : Fin (n * n) → Bool) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => if x (finProdFinEquiv (i, j)) then 1 else 0

/-- The `0/1`-permanent as a counting problem. -/
def permanentProblem : CountingProblem where
  isize n := n * n
  count n x := (decodeMatrix n x).permanent

/-- The matrix-entry variable `(i, j)` of the verifier. -/
def xvar (n : ℕ) (i j : Fin n) : Circuit (Fin (n * n) ⊕ Fin (n * n)) :=
  Circuit.var (Sum.inl (finProdFinEquiv (i, j)))

/-- The witness variable `(i, j)`: the `(i, j)` entry of the candidate permutation matrix. -/
def yvar (n : ℕ) (i j : Fin n) : Circuit (Fin (n * n) ⊕ Fin (n * n)) :=
  Circuit.var (Sum.inr (finProdFinEquiv (i, j)))

/-- The verifier circuit for the 0/1 permanent: the witness must be a permutation matrix whose
support is contained in the support of the input matrix. -/
def permVerifier (n : ℕ) : Circuit (Fin (n * n) ⊕ Fin (n * n)) :=
  Circuit.conj
    (Circuit.bigAnd ((List.finRange n).map fun i => Circuit.exactlyOne n (fun j => yvar n i j)))
    (Circuit.conj
      (Circuit.bigAnd ((List.finRange n).map fun j => Circuit.exactlyOne n (fun i => yvar n i j)))
      (Circuit.bigAnd ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
        Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j))))

lemma eval_permVerifier (n : ℕ) (x y : Fin (n * n) → Bool) :
    (permVerifier n).eval (Sum.elim x y) = true ↔
      ((∀ i : Fin n, ∃! j : Fin n, y (finProdFinEquiv (i, j)) = true) ∧
       (∀ j : Fin n, ∃! i : Fin n, y (finProdFinEquiv (i, j)) = true) ∧
       (∀ i j : Fin n, y (finProdFinEquiv (i, j)) = true →
          x (finProdFinEquiv (i, j)) = true)) := by
  have hy : ∀ i j : Fin n, (yvar n i j).eval (Sum.elim x y) = y (finProdFinEquiv (i, j)) := by
    intro i j; rfl
  have hx : ∀ i j : Fin n, (xvar n i j).eval (Sum.elim x y) = x (finProdFinEquiv (i, j)) := by
    intro i j; rfl
  rw [permVerifier, Circuit.eval, Bool.and_eq_true, Circuit.eval, Bool.and_eq_true,
    Circuit.eval_bigAnd, Circuit.eval_bigAnd, Circuit.eval_bigAnd]
  refine and_congr ?_ (and_congr ?_ ?_)
  · constructor
    · intro h i
      have := h _ (List.mem_map_of_mem (List.mem_finRange i))
      rw [Circuit.eval_exactlyOne] at this
      simpa only [hy] using this
    · intro h c hc
      simp only [List.mem_map] at hc
      obtain ⟨i, -, rfl⟩ := hc
      rw [Circuit.eval_exactlyOne]
      simpa only [hy] using h i
  · constructor
    · intro h j
      have := h _ (List.mem_map_of_mem (List.mem_finRange j))
      rw [Circuit.eval_exactlyOne] at this
      simpa only [hy] using this
    · intro h c hc
      simp only [List.mem_map] at hc
      obtain ⟨j, -, rfl⟩ := hc
      rw [Circuit.eval_exactlyOne]
      simpa only [hy] using h j
  · constructor
    · intro h i j hij
      have hmem : Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j) ∈
          ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
            Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j)) := by
        simp only [List.mem_flatMap, List.mem_map]
        exact ⟨i, List.mem_finRange i, j, List.mem_finRange j, rfl⟩
      have := h _ hmem
      simp only [Circuit.eval, hy, hx, hij, Bool.not_true, Bool.false_or] at this
      exact this
    · intro h c hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨i, -, j, -, rfl⟩ := hc
      simp only [Circuit.eval, hy, hx, Bool.or_eq_true, Bool.not_eq_true']
      by_cases hij : y (finProdFinEquiv (i, j)) = true
      · exact Or.inr (h i j hij)
      · exact Or.inl (by simpa using hij)

lemma size_permVerifier_le (n : ℕ) : (permVerifier n).size ≤ 32 * (n + 1) ^ 3 := by
  have hE : ∀ f : Fin n → Circuit (Fin (n * n) ⊕ Fin (n * n)), (∀ a, (f a).size = 1) →
      (Circuit.exactlyOne n f).size ≤ 3 + n * 2 + (n * n) * 5 := by
    intro f hf
    have h := Circuit.size_exactlyOne_le n f 1 (fun a => le_of_eq (hf a))
    norm_num at h ⊢
    omega
  have hrows : (Circuit.bigAnd ((List.finRange n).map fun i =>
      Circuit.exactlyOne n (fun j => yvar n i j))).size ≤
      1 + n * (1 + (3 + n * 2 + (n * n) * 5)) := by
    refine le_trans (Circuit.size_bigAnd_le _ (3 + n * 2 + (n * n) * 5) ?_) ?_
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨i, -, rfl⟩ := hc
      exact hE _ (fun _ => rfl)
    · simp
  have hcols : (Circuit.bigAnd ((List.finRange n).map fun j =>
      Circuit.exactlyOne n (fun i => yvar n i j))).size ≤
      1 + n * (1 + (3 + n * 2 + (n * n) * 5)) := by
    refine le_trans (Circuit.size_bigAnd_le _ (3 + n * 2 + (n * n) * 5) ?_) ?_
    · intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨j, -, rfl⟩ := hc
      exact hE _ (fun _ => rfl)
    · simp
  have hsupp : (Circuit.bigAnd ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
      Circuit.disj (Circuit.neg (yvar n i j)) (xvar n i j))).size ≤ 1 + (n * n) * 5 := by
    refine le_trans (Circuit.size_bigAnd_le _ 4 ?_) ?_
    · intro c hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨i, -, j, -, rfl⟩ := hc
      exact le_of_eq rfl
    · simp [List.length_flatMap]
  simp only [permVerifier, Circuit.size]
  nlinarith [hrows, hcols, hsupp, Nat.zero_le n]

/-- The witness (permutation matrix) associated with a permutation. -/
def permWitness (n : ℕ) (σ : Equiv.Perm (Fin n)) : Fin (n * n) → Bool :=
  fun idx => decide (σ (finProdFinEquiv.symm idx).1 = (finProdFinEquiv.symm idx).2)

lemma permWitness_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permWitness n σ (finProdFinEquiv (i, j)) = decide (σ i = j) := by
  simp [permWitness]

lemma card_witnesses (n : ℕ) (x : Fin (n * n) → Bool) :
    Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, x (finProdFinEquiv (i, σ i)) = true} =
      Nat.card {y : Fin (n * n) → Bool // (permVerifier n).eval (Sum.elim x y) = true} := by
  classical
  have hmem : ∀ σ : Equiv.Perm (Fin n), (∀ i, x (finProdFinEquiv (i, σ i)) = true) →
      (permVerifier n).eval (Sum.elim x (permWitness n σ)) = true := by
    intro σ h
    rw [eval_permVerifier]
    refine ⟨fun i => ⟨σ i, by simp [permWitness_apply], fun j hj => ?_⟩,
      fun j => ⟨σ.symm j, by simp [permWitness_apply], fun i hi => ?_⟩, fun i j hij => ?_⟩
    · simp only [permWitness_apply, decide_eq_true_eq] at hj
      exact hj.symm
    · simp only [permWitness_apply, decide_eq_true_eq] at hi
      rw [← hi, Equiv.symm_apply_apply]
    · simp only [permWitness_apply, decide_eq_true_eq] at hij
      rw [← hij]
      exact h i
  refine Nat.card_eq_of_bijective
    (fun p => ⟨permWitness n p.1, hmem p.1 p.2⟩) ⟨?_, ?_⟩
  · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hst
    have hw : permWitness n σ = permWitness n τ := congrArg Subtype.val hst
    refine Subtype.ext (Equiv.ext fun i => ?_)
    have h2 := congrFun hw (finProdFinEquiv (i, σ i))
    rw [permWitness_apply, permWitness_apply] at h2
    have h3 : τ i = σ i := by simpa using h2.symm
    exact h3.symm
  · rintro ⟨y, hy⟩
    rw [eval_permVerifier] at hy
    obtain ⟨hrows, hcols, hsupp⟩ := hy
    choose f hf hfu using hrows
    have hinj : Function.Injective f := by
      intro i i' hii
      obtain ⟨i0, -, hu⟩ := hcols (f i)
      rw [hu i (hf i), hu i' (by rw [hii]; exact hf i')]
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
    have hσ : ∀ i, σ i = f i := fun _ => rfl
    refine ⟨⟨σ, fun i => ?_⟩, ?_⟩
    · rw [hσ i]
      exact hsupp i (f i) (hf i)
    · refine Subtype.ext ?_
      funext idx
      obtain ⟨p, rfl⟩ := finProdFinEquiv.surjective idx
      obtain ⟨i, j⟩ := p
      show permWitness n σ (finProdFinEquiv (i, j)) = y (finProdFinEquiv (i, j))
      rw [permWitness_apply, hσ i]
      by_cases hj : j = f i
      · rw [hj]
        simpa using (hf i).symm
      · have hy0 : y (finProdFinEquiv (i, j)) = false := by
          by_contra hcon
          exact hj (hfu i j (by simpa using hcon))
        rw [hy0, decide_eq_false]
        exact fun h => hj h.symm

/-- **The 0/1 permanent lies in `#P`.** -/
theorem permanent_inSharpP : permanentProblem.InSharpP := by
  refine ⟨fun n => n * n, fun n => permVerifier n, ⟨1, 2, fun n => ?_⟩, ⟨32, 3, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg n]
  · exact fun n => size_permVerifier_le n
  · intro n x
    show (decodeMatrix n x).permanent = _
    rw [permanent_eq_card_perm (decodeMatrix n x) (fun i j => by
      simp only [decodeMatrix, Matrix.of_apply]
      split <;> simp)]
    rw [← card_witnesses n x]
    congr 1
    apply congrArg
    funext σ
    simp only [decodeMatrix, Matrix.of_apply, eq_iff_iff]
    constructor
    · intro h i
      have := h i
      split at this
      · assumption
      · simp at this
    · intro h i
      rw [if_pos (h i)]

/-! ## Part C: eliminating weights, i.e. `0/1` permanents simulate `ℕ`-weighted permanents -/

/-- The permanent is invariant under simultaneous reindexing of rows and columns. -/
theorem permanent_submatrix_equiv_self {α β R : Type} [DecidableEq α] [Fintype α] [DecidableEq β]
    [Fintype β] [CommSemiring R] (e : α ≃ β) (M : Matrix β β R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_bijective (Equiv.permCongr e) (Equiv.permCongr e).bijective _ _ ?_
  intro σ
  rw [← Equiv.prod_comp e (fun j => M ((Equiv.permCongr e σ) j) j)]
  exact Finset.prod_congr rfl fun i _ => by simp [Equiv.permCongr_apply, Matrix.submatrix_apply]

section Gadget

variable {n : ℕ}

/-- The vertices added for the weights: `A i j` parallel copies of the cell `(i, j)`. -/
abbrev Cells (A : Matrix (Fin n) (Fin n) ℕ) := (p : Fin n × Fin n) × Fin (A p.1 p.2)

/-- Vertices of the 0/1 gadget graph: the original ones plus one per cell copy. -/
abbrev Vert (A : Matrix (Fin n) (Fin n) ℕ) := Fin n ⊕ Cells A

/-- The 0/1 matrix simulating the weights of `A`: each vertex `i` points to every copy of a
cell in row `i`, every copy of a cell in column `j` points to `j`, and each cell copy carries a
self-loop. -/
def gadget (A : Matrix (Fin n) (Fin n) ℕ) : Matrix (Vert A) (Vert A) ℕ := Matrix.of fun v w =>
  match v, w with
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl i, Sum.inr c => if c.1.1 = i then 1 else 0
  | Sum.inr c, Sum.inl j => if c.1.2 = j then 1 else 0
  | Sum.inr c, Sum.inr c' => if c = c' then 1 else 0

lemma gadget_zeroOne (A : Matrix (Fin n) (Fin n) ℕ) (v w : Vert A) :
    gadget A v w = 0 ∨ gadget A v w = 1 := by
  cases v <;> cases w <;> simp [gadget] <;> tauto

variable (A : Matrix (Fin n) (Fin n) ℕ)

@[simp] lemma gadget_inl_inl (i j : Fin n) : gadget A (Sum.inl i) (Sum.inl j) = 0 := rfl

@[simp] lemma gadget_inl_inr (i : Fin n) (c : Cells A) :
    gadget A (Sum.inl i) (Sum.inr c) = if c.1.1 = i then 1 else 0 := rfl

@[simp] lemma gadget_inr_inl (c : Cells A) (j : Fin n) :
    gadget A (Sum.inr c) (Sum.inl j) = if c.1.2 = j then 1 else 0 := rfl

@[simp] lemma gadget_inr_inr (c c' : Cells A) :
    gadget A (Sum.inr c) (Sum.inr c') = if c = c' then 1 else 0 := rfl

/-- The cell copy selected in row `i` by the data `(π, k)`. -/
def cellOf (π : Equiv.Perm (Fin n)) (k : ∀ i, Fin (A i (π i))) (i : Fin n) : Cells A :=
  ⟨(i, π i), k i⟩

variable (π : Equiv.Perm (Fin n)) (k : ∀ i, Fin (A i (π i)))

lemma snd_of_used {c : Cells A} (h : c = cellOf A π k c.1.1) : c.1.2 = π c.1.1 :=
  congrArg (fun d : Cells A => d.1.2) h

/-- The cycle cover of the gadget graph determined by a permutation `π` together with a choice
`k` of a cell copy in each row. -/
def toPermV : Equiv.Perm (Vert A) where
  toFun := fun v => match v with
    | Sum.inl i => Sum.inr (cellOf A π k i)
    | Sum.inr c => if c = cellOf A π k c.1.1 then Sum.inl c.1.2 else Sum.inr c
  invFun := fun v => match v with
    | Sum.inl j => Sum.inr (cellOf A π k (π.symm j))
    | Sum.inr c => if c = cellOf A π k c.1.1 then Sum.inl c.1.1 else Sum.inr c
  left_inv := by
    rintro (i | c)
    · show (if cellOf A π k i = cellOf A π k (cellOf A π k i).1.1 then
          (Sum.inl (cellOf A π k i).1.1 : Vert A) else Sum.inr (cellOf A π k i)) = Sum.inl i
      rw [show (cellOf A π k i).1.1 = i from rfl, if_pos rfl]
    · by_cases h : c = cellOf A π k c.1.1
      · have h2 : c.1.2 = π c.1.1 := snd_of_used A π k h
        show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) with
          | Sum.inl j => (Sum.inr (cellOf A π k (π.symm j)) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.1 else Sum.inr d) = Sum.inr c
        rw [if_pos h]
        simp only [h2, Equiv.symm_apply_apply]
        exact congrArg Sum.inr h.symm
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) with
          | Sum.inl j => (Sum.inr (cellOf A π k (π.symm j)) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.1 else Sum.inr d) = Sum.inr c
        rw [if_neg h]
        show (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) = Sum.inr c
        rw [if_neg h]
  right_inv := by
    rintro (j | c)
    · show (if cellOf A π k (π.symm j) = cellOf A π k (cellOf A π k (π.symm j)).1.1 then
          (Sum.inl (cellOf A π k (π.symm j)).1.2 : Vert A)
          else Sum.inr (cellOf A π k (π.symm j))) = Sum.inl j
      rw [show (cellOf A π k (π.symm j)).1.1 = π.symm j from rfl, if_pos rfl,
        show (cellOf A π k (π.symm j)).1.2 = π (π.symm j) from rfl]
      simp
    · by_cases h : c = cellOf A π k c.1.1
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) with
          | Sum.inl i => (Sum.inr (cellOf A π k i) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.2 else Sum.inr d) = Sum.inr c
        rw [if_pos h]
        exact congrArg Sum.inr h.symm
      · show (match (if c = cellOf A π k c.1.1 then (Sum.inl c.1.1 : Vert A) else Sum.inr c) with
          | Sum.inl i => (Sum.inr (cellOf A π k i) : Vert A)
          | Sum.inr d => if d = cellOf A π k d.1.1 then Sum.inl d.1.2 else Sum.inr d) = Sum.inr c
        rw [if_neg h]
        show (if c = cellOf A π k c.1.1 then (Sum.inl c.1.2 : Vert A) else Sum.inr c) = Sum.inr c
        rw [if_neg h]

lemma toPermV_inl (i : Fin n) : toPermV A π k (Sum.inl i) = Sum.inr (cellOf A π k i) := rfl

lemma toPermV_inr (c : Cells A) :
    toPermV A π k (Sum.inr c) =
      if c = cellOf A π k c.1.1 then Sum.inl c.1.2 else Sum.inr c := rfl

/-- Cycle covers of the gadget graph coming from `(π, k)` indeed have all weights `1`. -/
lemma toPermV_valid (v : Vert A) : gadget A v (toPermV A π k v) = 1 := by
  rcases v with i | c
  · rw [toPermV_inl]
    show (if (cellOf A π k i).1.1 = i then 1 else 0) = 1
    rw [show (cellOf A π k i).1.1 = i from rfl, if_pos rfl]
  · rw [toPermV_inr]
    by_cases h : c = cellOf A π k c.1.1
    · rw [if_pos h]
      show (if c.1.2 = c.1.2 then 1 else 0) = 1
      rw [if_pos rfl]
    · rw [if_neg h]
      show (if c = c then 1 else 0) = 1
      rw [if_pos rfl]

lemma toPermV_injective :
    Function.Injective
      (fun p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))) => toPermV A p.1 p.2) := by
  rintro ⟨π₁, k₁⟩ ⟨π₂, k₂⟩ h
  simp only at h
  have hcell : ∀ i, cellOf A π₁ k₁ i = cellOf A π₂ k₂ i := by
    intro i
    have h1 := (Equiv.ext_iff.mp h) (Sum.inl i)
    rw [toPermV_inl, toPermV_inl] at h1
    exact Sum.inr.inj h1
  have hπ : π₁ = π₂ :=
    Equiv.ext fun i => congrArg (fun c : Cells A => c.1.2) (hcell i)
  subst hπ
  have hk : k₁ = k₂ := by
    funext i
    have := hcell i
    simpa [cellOf, Sigma.mk.injEq] using this
  simp [hk]

lemma toPermV_surjective (σ : Equiv.Perm (Vert A)) (hσ : ∀ v, gadget A v (σ v) = 1) :
    ∃ p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))), toPermV A p.1 p.2 = σ := by
  classical
  have hrow : ∀ i : Fin n, ∃ c : Cells A, σ (Sum.inl i) = Sum.inr c ∧ c.1.1 = i := by
    intro i
    have h := hσ (Sum.inl i)
    rcases hi : σ (Sum.inl i) with j | c
    · rw [hi] at h; simp at h
    · refine ⟨c, rfl, ?_⟩
      rw [hi, gadget_inl_inr] at h
      by_contra hne
      rw [if_neg hne] at h
      exact absurd h (by norm_num)
  choose cf hcf1 hcf2 using hrow
  have hused : ∀ i, σ (Sum.inr (cf i)) = Sum.inl (cf i).1.2 := by
    intro i
    have h := hσ (Sum.inr (cf i))
    rcases hi : σ (Sum.inr (cf i)) with j | c
    · rw [hi, gadget_inr_inl] at h
      by_cases hj : (cf i).1.2 = j
      · exact congrArg Sum.inl hj.symm
      · rw [if_neg hj] at h; exact absurd h (by norm_num)
    · rw [hi, gadget_inr_inr] at h
      by_cases hc : cf i = c
      · exfalso
        have heq : σ (Sum.inl i) = σ (Sum.inr (cf i)) := by rw [hcf1, hi, hc]
        simpa using σ.injective heq
      · rw [if_neg hc] at h; exact absurd h (by norm_num)
  have hinj : Function.Injective (fun i => (cf i).1.2) := by
    intro i i' hii
    have heq : σ (Sum.inr (cf i)) = σ (Sum.inr (cf i')) := by
      rw [hused, hused]; exact congrArg Sum.inl hii
    have h3 : cf i = cf i' := Sum.inr.inj (σ.injective heq)
    rw [← hcf2 i, ← hcf2 i', h3]
  let π' : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun i => (cf i).1.2) (Finite.injective_iff_bijective.mp hinj)
  have hπ' : ∀ i, π' i = (cf i).1.2 := fun _ => rfl
  have hA : ∀ i, A (cf i).1.1 (cf i).1.2 = A i (π' i) := by
    intro i; rw [hcf2 i, hπ' i]
  refine ⟨⟨π', fun i => Fin.cast (hA i) (cf i).2⟩, ?_⟩
  have hcell : ∀ i, cellOf A π' (fun i => Fin.cast (hA i) (cf i).2) i = cf i := by
    intro i
    refine Sigma.ext ?_ ?_
    · show (i, π' i) = (cf i).1
      rw [hπ' i]
      exact Prod.ext (hcf2 i).symm rfl
    · exact (Fin.heq_ext_iff (hA i).symm).mpr rfl
  refine Equiv.ext ?_
  rintro (i | c)
  · rw [toPermV_inl, hcell i, hcf1 i]
  · rw [toPermV_inr]
    by_cases h : c = cellOf A π' (fun i => Fin.cast (hA i) (cf i).2) c.1.1
    · rw [if_pos h]
      rw [hcell] at h
      conv_rhs => rw [h]
      rw [hused]
      exact congrArg Sum.inl (congrArg (fun d : Cells A => d.1.2) h)
    · rw [if_neg h]
      rw [hcell] at h
      have h1 := hσ (Sum.inr c)
      rcases hi : σ (Sum.inr c) with j | c'
      · exfalso
        rw [hi, gadget_inr_inl] at h1
        by_cases hj : c.1.2 = j
        · have hex : ∃ i, (cf i).1.2 = c.1.2 := ⟨π'.symm c.1.2, by
            rw [← hπ' (π'.symm c.1.2), Equiv.apply_symm_apply]⟩
          obtain ⟨i, hi2⟩ := hex
          have : σ (Sum.inr (cf i)) = σ (Sum.inr c) := by
            rw [hused, hi, hi2, hj]
          have hcfc : cf i = c := Sum.inr.inj (σ.injective this)
          apply h
          rw [← hcfc, hcf2 i]
        · rw [if_neg hj] at h1; exact absurd h1 (by norm_num)
      · rw [hi, gadget_inr_inr] at h1
        by_cases hc : c = c'
        · exact congrArg Sum.inr hc
        · rw [if_neg hc] at h1; exact absurd h1 (by norm_num)

lemma card_sigma_eq_permanent :
    Fintype.card ((π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i)))) = A.permanent := by
  rw [Fintype.card_sigma, ← Matrix.permanent_transpose]
  unfold Matrix.permanent
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => Fintype.card_fin _

/-- The permanent of the 0/1 gadget matrix equals the weighted permanent of `A`. -/
lemma gadget_permanent : (gadget A).permanent = A.permanent := by
  classical
  have hbij : Function.Bijective
      (fun p : (π : Equiv.Perm (Fin n)) × (∀ i, Fin (A i (π i))) =>
        (⟨toPermV A p.1 p.2, toPermV_valid A p.1 p.2⟩ :
          {σ : Equiv.Perm (Vert A) // ∀ v, gadget A v (σ v) = 1})) := by
    constructor
    · intro p q hpq
      exact toPermV_injective A (congrArg Subtype.val hpq)
    · rintro ⟨σ, hσ⟩
      obtain ⟨p, hp⟩ := toPermV_surjective A σ hσ
      exact ⟨p, Subtype.ext hp⟩
  rw [permanent_eq_card_perm (gadget A) (gadget_zeroOne A), ← Nat.card_eq_of_bijective _ hbij,
    Nat.card_eq_fintype_card, card_sigma_eq_permanent]

lemma card_Vert : Fintype.card (Vert A) = n + ∑ i, ∑ j, A i j := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  congr 1
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Fintype.card_fin _

end Gadget

/-- **Weight elimination.** The permanent of an arbitrary matrix of natural-number weights is
the permanent of a 0/1 matrix of size `n + ∑ i j, A i j`.  The 0/1 matrix is built by replacing
the weight `A i j` by `A i j` parallel two-step routes from `i` to `j`, each unused route being
covered by a self-loop; the size is therefore polynomial in `n` and the total weight, i.e.
polynomial in the input size when the weights are written in unary. -/
theorem exists_zeroOne_permanent_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
      N = n + ∑ i, ∑ j, A i j ∧ (∀ i j, B i j = 0 ∨ B i j = 1) ∧
        B.permanent = A.permanent := by
  classical
  let e : Fin (Fintype.card (Vert A)) ≃ Vert A := (Fintype.equivFin (Vert A)).symm
  refine ⟨Fintype.card (Vert A), (gadget A).submatrix e e, card_Vert A, fun i j => ?_, ?_⟩
  · exact gadget_zeroOne A (e i) (e j)
  · rw [permanent_submatrix_equiv_self e (gadget A), gadget_permanent]

/-! ## The main theorem

Scope of what is formalized below.  The statement `CS.valiant_permanent` collects the parts of
Valiant's theorem on the 0/1 permanent that are proved here in full:

* membership of the 0/1 permanent in `#P` (Part B), with respect to the witness-counting
  definition `CS.CountingProblem.InSharpP`, whose verifiers are Boolean circuits of
  polynomial size given by the explicit construction `CS.permVerifier`; the definition does not
  impose a separate uniformity condition on the circuit family, but the family used here is
  produced by an explicit uniform construction;
* the weight-elimination step (Part C), which shows that 0/1 permanents simulate arbitrary
  `ℕ`-weighted permanents;
* the identification of the 0/1 permanent with a count of perfect matchings / cycle covers
  (Part A), which is what makes it a counting problem in the first place.

The remaining ingredient of Valiant's theorem, namely the `#P`-hardness reduction from `#SAT`
to the permanent (variable, clause and XOR gadgets, followed by modular interpolation), is not
formalized here; no statement below assumes it.
-/

/-- **Valiant's permanent theorem (formalized core).**

The three conjuncts are:

* the 0/1 permanent is a counting problem in `#P`, witnessed by an explicitly constructed
  family of polynomial-size verifier circuits whose accepted witnesses are exactly the
  permutations supported on the matrix;
* every `ℕ`-weighted permanent is the permanent of a 0/1 matrix of controlled size
  (the weight-elimination step of Valiant's construction), so the 0/1 permanent is at least
  as hard as the weighted permanent;
* for 0/1 matrices the permanent is exactly the number of perfect matchings of the associated
  bipartite graph (equivalently, of cycle covers of the associated digraph). -/
theorem valiant_permanent :
    permanentProblem.InSharpP ∧
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ),
      ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
        N = n + ∑ i, ∑ j, A i j ∧ (∀ i j, B i j = 0 ∨ B i j = 1) ∧
          B.permanent = A.permanent) ∧
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ), (∀ i j, A i j = 0 ∨ A i j = 1) →
      A.permanent = Nat.card {σ : Equiv.Perm (Fin n) // ∀ i, A i (σ i) = 1}) :=
  ⟨permanent_inSharpP, fun _ A => exists_zeroOne_permanent_eq A,
    fun _ A h => permanent_eq_card_perm A h⟩

end CS


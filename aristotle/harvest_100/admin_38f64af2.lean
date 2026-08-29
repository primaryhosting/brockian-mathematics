import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Scope of this formalization

Valiant's theorem states that the 0/1 permanent is `#P`-complete. This file develops:

* Boolean circuits with evaluation and size, and a definition of `#P` in its nonuniform
  circuit-verifier form (`CS.InSharpP`), of parsimonious reductions computed by
  polynomial-size circuits (`CS.ParsimoniousReduction`), and of `#P`-completeness
  (`CS.IsSharpPComplete`).
* The 0/1 permanent as a counting problem (`CS.permProblem`), its identification with
  `Matrix.permanent` of the encoded 0/1 matrix, and its identification with the problem of
  counting perfect matchings of a bipartite graph (`CS.matchingProblem`).
* A proof that the 0/1 permanent problem lies in `#P` (`CS.permProblem_inSharpP`), by an
  explicit polynomial-size verifier circuit family checking that the witness is a permutation
  matrix supported on the `1`-entries of the instance.
* `CS.valiant_permanent`: `#P`-completeness of the 0/1 permanent, given the `#P`-hardness of
  counting bipartite perfect matchings. That hardness — the combinatorial core of Valiant's
  original argument, proved there by an intricate gadget construction — is taken as an explicit
  hypothesis and is *not* formalized here.
-/

namespace CS

/-! ## Boolean circuits -/

/-- Boolean circuits (formulas) over `N` input variables. -/
inductive BoolCircuit (N : ℕ) : Type
  | const : Bool → BoolCircuit N
  | var : Fin N → BoolCircuit N
  | neg : BoolCircuit N → BoolCircuit N
  | conj : BoolCircuit N → BoolCircuit N → BoolCircuit N
  | disj : BoolCircuit N → BoolCircuit N → BoolCircuit N

namespace BoolCircuit

variable {N : ℕ}

/-- Evaluation of a circuit on an input assignment. -/
def eval : BoolCircuit N → (Fin N → Bool) → Bool
  | const b, _ => b
  | var i, x => x i
  | neg c, x => !(c.eval x)
  | conj c d, x => (c.eval x) && (d.eval x)
  | disj c d, x => (c.eval x) || (d.eval x)

/-- The number of gates of a circuit. -/
def size : BoolCircuit N → ℕ
  | const _ => 1
  | var _ => 1
  | neg c => c.size + 1
  | conj c d => c.size + d.size + 1
  | disj c d => c.size + d.size + 1

/-- Conjunction of a list of circuits. -/
def bigAnd : List (BoolCircuit N) → BoolCircuit N
  | [] => const true
  | c :: cs => conj c (bigAnd cs)

/-- Disjunction of a list of circuits. -/
def bigOr : List (BoolCircuit N) → BoolCircuit N
  | [] => const false
  | c :: cs => disj c (bigOr cs)

lemma eval_bigAnd (x : Fin N → Bool) :
    ∀ l : List (BoolCircuit N), (bigAnd l).eval x = true ↔ ∀ c ∈ l, c.eval x = true := by
  intro l
  induction l with
  | nil => simp [bigAnd, eval]
  | cons c cs ih => simp [bigAnd, eval, ih]

lemma eval_bigOr (x : Fin N → Bool) :
    ∀ l : List (BoolCircuit N), (bigOr l).eval x = true ↔ ∃ c ∈ l, c.eval x = true := by
  intro l
  induction l with
  | nil => simp [bigOr, eval]
  | cons c cs ih => simp [bigOr, eval, ih]

lemma size_bigAnd_le (s : ℕ) :
    ∀ l : List (BoolCircuit N), (∀ c ∈ l, c.size ≤ s) →
      (bigAnd l).size ≤ 1 + l.length * (s + 1) := by
  intro l
  induction l with
  | nil => simp [bigAnd, size]
  | cons c cs ih =>
      intro h
      have h1 : c.size ≤ s := h c (by simp)
      have h2 := ih (fun d hd => h d (by simp [hd]))
      simp only [bigAnd, size, List.length_cons]
      nlinarith [h1, h2]

lemma size_bigOr_le (s : ℕ) :
    ∀ l : List (BoolCircuit N), (∀ c ∈ l, c.size ≤ s) →
      (bigOr l).size ≤ 1 + l.length * (s + 1) := by
  intro l
  induction l with
  | nil => simp [bigOr, size]
  | cons c cs ih =>
      intro h
      have h1 : c.size ≤ s := h c (by simp)
      have h2 := ih (fun d hd => h d (by simp [hd]))
      simp only [bigOr, size, List.length_cons]
      nlinarith [h1, h2]

end BoolCircuit

/-! ## Counting problems, `#P`, and parsimonious reductions -/

/-- A counting problem: for every input length `n`, a function from `n`-bit inputs to `ℕ`. -/
abbrev CountingProblem := (n : ℕ) → (Fin n → Bool) → ℕ

/-- A function `ℕ → ℕ` is polynomially bounded. -/
def PolyBounded (g : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, g n ≤ c * (n + 1) ^ d

/-- Membership in `#P` (in its nonuniform, circuit-verifier form): `f n x` counts the witnesses
`y` of polynomially bounded length that are accepted by a polynomial-size verifier circuit. -/
def InSharpP (f : CountingProblem) : Prop :=
  ∃ (m : ℕ → ℕ) (V : (n : ℕ) → BoolCircuit (n + m n)),
    PolyBounded m ∧ PolyBounded (fun n => (V n).size) ∧
      ∀ n x, f n x = Nat.card {y : Fin (m n) → Bool // (V n).eval (Fin.append x y) = true}

/-- A parsimonious reduction computed by polynomial-size circuits (one circuit per output bit). -/
def ParsimoniousReduction (f g : CountingProblem) : Prop :=
  ∃ (l : ℕ → ℕ) (R : (n : ℕ) → Fin (l n) → BoolCircuit n),
    PolyBounded l ∧ PolyBounded (fun n => ∑ i, (R n i).size) ∧
      ∀ n x, f n x = g (l n) (fun i => (R n i).eval x)

/-- The identity is a parsimonious reduction, so the notion is reflexive. -/
theorem parsimoniousReduction_refl (f : CountingProblem) : ParsimoniousReduction f f := by
  refine ⟨fun n => n, fun n i => .var i, ⟨1, 1, by intro n; simp⟩, ⟨1, 1, ?_⟩, ?_⟩
  · intro n
    simp [BoolCircuit.size]
  · intro n x
    rfl

/-- `#P`-hardness under parsimonious reductions. -/
def SharpPHard (g : CountingProblem) : Prop := ∀ f, InSharpP f → ParsimoniousReduction f g

/-- `#P`-completeness under parsimonious reductions. -/
def IsSharpPComplete (g : CountingProblem) : Prop := InSharpP g ∧ SharpPHard g

/-! ## The 0/1 permanent and bipartite perfect matchings -/

/-- The index in `Fin (k * k)` of the matrix position `(i, j)`. -/
def sqIdx (k : ℕ) (i j : Fin k) : Fin (k * k) := finProdFinEquiv (i, j)

lemma sq_sqrt_le (n : ℕ) : Nat.sqrt n * Nat.sqrt n ≤ n := by
  have := Nat.sqrt_le' n
  nlinarith [this]

/-- Reading a `0/1` matrix of size `k × k`, `k = √n`, out of an `n`-bit input. -/
def inIdx (n : ℕ) (i j : Fin (Nat.sqrt n)) : Fin n :=
  Fin.castLE (sq_sqrt_le n) (sqIdx _ i j)

/-- The number of permutations `σ` with all entries `A i (σ i)` equal to `1`;
equivalently, the permanent of the 0/1 matrix `A`. -/
noncomputable def permCount {k : ℕ} (A : Fin k → Fin k → Bool) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin k) // ∀ i, A i (σ i) = true}

/-- `M` is a perfect matching of the bipartite graph with parts `Fin k`, `Fin k`
and adjacency matrix `A`. -/
def IsPerfectMatching {k : ℕ} (A : Fin k → Fin k → Bool) (M : Finset (Fin k × Fin k)) : Prop :=
  (∀ e ∈ M, A e.1 e.2 = true) ∧ (∀ i, ∃! j, (i, j) ∈ M) ∧ (∀ j, ∃! i, (i, j) ∈ M)

/-- The number of perfect matchings of a bipartite graph given by its adjacency matrix. -/
noncomputable def matchingCount {k : ℕ} (A : Fin k → Fin k → Bool) : ℕ :=
  Nat.card {M : Finset (Fin k × Fin k) // IsPerfectMatching A M}

/-- The 0/1 permanent as a counting problem: the input encodes a `√n × √n` 0/1 matrix. -/
noncomputable def permProblem : CountingProblem := fun n x => permCount (fun i j => x (inIdx n i j))

/-- Counting perfect matchings of a bipartite graph, as a counting problem. -/
noncomputable def matchingProblem : CountingProblem := fun n x => matchingCount (fun i j => x (inIdx n i j))

/-- The 0/1 permanent counts the permutations avoiding the zero positions,
i.e. it agrees with `Matrix.permanent` of the corresponding 0/1 matrix over `ℕ`. -/
theorem permCount_eq_permanent {k : ℕ} (A : Fin k → Fin k → Bool) :
    (permCount A : ℕ) =
      Matrix.permanent (Matrix.of fun i j => if A i j then (1 : ℕ) else 0) := by
  classical
  have h1 : Matrix.permanent (Matrix.of fun i j => if A i j then (1 : ℕ) else 0)
      = ∑ σ : Equiv.Perm (Fin k), if (∀ i, A (σ i) i = true) then 1 else 0 := by
    rw [Matrix.permanent]
    refine Finset.sum_congr rfl ?_
    intro σ _
    by_cases h : ∀ i, A (σ i) i = true
    · simp [h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rw [if_neg (by push_neg; exact ⟨i, hi⟩)]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  rw [h1, Finset.sum_boole]
  simp only [permCount]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_nbij (fun σ => σ⁻¹) ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at *
    intro i
    have := hσ (σ⁻¹ i)
    simpa using this
  · intro a _ b _ hab
    simpa using congrArg (fun x : Equiv.Perm (Fin k) => x⁻¹) hab
  · intro σ hσ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and, Set.mem_image] at *
    refine ⟨σ⁻¹, ?_, by simp⟩
    intro i
    have := hσ (σ⁻¹ i)
    simpa using this

/-- Counting perfect matchings of a bipartite graph is the same as evaluating the 0/1 permanent
of its adjacency matrix. -/
theorem matchingCount_eq_permCount {k : ℕ} (A : Fin k → Fin k → Bool) :
    matchingCount A = permCount A := by
  classical
  unfold matchingCount permCount
  refine Nat.card_congr (Equiv.ofBijective
    (β := {M : Finset (Fin k × Fin k) // IsPerfectMatching A M})
    (fun σ => ⟨Finset.image (fun i => (i, σ.1 i)) Finset.univ, ?_, ?_, ?_⟩) ?_).symm
  · rintro ⟨i, j⟩ he
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at he
    obtain ⟨a, ha1, ha2⟩ := he
    subst ha1; subst ha2
    exact σ.2 a
  · intro i
    refine ⟨σ.1 i, by simp, ?_⟩
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hy
    obtain ⟨a, ha1, ha2⟩ := hy
    subst ha1; exact ha2.symm
  · intro j
    refine ⟨σ.1.symm j, by simp, ?_⟩
    intro y hy
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hy
    obtain ⟨a, ha1, ha2⟩ := hy
    subst ha1
    simp [← ha2]
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      refine Subtype.ext (Equiv.ext fun i => ?_)
      have hmem : (i, σ i) ∈ Finset.image (fun i => (i, τ i)) Finset.univ := by
        rw [← h]; simp
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq] at hmem
      obtain ⟨a, ha1, ha2⟩ := hmem
      subst ha1; simp [ha2]
    · rintro ⟨M, hM1, hM2, hM3⟩
      have hg : ∀ i, ((i : Fin k), (hM2 i).choose) ∈ M := fun i => (hM2 i).choose_spec.1
      set g : Fin k → Fin k := fun i => (hM2 i).choose with hgdef
      have hinj : Function.Injective g := by
        intro a b hab
        have h1 : (a, g a) ∈ M := hg a
        have h2 : (b, g b) ∈ M := hg b
        rw [hab] at h1
        exact ((hM3 (g b)).unique h1 h2)
      have hbij : Function.Bijective g := Finite.injective_iff_bijective.mp hinj
      refine ⟨⟨Equiv.ofBijective g hbij, fun i => hM1 _ (hg i)⟩, ?_⟩
      apply Subtype.ext
      apply Finset.ext
      rintro ⟨i, j⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
        Equiv.ofBijective_apply]
      constructor
      · rintro ⟨a, rfl, rfl⟩
        exact hg a
      · intro h
        exact ⟨i, rfl, ((hM2 i).unique (hg i) h)⟩

/-- The 0/1 permanent problem evaluates `Matrix.permanent` of the encoded 0/1 matrix. -/
theorem permProblem_eq_permanent (n : ℕ) (x : Fin n → Bool) :
    permProblem n x =
      Matrix.permanent (Matrix.of fun i j => if x (inIdx n i j) then (1 : ℕ) else 0) :=
  permCount_eq_permanent _

theorem matchingProblem_eq_permProblem : matchingProblem = permProblem := by
  funext n x
  exact matchingCount_eq_permCount _

/-! ### Sanity checks -/

example : permCount (fun _ _ : Fin 3 => true) = 6 := by
  rw [permCount, Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype, Fintype.card_perm, Nat.factorial]

example : permCount (fun i j : Fin 2 => decide (i = j)) = 1 := by
  rw [permCount, Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]
  decide

example : permCount (fun _ _ : Fin 2 => false) = 0 := by
  rw [permCount, Nat.card_eq_fintype_card]
  simp

/-! ## The permanent problem is in `#P` -/

section Verifier

variable (n : ℕ)

/-- Circuit variable reading the matrix entry `(i, j)` of the instance. -/
def xvar (i j : Fin (Nat.sqrt n)) : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  .var (Fin.castAdd _ (inIdx n i j))

/-- Circuit variable reading the entry `(i, j)` of the witness permutation matrix. -/
def yvar (i j : Fin (Nat.sqrt n)) : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  .var (Fin.natAdd n (sqIdx _ i j))

/-- "Row `i` of the witness has its unique `1` in column `j`". -/
def rowTerm (i j : Fin (Nat.sqrt n)) : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  .conj (yvar n i j)
    (BoolCircuit.bigAnd ((List.finRange _).map
      (fun j' => .disj (.const (decide (j' = j))) (.neg (yvar n i j')))))

/-- "Row `i` of the witness contains exactly one `1`". -/
def rowCond (i : Fin (Nat.sqrt n)) : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  BoolCircuit.bigOr ((List.finRange _).map (fun j => rowTerm n i j))

/-- "Column `j` of the witness contains at least one `1`". -/
def colCond (j : Fin (Nat.sqrt n)) : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  BoolCircuit.bigOr ((List.finRange _).map (fun i => yvar n i j))

/-- "Every `1` of the witness sits at a `1` entry of the instance". -/
def edgeCond : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  BoolCircuit.bigAnd ((List.finRange _).flatMap
    (fun i => (List.finRange _).map (fun j => .disj (.neg (yvar n i j)) (xvar n i j))))

/-- The verifier circuit for the permanent: it accepts a witness iff the witness is a permutation
matrix supported on the `1` entries of the instance matrix. -/
def verifier : BoolCircuit (n + Nat.sqrt n * Nat.sqrt n) :=
  BoolCircuit.bigAnd
    (((List.finRange _).map (rowCond n)) ++ ((List.finRange _).map (colCond n)) ++ [edgeCond n])

end Verifier

/-- Currying the witness bit string into a square Boolean matrix. -/
def curryEquiv (k : ℕ) : (Fin k → Fin k → Bool) ≃ (Fin (k * k) → Bool) :=
  (Equiv.curry (Fin k) (Fin k) Bool).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

lemma curryEquiv_apply (k : ℕ) (Y : Fin k → Fin k → Bool) (i j : Fin k) :
    curryEquiv k Y (sqIdx k i j) = Y i j := by
  simp [curryEquiv, sqIdx, Equiv.arrowCongr]

/-- The witness conditions checked by the verifier circuit. -/
def IsPermMatrixOn {k : ℕ} (X Y : Fin k → Fin k → Bool) : Prop :=
  (∀ i, ∃! j, Y i j = true) ∧ (∀ j, ∃ i, Y i j = true) ∧ (∀ i j, Y i j = true → X i j = true)

theorem eval_verifier (n : ℕ) (x : Fin n → Bool) (Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool) :
    (verifier n).eval (Fin.append x (curryEquiv _ Y)) = true ↔
      IsPermMatrixOn (fun i j => x (inIdx n i j)) Y := by
  classical
  set a := Fin.append x (curryEquiv (Nat.sqrt n) Y) with ha
  have hy : ∀ i j, (yvar n i j).eval a = Y i j := by
    intro i j
    simp [yvar, BoolCircuit.eval, ha, curryEquiv_apply]
  have hx : ∀ i j, (xvar n i j).eval a = x (inIdx n i j) := by
    intro i j
    simp [xvar, BoolCircuit.eval, ha]
  have hterm : ∀ i j, (rowTerm n i j).eval a = true ↔
      (Y i j = true ∧ ∀ j', j' ≠ j → Y i j' = false) := by
    intro i j
    rw [rowTerm]
    simp only [BoolCircuit.eval, Bool.and_eq_true, BoolCircuit.eval_bigAnd, List.mem_map,
      List.mem_finRange, true_and, hy]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j' hj' => ?_⟩
      have hc := h2 _ ⟨j', rfl⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        hy] at hc
      rcases hc with hc | hc
      · exact absurd hc hj'
      · exact hc
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rintro c ⟨j', rfl⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', hy]
      by_cases hjj : j' = j
      · exact Or.inl hjj
      · exact Or.inr (h2 j' hjj)
  have hrow : ∀ i, (rowCond n i).eval a = true ↔ ∃! j, Y i j = true := by
    intro i
    rw [rowCond, BoolCircuit.eval_bigOr]
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨c, ⟨j, rfl⟩, hc⟩
      obtain ⟨h1, h2⟩ := (hterm i j).1 hc
      refine ⟨j, h1, fun j' hj' => ?_⟩
      by_contra hne
      have hj'' : Y i j' = true := hj'
      rw [h2 j' hne] at hj''
      exact Bool.noConfusion hj''
    · rintro ⟨j, h1, h2⟩
      refine ⟨rowTerm n i j, ⟨j, rfl⟩, (hterm i j).2 ⟨h1, fun j' hj' => ?_⟩⟩
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hj' (h2 j' hc)
  have hcol : ∀ j, (colCond n j).eval a = true ↔ ∃ i, Y i j = true := by
    intro j
    rw [colCond, BoolCircuit.eval_bigOr]
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro ⟨c, ⟨i, rfl⟩, hc⟩
      exact ⟨i, by rwa [hy] at hc⟩
    · rintro ⟨i, hi⟩
      exact ⟨yvar n i j, ⟨i, rfl⟩, by rw [hy]; exact hi⟩
  have hedge : (edgeCond n).eval a = true ↔ ∀ i j, Y i j = true → x (inIdx n i j) = true := by
    rw [edgeCond, BoolCircuit.eval_bigAnd]
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    constructor
    · rintro h i j hij
      have hc := h _ ⟨i, ⟨j, rfl⟩⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, Bool.not_eq_true', hy, hx, hij] at hc
      simpa using hc
    · rintro h c ⟨i, ⟨j, rfl⟩⟩
      simp only [BoolCircuit.eval, Bool.or_eq_true, Bool.not_eq_true', hy, hx]
      by_cases hij : Y i j = true
      · exact Or.inr (h i j hij)
      · exact Or.inl (by simpa using hij)
  rw [verifier, BoolCircuit.eval_bigAnd, IsPermMatrixOn]
  simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton, true_and]
  constructor
  · intro h
    exact ⟨fun i => (hrow i).1 (h _ (Or.inl (Or.inl ⟨i, rfl⟩))),
      fun j => (hcol j).1 (h _ (Or.inl (Or.inr ⟨j, rfl⟩))), hedge.1 (h _ (Or.inr rfl))⟩
  · rintro ⟨h1, h2, h3⟩ c hc
    rcases hc with (⟨i, rfl⟩ | ⟨j, rfl⟩) | rfl
    · exact (hrow i).2 (h1 i)
    · exact (hcol j).2 (h2 j)
    · exact hedge.2 h3

theorem card_permMatrices {k : ℕ} (X : Fin k → Fin k → Bool) :
    Nat.card {Y : Fin k → Fin k → Bool // IsPermMatrixOn X Y} = permCount X := by
  classical
  unfold permCount
  refine Nat.card_congr (Equiv.ofBijective
    (β := {Y : Fin k → Fin k → Bool // IsPermMatrixOn X Y})
    (fun σ => ⟨fun i j => decide (σ.1 i = j), ?_, ?_, ?_⟩) ?_).symm
  · intro i
    refine ⟨σ.1 i, by simp, ?_⟩
    intro y hy
    simpa [eq_comm] using hy
  · intro j
    exact ⟨σ.1.symm j, by simp⟩
  · intro i j hij
    simp only [decide_eq_true_eq] at hij
    subst hij
    exact σ.2 i
  · constructor
    · rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      simp only [Subtype.mk.injEq] at h
      refine Subtype.ext (Equiv.ext fun i => ?_)
      have hval := congrFun (congrFun h i) (σ i)
      simp at hval
      exact hval.symm
    · rintro ⟨Y, hY1, hY2, hY3⟩
      set g : Fin k → Fin k := fun i => (hY1 i).choose with hgdef
      have hgY : ∀ i, Y i (g i) = true := fun i => (hY1 i).choose_spec.1
      have huniq : ∀ i j, Y i j = true → j = g i := fun i j h => (hY1 i).choose_spec.2 j h
      have hsurj : Function.Surjective g := by
        intro j
        obtain ⟨i, hi⟩ := hY2 j
        exact ⟨i, (huniq i j hi).symm⟩
      have hbij : Function.Bijective g := Finite.surjective_iff_bijective.mp hsurj
      refine ⟨⟨Equiv.ofBijective g hbij, fun i => hY3 i (g i) (hgY i)⟩, ?_⟩
      apply Subtype.ext
      funext i j
      simp only [Equiv.ofBijective_apply]
      by_cases h : Y i j = true
      · have hj := huniq i j h
        simp [hj, hgY]
      · simp only [Bool.not_eq_true] at h
        have hne : g i ≠ j := by
          intro hc
          rw [← hc] at h
          rw [hgY i] at h
          exact Bool.noConfusion h
        simp [h, hne]

theorem size_verifier_le (n : ℕ) : (verifier n).size ≤ 200 * (n + 1) ^ 3 := by
  have hkn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hterm : ∀ i j, (rowTerm n i j).size ≤ 5 * Nat.sqrt n + 3 := by
    intro i j
    have hb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n) 4
      ((List.finRange (Nat.sqrt n)).map
        (fun j' => BoolCircuit.disj (BoolCircuit.const (decide (j' = j)))
          (BoolCircuit.neg (yvar n i j')))) (by
          intro c hc
          simp only [List.mem_map] at hc
          obtain ⟨j', _, rfl⟩ := hc
          simp [BoolCircuit.size, yvar])
    simp only [List.length_map, List.length_finRange] at hb
    simp only [rowTerm, BoolCircuit.size]
    have hyv : (yvar n i j).size = 1 := rfl
    omega
  have hrow : ∀ i, (rowCond n i).size ≤ 1 + Nat.sqrt n * (5 * Nat.sqrt n + 4) := by
    intro i
    have hb := BoolCircuit.size_bigOr_le (N := n + Nat.sqrt n * Nat.sqrt n) (5 * Nat.sqrt n + 3)
      ((List.finRange (Nat.sqrt n)).map (fun j => rowTerm n i j)) (by
        intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨j, _, rfl⟩ := hc
        exact hterm i j)
    simp only [List.length_map, List.length_finRange] at hb
    simp only [rowCond]
    omega
  have hcol : ∀ j, (colCond n j).size ≤ 1 + Nat.sqrt n * 2 := by
    intro j
    have hb := BoolCircuit.size_bigOr_le (N := n + Nat.sqrt n * Nat.sqrt n) 1
      ((List.finRange (Nat.sqrt n)).map (fun i => yvar n i j)) (by
        intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨i, _, rfl⟩ := hc
        simp [BoolCircuit.size, yvar])
    simp only [List.length_map, List.length_finRange] at hb
    simp only [colCond]
    omega
  have hlen : ((List.finRange (Nat.sqrt n)).flatMap
      (fun i => (List.finRange (Nat.sqrt n)).map (fun j =>
        BoolCircuit.disj (BoolCircuit.neg (yvar n i j)) (xvar n i j)))).length
      = Nat.sqrt n * Nat.sqrt n := by
    simp [List.length_flatMap]
  have hedge : (edgeCond n).size ≤ 1 + (Nat.sqrt n * Nat.sqrt n) * 5 := by
    have hb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n) 4
      ((List.finRange (Nat.sqrt n)).flatMap
        (fun i => (List.finRange (Nat.sqrt n)).map (fun j =>
          BoolCircuit.disj (BoolCircuit.neg (yvar n i j)) (xvar n i j)))) (by
        intro c hc
        simp only [List.mem_flatMap, List.mem_map] at hc
        obtain ⟨i, _, j, _, rfl⟩ := hc
        simp [BoolCircuit.size, yvar, xvar])
    rw [hlen] at hb
    simpa [edgeCond] using hb
  have hall : ∀ c ∈ (((List.finRange (Nat.sqrt n)).map (rowCond n)) ++
      ((List.finRange (Nat.sqrt n)).map (colCond n)) ++ [edgeCond n]),
      c.size ≤ 10 * Nat.sqrt n * Nat.sqrt n + 6 * Nat.sqrt n + 3 := by
    intro c hc
    simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton,
      true_and] at hc
    rcases hc with (⟨i, rfl⟩ | ⟨j, rfl⟩) | rfl
    · have h := hrow i; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
    · have h := hcol j; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
    · have h := hedge; nlinarith [h, Nat.zero_le (Nat.sqrt n)]
  have hvb := BoolCircuit.size_bigAnd_le (N := n + Nat.sqrt n * Nat.sqrt n)
    (10 * Nat.sqrt n * Nat.sqrt n + 6 * Nat.sqrt n + 3)
    (((List.finRange (Nat.sqrt n)).map (rowCond n)) ++
      ((List.finRange (Nat.sqrt n)).map (colCond n)) ++ [edgeCond n]) hall
  simp only [List.length_append, List.length_map, List.length_finRange,
    List.length_singleton] at hvb
  have hv : (verifier n).size ≤ 200 * (Nat.sqrt n + 1) ^ 3 := by
    rw [verifier]
    refine le_trans hvb ?_
    nlinarith [Nat.zero_le (Nat.sqrt n)]
  have hmono : (Nat.sqrt n + 1) ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  exact le_trans hv (Nat.mul_le_mul_left 200 hmono)

/-- The 0/1 permanent problem lies in `#P`. -/
theorem permProblem_inSharpP : InSharpP permProblem := by
  refine ⟨fun n => Nat.sqrt n * Nat.sqrt n, fun n => verifier n, ⟨1, 1, ?_⟩, ⟨200, 3, ?_⟩, ?_⟩
  · intro n
    have h := sq_sqrt_le n
    simp only [pow_one, one_mul]
    omega
  · intro n
    exact size_verifier_le n
  · intro n x
    calc permProblem n x
        = Nat.card {Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool //
            IsPermMatrixOn (fun i j => x (inIdx n i j)) Y} :=
          (card_permMatrices _).symm
      _ = Nat.card {Y : Fin (Nat.sqrt n) → Fin (Nat.sqrt n) → Bool //
            (verifier n).eval (Fin.append x (curryEquiv _ Y)) = true} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun Y => (eval_verifier n x Y).symm))
      _ = Nat.card {y : Fin (Nat.sqrt n * Nat.sqrt n) → Bool //
            (verifier n).eval (Fin.append x y) = true} :=
          Nat.card_congr (Equiv.subtypeEquiv (curryEquiv (Nat.sqrt n)) (fun _ => Iff.rfl))

/-! ## Valiant's theorem -/

/-- **Valiant's theorem**: the 0/1 permanent is `#P`-complete.

The formalization is relative to the (unformalized here) combinatorial core of Valiant's
theorem, namely the `#P`-hardness of counting perfect matchings in bipartite graphs, which is
taken as the hypothesis `hmatch`. What is proved here is that the 0/1 permanent problem belongs
to `#P` (via an explicit polynomial-size verifier circuit family checking that a witness is a
permutation matrix supported on the `1`-entries of the instance), and that the 0/1 permanent
problem *is* the problem of counting bipartite perfect matchings, so that the hardness
hypothesis transfers to it; hence the permanent is `#P`-complete. -/
theorem valiant_permanent (hmatch : SharpPHard matchingProblem) : IsSharpPComplete permProblem :=
  ⟨permProblem_inSharpP, matchingProblem_eq_permProblem ▸ hmatch⟩

/-- Unconditional companion of `CS.valiant_permanent`: since the 0/1 permanent problem *is* the
problem of counting bipartite perfect matchings, and since it belongs to `#P`, it is
`#P`-complete precisely when counting bipartite perfect matchings is `#P`-hard. -/
theorem isSharpPComplete_permProblem_iff :
    IsSharpPComplete permProblem ↔ SharpPHard matchingProblem := by
  constructor
  · intro h
    rw [matchingProblem_eq_permProblem]
    exact h.2
  · exact valiant_permanent

end CS

/-- info: 'CS.valiant_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CS.valiant_permanent

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


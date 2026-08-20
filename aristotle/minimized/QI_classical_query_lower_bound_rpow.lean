import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

set_option grind.warning false

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

theorem classical_query_lower_bound_rpow {n q : ℕ} (A : QueryAlg n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) :
    (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (q : ℝ) + 2 := by
  have h := classical_query_lower_bound A hA
  have h' : ((2:ℝ)) ^ (n : ℕ) ≤ ((q : ℝ) + 2) ^ 2 := by exact_mod_cast h
  have ha : (0:ℝ) ≤ (2:ℝ) ^ ((n : ℝ) / 2) := by positivity
  have hb : (0:ℝ) ≤ (q : ℝ) + 2 := by positivity
  have hsq : ((2:ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2:ℝ) ^ (n : ℕ) := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0), Real.rpow_natCast]
  nlinarith [h', ha, hb, hsq]

/-- **Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries.**

1. *(quantum, one query per round)* For every instance `f` with hidden shift `s`:
   * a single query produces a measurement outcome that is uniformly distributed
     on the hyperplane orthogonal to `s`;
   * the outcomes of `2 * n` independent rounds form a probability distribution,
     and the probability that they fail to determine `s` is at most `2 ^ (-n)`;
     so `2 * n = O(n)` queries suffice.
2. *(classical)* Every deterministic classical algorithm which always outputs the
   hidden shift using `q` queries satisfies `2 ^ (n / 2) ≤ q + 2`, i.e. it needs
   `Ω(2 ^ (n / 2))` queries. -/

def IsSimon {n : ℕ} (f : BV n → BV n) (s : BV n) : Prop :=
  s ≠ 0 ∧ ∀ x y, f x = f y ↔ (y = x ∨ y = x + s)

section
variable {n : ℕ}

lemma card_bv (n : ℕ) : Fintype.card (BV n) = 2 ^ n := by
  simp [BV]

lemma zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma zmod_two_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

@[simp] lemma bv_add_self (x : BV n) : x + x = 0 := by
  funext i
  simpa using zmod_two_add_self (x i)

def e {n : ℕ} (i : Fin n) : BV n := fun j => if j = i then 1 else 0

lemma exists_ne_zero_coord {x : BV n} (hx : x ≠ 0) : ∃ i, x i = 1 := by
  by_contra h
  push_neg at h
  apply hx
  funext i
  rcases zmod_two_cases (x i) with h0 | h1
  · simpa using h0
  · exact absurd h1 (h i)

/-- If `s ≠ 0` there is a vector pairing to `1` with `s`. -/

def trace (A : QueryAlg n) (f : BV n → BV n) : ℕ → List (BV n)
  | 0 => []
  | k + 1 => trace A f k ++ [f (A.next (trace A f k))]

/-- The `k`-th query point of `A` when run on `f`. -/

def query (A : QueryAlg n) (f : BV n → BV n) (k : ℕ) : BV n := A.next (trace A f k)

/-- The output of `A` after `q` queries to `f`. -/

def result (A : QueryAlg n) (f : BV n → BV n) (q : ℕ) : BV n := A.out (trace A f q)

lemma trace_succ (A : QueryAlg n) (f : BV n → BV n) (k : ℕ) :
    trace A f (k + 1) = trace A f k ++ [f (query A f k)] := rfl

/-- Two oracles agreeing on all the query points that the algorithm asks of `f`
produce the same transcript. -/

lemma trace_congr (A : QueryAlg n) (f g : BV n → BV n) :
    ∀ k : ℕ, (∀ j < k, g (query A f j) = f (query A f j)) → trace A g k = trace A f k
  | 0, _ => rfl
  | k + 1, h => by
      have ih : trace A g k = trace A f k :=
        trace_congr A f g k fun j hj => h j (Nat.lt_succ_of_lt hj)
      have hq : query A g k = query A f k := by
        simp only [query, ih]
      rw [trace_succ, trace_succ, ih, hq, h k (Nat.lt_succ_self k)]

/-! ### Constructing Simon functions with prescribed values -/

/-- Canonical representative of the coset `{x, x + s}`, chosen using a
coordinate `i` where `s i = 1`. -/

def repOf (s : BV n) (i : Fin n) (x : BV n) : BV n := if x i = 0 then x else x + s

lemma repOf_cases (s : BV n) (i : Fin n) (x : BV n) :
    repOf s i x = x ∨ repOf s i x = x + s := by
  unfold repOf; split <;> simp

lemma repOf_add_s {s : BV n} {i : Fin n} (hs : s i = 1) (x : BV n) :
    repOf s i (x + s) = repOf s i x := by
  have hx : (x + s) i = x i + 1 := by simp [hs]
  simp only [repOf]
  rcases zmod_two_cases (x i) with h | h
  · have h1 : (x + s) i ≠ 0 := by rw [hx, h, zero_add]; decide
    rw [if_neg h1, if_pos h, add_assoc, bv_add_self, add_zero]
  · have h0 : (x + s) i = 0 := by rw [hx, h]; decide
    have h1 : ¬ (x i = 0) := by rw [h]; decide
    rw [if_pos h0, if_neg h1]

lemma repOf_eq_iff {s : BV n} {i : Fin n} (hs : s i = 1) (x y : BV n) :
    repOf s i x = repOf s i y ↔ (y = x ∨ y = x + s) := by
  constructor
  · intro h
    rcases repOf_cases s i x with hx | hx <;> rcases repOf_cases s i y with hy | hy
    · have hxy : x = y := by rw [← hx, ← hy]; exact h
      exact Or.inl hxy.symm
    · have hxy : x = y + s := by rw [← hx, ← hy]; exact h
      exact Or.inr (by rw [hxy, add_assoc, bv_add_self, add_zero])
    · have hxy : x + s = y := by rw [← hx, ← hy]; exact h
      exact Or.inr hxy.symm
    · have hxy : x + s = y + s := by rw [← hx, ← hy]; exact h
      exact Or.inl (add_right_cancel hxy).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (repOf_add_s hs x).symm

/-- **Extension lemma.**  If `s ≠ 0` and no two points of a finite set `X`
differ by `s`, then there is a function satisfying Simon's promise with hidden
shift `s` which is the identity on `X`. -/

lemma exists_isSimon_id_on {s : BV n} (hs : s ≠ 0) (X : Finset (BV n))
    (hX : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s) :
    ∃ f : BV n → BV n, IsSimon f s ∧ ∀ x ∈ X, f x = x := by
  classical
  obtain ⟨i, hi⟩ := exists_ne_zero_coord hs
  set r : BV n → BV n := repOf s i with hr
  -- `r` is injective on `X`
  have hinj : ∀ x ∈ X, ∀ y ∈ X, r x = r y → x = y := by
    intro x hx y hy hxy
    rcases (repOf_eq_iff hi x y).1 hxy with h | h
    · exact h.symm
    · exact absurd (by rw [h, ← add_assoc, bv_add_self, zero_add] : x + y = s) (hX x hx y hy)
  set R : Finset (BV n) := X.image r with hR
  have hmap : ∀ a : {a : BV n // a ∈ X}, r a.1 ∈ R := fun a =>
    Finset.mem_image_of_mem r a.2
  let g : {a : BV n // a ∈ X} → {b : BV n // b ∈ R} := fun a => ⟨r a.1, hmap a⟩
  have hgbij : Function.Bijective g := by
    constructor
    · intro a b hab
      exact Subtype.ext (hinj a.1 a.2 b.1 b.2 (congrArg Subtype.val hab))
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hb
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : {a : BV n // a ∈ X} ≃ {b : BV n // b ∈ R} := Equiv.ofBijective g hgbij
  let L : Equiv.Perm (BV n) := e.symm.extendSubtype
  refine ⟨fun z => L (r z), ⟨hs, ?_⟩, ?_⟩
  · intro x y
    constructor
    · intro h
      exact (repOf_eq_iff hi x y).1 (L.injective h)
    · intro h
      exact congrArg L ((repOf_eq_iff hi x y).2 h)
  · intro x hx
    have hmem : r x ∈ R := Finset.mem_image_of_mem r hx
    show L (r x) = x
    rw [show L (r x) = (e.symm ⟨r x, hmem⟩ : BV n) from
      Equiv.extendSubtype_apply_of_mem e.symm (r x) hmem]
    have : e ⟨x, hx⟩ = ⟨r x, hmem⟩ := rfl
    rw [← this, Equiv.symm_apply_apply]

/-- Simon instances exist for every nonzero hidden shift, so the promise is not
vacuous. -/

theorem classical_lower_bound {n q : ℕ} (A : QueryAlg n) (hq : q * q + 3 ≤ 2 ^ n) :
    ∃ (f : BV n → BV n) (s : BV n), IsSimon f s ∧ result A f q ≠ s := by
  classical
  -- the (at most `q`) points queried when the oracle is the identity
  set X : Finset (BV n) := (Finset.range q).image (fun k => query A id k) with hXdef
  have hXcard : X.card ≤ q := le_trans (Finset.card_image_le) (by simp)
  -- the forbidden shifts
  set D : Finset (BV n) := ((X ×ˢ X).image (fun p => p.1 + p.2)) ∪ {0} with hDdef
  have hDcard : D.card ≤ q * q + 1 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 : ((X ×ˢ X).image (fun p => p.1 + p.2)).card ≤ q * q := by
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hXcard hXcard
    simpa using Nat.add_le_add h1 (le_of_eq (Finset.card_singleton 0))
  -- there are at least two admissible shifts
  have hcompl : 1 < (Finset.univ \ D).card := by
    have hcard : (Finset.univ \ D).card = 2 ^ n - D.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_bv]
    have hD : D.card ≤ 2 ^ n := le_trans hDcard (by omega)
    omega
  obtain ⟨s, hsD, t, htD, hst⟩ := Finset.one_lt_card.1 hcompl
  have hmem : ∀ u ∈ Finset.univ \ D, u ≠ 0 ∧ ∀ x ∈ X, ∀ y ∈ X, x + y ≠ u := by
    intro u hu
    have hu' : u ∉ D := (Finset.mem_sdiff.1 hu).2
    constructor
    · intro h0
      exact hu' (by rw [h0, hDdef]; exact Finset.mem_union_right _ (Finset.mem_singleton_self 0))
    · intro x hx y hy hxy
      refine hu' ?_
      rw [hDdef]
      refine Finset.mem_union_left _ ?_
      exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, hxy⟩
  obtain ⟨hs0, hsX⟩ := hmem s hsD
  obtain ⟨ht0, htX⟩ := hmem t htD
  obtain ⟨f, hf, hfid⟩ := exists_isSimon_id_on hs0 X hsX
  obtain ⟨g, hg, hgid⟩ := exists_isSimon_id_on ht0 X htX
  -- both oracles agree with the identity on all queried points
  have key : ∀ (h : BV n → BV n), (∀ x ∈ X, h x = x) → result A h q = result A id q := by
    intro h hid
    have : trace A h q = trace A id q := by
      refine trace_congr A id h q ?_
      intro j hj
      have hmemj : query A id j ∈ X := by
        rw [hXdef]
        exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
      simpa using hid _ hmemj
    simp [result, this]
  have hfr : result A f q = result A id q := key f hfid
  have hgr : result A g q = result A id q := key g hgid
  by_cases hres : result A id q = s
  · exact ⟨g, t, hg, by rw [hgr, hres]; exact hst⟩
  · exact ⟨f, s, hf, by rw [hfr]; exact hres⟩

/-- **`Ω(2 ^ (n / 2))` classical queries are necessary.**  A deterministic
algorithm that always outputs the hidden shift after `q` queries must satisfy
`2 ^ n ≤ (q + 2) ^ 2`. -/

theorem classical_query_lower_bound {n q : ℕ} (A : QueryAlg n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → result A f q = s) :
    2 ^ n ≤ (q + 2) ^ 2 := by
  by_contra h
  push_neg at h
  have hq : q * q + 3 ≤ 2 ^ n := by nlinarith [h]
  obtain ⟨f, s, hfs, hne⟩ := classical_lower_bound A hq
  exact hne (hA f s hfs)

end QI

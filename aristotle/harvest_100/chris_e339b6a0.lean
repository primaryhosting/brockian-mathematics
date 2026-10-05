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
# Boolean circuits (formulas) and block-structured witness counting

This file sets up the elementary infrastructure used in the formalization of Toda's
theorem: a datatype of boolean formulas over variables indexed by `ℕ`, variable
substitution, big conjunctions/disjunctions, assignments extended by "blocks" of
witness bits, and counting of satisfying blocks.
-/

open scoped BigOperators

namespace CS

/-- Boolean formulas over variables indexed by `ℕ`. -/
inductive Circ where
  | fls : Circ
  | tru : Circ
  | var : ℕ → Circ
  | neg : Circ → Circ
  | conj : Circ → Circ → Circ
  | disj : Circ → Circ → Circ
  | xorC : Circ → Circ → Circ
  deriving Inhabited

namespace Circ

/-- Value of a formula under an assignment. -/
def eval : Circ → (ℕ → Bool) → Bool
  | fls, _ => false
  | tru, _ => true
  | var i, α => α i
  | neg c, α => !(c.eval α)
  | conj c d, α => (c.eval α) && (d.eval α)
  | disj c d, α => (c.eval α) || (d.eval α)
  | xorC c d, α => Bool.xor (c.eval α) (d.eval α)

@[simp] lemma eval_fls (α) : eval fls α = false := rfl
@[simp] lemma eval_tru (α) : eval tru α = true := rfl
@[simp] lemma eval_var (i α) : eval (var i) α = α i := rfl
@[simp] lemma eval_neg (c α) : eval (neg c) α = !(c.eval α) := rfl
@[simp] lemma eval_conj (c d α) : eval (conj c d) α = ((c.eval α) && (d.eval α)) := rfl
@[simp] lemma eval_disj (c d α) : eval (disj c d) α = ((c.eval α) || (d.eval α)) := rfl
@[simp] lemma eval_xorC (c d α) : eval (xorC c d) α = Bool.xor (c.eval α) (d.eval α) := rfl

/-- Number of nodes of a formula. -/
def size : Circ → ℕ
  | fls => 1
  | tru => 1
  | var _ => 1
  | neg c => c.size + 1
  | conj c d => c.size + d.size + 1
  | disj c d => c.size + d.size + 1
  | xorC c d => c.size + d.size + 1

@[simp] lemma size_fls : size fls = 1 := rfl
@[simp] lemma size_tru : size tru = 1 := rfl
@[simp] lemma size_var (i) : size (var i) = 1 := rfl
@[simp] lemma size_neg (c) : size (neg c) = c.size + 1 := rfl
@[simp] lemma size_conj (c d) : size (conj c d) = c.size + d.size + 1 := rfl
@[simp] lemma size_disj (c d) : size (disj c d) = c.size + d.size + 1 := rfl
@[simp] lemma size_xorC (c d) : size (xorC c d) = c.size + d.size + 1 := rfl

/-- Renaming of variables. -/
def subst : Circ → (ℕ → ℕ) → Circ
  | fls, _ => fls
  | tru, _ => tru
  | var i, ρ => var (ρ i)
  | neg c, ρ => neg (c.subst ρ)
  | conj c d, ρ => conj (c.subst ρ) (d.subst ρ)
  | disj c d, ρ => disj (c.subst ρ) (d.subst ρ)
  | xorC c d, ρ => xorC (c.subst ρ) (d.subst ρ)

@[simp] lemma eval_subst (c : Circ) (ρ : ℕ → ℕ) (α : ℕ → Bool) :
    (c.subst ρ).eval α = c.eval (fun i => α (ρ i)) := by
  induction c with
  | fls => rfl
  | tru => rfl
  | var i => rfl
  | neg c ih => simp [subst, ih]
  | conj c d ih1 ih2 => simp [subst, ih1, ih2]
  | disj c d ih1 ih2 => simp [subst, ih1, ih2]
  | xorC c d ih1 ih2 => simp [subst, ih1, ih2]

@[simp] lemma size_subst (c : Circ) (ρ : ℕ → ℕ) : (c.subst ρ).size = c.size := by
  induction c with
  | fls => rfl
  | tru => rfl
  | var i => rfl
  | neg c ih => simp [subst, ih]
  | conj c d ih1 ih2 => simp [subst, ih1, ih2]
  | disj c d ih1 ih2 => simp [subst, ih1, ih2]
  | xorC c d ih1 ih2 => simp [subst, ih1, ih2]

/-- Conjunction of a list of formulas. -/
def bigAnd : List Circ → Circ
  | [] => tru
  | c :: cs => conj c (bigAnd cs)

/-- Disjunction of a list of formulas. -/
def bigOr : List Circ → Circ
  | [] => fls
  | c :: cs => disj c (bigOr cs)

/-- Parity (xor) of a list of formulas. -/
def bigXor : List Circ → Circ
  | [] => fls
  | c :: cs => xorC c (bigXor cs)

@[simp] lemma eval_bigAnd (l : List Circ) (α) :
    (bigAnd l).eval α = l.all (fun c => c.eval α) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [bigAnd, ih]

@[simp] lemma eval_bigOr (l : List Circ) (α) :
    (bigOr l).eval α = l.any (fun c => c.eval α) := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [bigOr, ih]

lemma size_bigAnd (l : List Circ) : (bigAnd l).size ≤ 1 + (l.map size).sum + l.length := by
  induction l with
  | nil => simp [bigAnd]
  | cons c cs ih => simp [bigAnd]; omega

lemma size_bigOr (l : List Circ) : (bigOr l).size ≤ 1 + (l.map size).sum + l.length := by
  induction l with
  | nil => simp [bigOr]
  | cons c cs ih => simp [bigOr]; omega

lemma size_bigXor (l : List Circ) : (bigXor l).size ≤ 1 + (l.map size).sum + l.length := by
  induction l with
  | nil => simp [bigXor]
  | cons c cs ih => simp [bigXor]; omega

end Circ

/-! ### Assignments extended by blocks of witness bits -/

/-- `ext α off w` is the assignment which agrees with `α` outside the window
`[off, off + M)` and takes the values of the block `w` inside it. -/
def ext (α : ℕ → Bool) (off : ℕ) {M : ℕ} (w : Fin M → Bool) : ℕ → Bool := fun i =>
  if h : off ≤ i ∧ i - off < M then w ⟨i - off, h.2⟩ else α i

lemma ext_lt (α : ℕ → Bool) (off : ℕ) {M : ℕ} (w : Fin M → Bool) {i : ℕ} (h : i < off) :
    ext α off w i = α i := by
  have hn : ¬ (off ≤ i ∧ i - off < M) := by omega
  simp only [ext, dif_neg hn]

lemma ext_ge (α : ℕ → Bool) (off : ℕ) {M : ℕ} (w : Fin M → Bool) {i : ℕ} (h : off + M ≤ i) :
    ext α off w i = α i := by
  have hn : ¬ (off ≤ i ∧ i - off < M) := by omega
  simp only [ext, dif_neg hn]

lemma ext_mem (α : ℕ → Bool) (off : ℕ) {M : ℕ} (w : Fin M → Bool) (j : Fin M) :
    ext α off w (off + j) = w j := by
  have h : off ≤ off + (j : ℕ) ∧ off + (j : ℕ) - off < M := by omega
  simp only [ext, dif_pos h]
  congr 1
  simp

/-- Number of witness blocks of length `M`, placed at offset `off`, satisfying `V`. -/
def cnt (V : Circ) (α : ℕ → Bool) (off M : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin M → Bool => V.eval (ext α off w) = true)).card

lemma cnt_eq_sum (V : Circ) (α : ℕ → Bool) (off M : ℕ) :
    cnt V α off M = ∑ w : Fin M → Bool, (if V.eval (ext α off w) = true then 1 else 0) := by
  rw [cnt, Finset.card_filter]

/-- Concatenation of two blocks. -/
def blockCat {M₁ M₂ : ℕ} (w₁ : Fin M₁ → Bool) (w₂ : Fin M₂ → Bool) : Fin (M₁ + M₂) → Bool :=
  fun i => if h : (i : ℕ) < M₁ then w₁ ⟨i, h⟩ else w₂ ⟨(i : ℕ) - M₁, by omega⟩

lemma ext_blockCat (α : ℕ → Bool) (off : ℕ) {M₁ M₂ : ℕ}
    (w₁ : Fin M₁ → Bool) (w₂ : Fin M₂ → Bool) :
    ext α off (blockCat w₁ w₂) = ext (ext α off w₁) (off + M₁) w₂ := by
  funext i
  by_cases h1 : i < off
  · rw [ext_lt _ _ _ h1, ext_lt _ _ _ (by omega : i < off + M₁), ext_lt _ _ _ h1]
  by_cases h2 : i < off + M₁
  · have e1 : ext α off (blockCat w₁ w₂) i = blockCat w₁ w₂ ⟨i - off, by omega⟩ := by
      simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ + M₂ by omega)]
    rw [e1, ext_lt _ _ _ (by omega : i < off + M₁)]
    have e2 : ext α off w₁ i = w₁ ⟨i - off, by omega⟩ := by
      simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ by omega)]
    rw [e2]
    simp only [blockCat, dif_pos (show i - off < M₁ by omega)]
  · by_cases h3 : i < off + M₁ + M₂
    · have e1 : ext α off (blockCat w₁ w₂) i = blockCat w₁ w₂ ⟨i - off, by omega⟩ := by
        simp only [ext, dif_pos (show off ≤ i ∧ i - off < M₁ + M₂ by omega)]
      have e2 : ext (ext α off w₁) (off + M₁) w₂ i = w₂ ⟨i - (off + M₁), by omega⟩ := by
        simp only [ext, dif_pos (show off + M₁ ≤ i ∧ i - (off + M₁) < M₂ by omega)]
      rw [e1, e2]
      simp only [blockCat, dif_neg (show ¬ (i - off < M₁) by omega)]
      congr 1
      simp only [Fin.mk.injEq]
      omega
    · rw [ext_ge _ _ _ (by omega : off + (M₁ + M₂) ≤ i), ext_ge _ _ _ (by omega : off + M₁ + M₂ ≤ i),
        ext_ge _ _ _ (by omega : off + M₁ ≤ i)]

/-- The concatenation map is a bijection. -/
def blockCatEquiv (M₁ M₂ : ℕ) :
    ((Fin M₁ → Bool) × (Fin M₂ → Bool)) ≃ (Fin (M₁ + M₂) → Bool) where
  toFun p := blockCat p.1 p.2
  invFun w := (fun i => w ⟨i, by omega⟩, fun i => w ⟨M₁ + i, by omega⟩)
  left_inv := by
    rintro ⟨w₁, w₂⟩
    have h1 : (fun i : Fin M₁ => blockCat w₁ w₂ ⟨i, by omega⟩) = w₁ := by
      funext i
      simp only [blockCat, dif_pos i.isLt]
    have h2 : (fun i : Fin M₂ => blockCat w₁ w₂ ⟨M₁ + i, by omega⟩) = w₂ := by
      funext i
      simp only [blockCat]
      rw [dif_neg (by omega : ¬ ((M₁ + (i : ℕ)) < M₁))]
      congr 1
      simp
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  right_inv := by
    intro w
    funext i
    simp only [blockCat]
    by_cases h : (i : ℕ) < M₁
    · rw [dif_pos h]
    · rw [dif_neg h]
      have he : (⟨M₁ + ((i : ℕ) - M₁), by omega⟩ : Fin (M₁ + M₂)) = i := by
        apply Fin.ext
        simp only []
        omega
      rw [he]

/-- Counting over a block of size `M₁ + M₂` splits as a sum over the first sub-block. -/
lemma cnt_split (V : Circ) (α : ℕ → Bool) (off M₁ M₂ : ℕ) :
    cnt V α off (M₁ + M₂) = ∑ w₁ : Fin M₁ → Bool, cnt V (ext α off w₁) (off + M₁) M₂ := by
  rw [cnt_eq_sum]
  rw [← Equiv.sum_comp (blockCatEquiv M₁ M₂)
    (fun w => if V.eval (ext α off w) = true then 1 else 0)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun w₁ _ => ?_)
  rw [cnt_eq_sum]
  refine Finset.sum_congr rfl (fun w₂ _ => ?_)
  simp only [blockCatEquiv, Equiv.coe_fn_mk, ext_blockCat]

/-! ### Polynomial bounds -/

/-- A function `ℕ → ℕ` is polynomially bounded. -/
def PolyBd (f : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, f n ≤ c * (n + 1) ^ k

lemma PolyBd.const (c : ℕ) : PolyBd (fun _ => c) := ⟨c, 0, by simp⟩

lemma PolyBd.id' : PolyBd (fun n => n) := ⟨1, 1, by intro n; simp⟩

lemma PolyBd.mono {f g : ℕ → ℕ} (hg : PolyBd g) (h : ∀ n, f n ≤ g n) : PolyBd f := by
  obtain ⟨c, k, hc⟩ := hg
  exact ⟨c, k, fun n => le_trans (h n) (hc n)⟩

lemma PolyBd.add {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd (fun n => f n + g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max k₁ k₂, fun n => ?_⟩
  have p1 : (n + 1) ^ k₁ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have p2 : (n + 1) ^ k₂ ≤ (n + 1) ^ (max k₁ k₂) :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  calc f n + g n ≤ c₁ * (n+1)^k₁ + c₂ * (n+1)^k₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * (n+1)^(max k₁ k₂) + c₂ * (n+1)^(max k₁ k₂) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ p1) (Nat.mul_le_mul_left _ p2)
    _ = (c₁ + c₂) * (n+1)^(max k₁ k₂) := by ring

lemma PolyBd.mul {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd (fun n => f n * g n) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, k₁ + k₂, fun n => ?_⟩
  calc f n * g n ≤ (c₁ * (n+1)^k₁) * (c₂ * (n+1)^k₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
    _ = c₁ * c₂ * (n+1)^(k₁+k₂) := by ring

lemma PolyBd.comp {f g : ℕ → ℕ} (hf : PolyBd f) (hg : PolyBd g) : PolyBd (fun n => f (g n)) := by
  obtain ⟨c₁, k₁, h₁⟩ := hf
  obtain ⟨c₂, k₂, h₂⟩ := hg
  refine ⟨c₁ * (c₂ + 1) ^ k₁, k₂ * k₁, fun n => ?_⟩
  have hpow : 1 ≤ (n + 1) ^ k₂ := Nat.one_le_pow _ _ (by omega)
  have h : g n + 1 ≤ (c₂ + 1) * (n + 1) ^ k₂ := by
    have := h₂ n
    nlinarith
  calc f (g n) ≤ c₁ * (g n + 1) ^ k₁ := h₁ _
    _ ≤ c₁ * ((c₂ + 1) * (n + 1) ^ k₂) ^ k₁ :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = c₁ * (c₂ + 1) ^ k₁ * (n + 1) ^ (k₂ * k₁) := by
        rw [Nat.mul_pow, ← Nat.pow_mul]; ring

/-- A family of formulas of polynomial size. -/
def PolySize (C : ℕ → Circ) : Prop := PolyBd (fun n => (C n).size)

end CS

import RequestProject.Toda.Circuit

/-!
# The complexity classes `PH`, `#P` and `P^{#P}`

We work in the (standard) nonuniform circuit model: a *language* assigns to every input
length `n` a predicate on `n`-bit inputs, and "polynomial time" is modelled by families of
boolean formulas of polynomial size (i.e. `P/poly`).  All classes below are the
circuit analogues of the usual uniform ones.
-/

open scoped BigOperators

namespace CS

/-- A language: for every input length, a predicate on inputs of that length. -/
def Lang := (n : ℕ) → (Fin n → Bool) → Prop

/-- The assignment associated with an input: bit `i` of `x` for `i < n`, `false` beyond. -/
def inp {n : ℕ} (x : Fin n → Bool) : ℕ → Bool := ext (fun _ => false) 0 x

@[simp] lemma inp_apply {n : ℕ} (x : Fin n → Bool) (i : Fin n) : inp x i = x i := by
  have := ext_mem (fun _ => false) 0 x i
  simpa using this

/-! ### The polynomial hierarchy -/

/-- `altSat qs off m α C` is the value of the quantified formula with quantifier
prefix `qs` (`true` = `∃`, `false` = `∀`), whose quantified blocks have length `m` and are
placed at the consecutive offsets `off, off + m, off + 2m, …` of the assignment `α`,
and whose matrix is the formula `C`. -/
def altSat : List Bool → ℕ → ℕ → (ℕ → Bool) → Circ → Prop
  | [], _, _, α, C => C.eval α = true
  | (q :: qs), off, m, α, C =>
      if q then ∃ y : Fin m → Bool, altSat qs (off + m) m (ext α off y) C
      else ∀ y : Fin m → Bool, altSat qs (off + m) m (ext α off y) C

@[simp] lemma altSat_nil (off m : ℕ) (α : ℕ → Bool) (C : Circ) :
    altSat [] off m α C ↔ C.eval α = true := Iff.rfl

@[simp] lemma altSat_cons_true (qs : List Bool) (off m : ℕ) (α : ℕ → Bool) (C : Circ) :
    altSat (true :: qs) off m α C ↔
      ∃ y : Fin m → Bool, altSat qs (off + m) m (ext α off y) C := by
  simp [altSat]

@[simp] lemma altSat_cons_false (qs : List Bool) (off m : ℕ) (α : ℕ → Bool) (C : Circ) :
    altSat (false :: qs) off m α C ↔
      ∀ y : Fin m → Bool, altSat qs (off + m) m (ext α off y) C := by
  simp [altSat]

/-- The polynomial hierarchy (in the circuit model): languages defined by a constant
number of alternating quantifiers over polynomially long witnesses, with a
polynomial-size matrix. -/
def PH (L : Lang) : Prop :=
  ∃ (qs : List Bool) (m : ℕ → ℕ) (C : ℕ → Circ), PolyBd m ∧ PolySize C ∧
    ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔ altSat qs n (m n) (inp x) (C n)

/-! ### The counting class `#P` -/

/-- `#P` (in the circuit model): functions counting the satisfying witness blocks of a
polynomial-size formula. -/
def SharpP (f : (n : ℕ) → (Fin n → Bool) → ℕ) : Prop :=
  ∃ (M : ℕ → ℕ) (V : ℕ → Circ), PolyBd M ∧ PolySize V ∧
    ∀ (n : ℕ) (x : Fin n → Bool), f n x = cnt (V n) (inp x) n (M n)

/-! ### Oracle machines and `P^{#P}` -/

/-- A (nonuniform) polynomial-time oracle machine: it makes `t` adaptive queries of length
`qlen` to the oracle, keeping `abits` bits of each answer.  Bit `c` of query `i` is computed
by the formula `Q i c` from the input together with the answer bits of the earlier queries,
which are stored in consecutive blocks starting at offset `base`.  The formula `out`
computes the final answer. -/
structure OMach where
  /-- number of oracle queries -/
  t : ℕ
  /-- length of each query string -/
  qlen : ℕ
  /-- number of bits kept from each answer -/
  abits : ℕ
  /-- offset at which the answer blocks are stored -/
  base : ℕ
  /-- `Q i c` computes bit `c` of the `i`-th query -/
  Q : ℕ → ℕ → Circ
  /-- output formula -/
  out : Circ

namespace OMach

/-- The assignment after `i` oracle queries have been answered. -/
def state (f : (n : ℕ) → (Fin n → Bool) → ℕ) (α : ℕ → Bool) (M : OMach) : ℕ → (ℕ → Bool)
  | 0 => α
  | (i + 1) =>
      let β := M.state f α i
      ext β (M.base + i * M.abits)
        (fun k : Fin M.abits =>
          Nat.testBit (f M.qlen (fun c : Fin M.qlen => (M.Q i c).eval β)) k)

/-- The value computed by the oracle machine. -/
def accepts (f : (n : ℕ) → (Fin n → Bool) → ℕ) (α : ℕ → Bool) (M : OMach) : Bool :=
  M.out.eval (M.state f α M.t)

/-- Size of an oracle machine. -/
def size (M : OMach) : ℕ :=
  M.out.size + M.base + M.abits + M.t + M.qlen +
    ∑ i ∈ Finset.range M.t, ∑ c ∈ Finset.range M.qlen, (M.Q i c).size

end OMach

/-- `P^{#P}` (in the circuit model): languages decided by a polynomial-size family of
oracle machines whose oracle is a `#P` function. -/
def PSharpP (L : Lang) : Prop :=
  ∃ (f : (n : ℕ) → (Fin n → Bool) → ℕ), SharpP f ∧
    ∃ (D : ℕ → OMach), PolyBd (fun n => (D n).size) ∧
      ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔ (D n).accepts f (inp x) = true

/-! ### A single oracle query suffices -/

/-- The oracle machine which queries the oracle on the input itself and outputs bit `j`
of the answer. -/
def bitMach (n j : ℕ) : OMach where
  t := 1
  qlen := n
  abits := j + 1
  base := n
  Q := fun _ c => Circ.var c
  out := Circ.var (n + j)

lemma bitMach_size (n j : ℕ) : (bitMach n j).size = 1 + n + (j + 1) + 1 + n + n := by
  simp [bitMach, OMach.size]
  ring

lemma bitMach_accepts (f : (n : ℕ) → (Fin n → Bool) → ℕ) (n j : ℕ) (x : Fin n → Bool) :
    (bitMach n j).accepts f (inp x) = Nat.testBit (f n x) j := by
  show Circ.eval (Circ.var (n + j)) _ = _
  simp only [OMach.state, Circ.eval_var, bitMach]
  have hx : (fun c : Fin n => (Circ.var (c : ℕ)).eval (inp x)) = x := by
    funext c
    simp
  rw [hx]
  have := ext_mem (inp x) (n + 0 * (j + 1))
    (fun k : Fin (j + 1) => Nat.testBit (f n x) k) ⟨j, by omega⟩
  simpa using this

/-- If a language is decided by taking one prescribed bit of the value of a `#P` function
on the input itself, then it lies in `P^{#P}`. -/
lemma PSharpP_of_bit {L : Lang} {f : (n : ℕ) → (Fin n → Bool) → ℕ} (hf : SharpP f)
    {j : ℕ → ℕ} (hj : PolyBd j)
    (h : ∀ (n : ℕ) (x : Fin n → Bool), L n x ↔ Nat.testBit (f n x) (j n) = true) :
    PSharpP L := by
  classical
  refine ⟨f, hf, fun n => bitMach n (j n), ?_, ?_⟩
  · refine PolyBd.mono (g := fun n => 1 + n + (j n + 1) + 1 + n + n)
      (PolyBd.add (PolyBd.add (PolyBd.add (PolyBd.add (PolyBd.add
        (PolyBd.const 1) PolyBd.id') (PolyBd.add hj (PolyBd.const 1)))
        (PolyBd.const 1)) PolyBd.id') PolyBd.id') ?_
    intro n
    exact le_of_eq (bitMach_size n (j n))
  · intro n x
    rw [h n x, bitMach_accepts]

end CS


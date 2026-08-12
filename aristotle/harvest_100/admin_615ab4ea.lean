/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/
def eval {n : ℕ} : Circ n → (Fin n → Bool) → Bool
  | var i, x => x i
  | const b, _ => b
  | not c, x => !(eval c x)
  | and a b, x => (eval a x) && (eval b x)
  | or a b, x => (eval a x) || (eval b x)

/-- The set of subcircuits (gates) of a circuit. -/
def subterms {n : ℕ} : Circ n → Finset (Circ n)
  | var i => {var i}
  | const b => {const b}
  | not c => insert (not c) (subterms c)
  | and a b => insert (and a b) (subterms a ∪ subterms b)
  | or a b => insert (or a b) (subterms a ∪ subterms b)

/-- The size of a circuit: the number of distinct gates, i.e. its size as a DAG. -/
def size {n : ℕ} (c : Circ n) : ℕ := (subterms c).card

@[simp] lemma size_var {n : ℕ} (i : Fin n) : size (var i) = 1 := by
  simp [size, subterms]

@[simp] lemma size_const {n : ℕ} (b : Bool) : size (const b : Circ n) = 1 := by
  simp [size, subterms]

lemma size_not {n : ℕ} (c : Circ n) : size (not c) ≤ 1 + size c := by
  simpa [size, subterms, add_comm] using Finset.card_insert_le (not c) (subterms c)

lemma size_and {n : ℕ} (a b : Circ n) : size (and a b) ≤ 1 + size a + size b := by
  have h1 : (insert (and a b) (subterms a ∪ subterms b)).card
      ≤ (subterms a ∪ subterms b).card + 1 := Finset.card_insert_le _ _
  have h2 : (subterms a ∪ subterms b).card ≤ (subterms a).card + (subterms b).card :=
    Finset.card_union_le _ _
  simp only [size, subterms]
  omega

lemma size_or {n : ℕ} (a b : Circ n) : size (or a b) ≤ 1 + size a + size b := by
  have h1 : (insert (or a b) (subterms a ∪ subterms b)).card
      ≤ (subterms a ∪ subterms b).card + 1 := Finset.card_insert_le _ _
  have h2 : (subterms a ∪ subterms b).card ≤ (subterms a).card + (subterms b).card :=
    Finset.card_union_le _ _
  simp only [size, subterms]
  omega

/-- Substitution of circuits for the input variables of a circuit. -/
def subst {n k : ℕ} : Circ k → (Fin k → Circ n) → Circ n
  | var i, σ => σ i
  | const b, _ => const b
  | not c, σ => not (subst c σ)
  | and a b, σ => and (subst a σ) (subst b σ)
  | or a b, σ => or (subst a σ) (subst b σ)

lemma eval_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) (x : Fin n → Bool) :
    eval (subst c σ) x = eval c (fun i => eval (σ i) x) := by
  induction c with
  | var i => simp [subst, eval]
  | const b => simp [subst, eval]
  | not c ih => simp [subst, eval, ih]
  | and a b iha ihb => simp [subst, eval, iha, ihb]
  | or a b iha ihb => simp [subst, eval, iha, ihb]

lemma subterms_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) :
    subterms (subst c σ) ⊆
      (subterms c).image (fun t => subst t σ) ∪
        Finset.univ.biUnion (fun i : Fin k => subterms (σ i)) := by
  induction c with
  | var i =>
      intro t ht
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩)
  | const b =>
      intro t ht
      refine Finset.mem_union_left _ ?_
      simp only [subst, subterms, Finset.mem_singleton] at ht
      subst ht
      exact Finset.mem_image.2 ⟨const b, by simp [subterms], rfl⟩
  | not c ih =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert] at ht
      rcases ht with ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨not c, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (ih ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
  | and a b iha ihb =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert, Finset.mem_union] at ht
      rcases ht with ht | ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨and a b, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (iha ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.1 (ihb ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
  | or a b iha ihb =>
      intro t ht
      simp only [subst, subterms, Finset.mem_insert, Finset.mem_union] at ht
      rcases ht with ht | ht | ht
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨or a b, ?_, ?_⟩)
        · simp [subterms]
        · simp [subst, ht]
      · rcases Finset.mem_union.1 (iha ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.1 (ihb ht) with h | h
        · rcases Finset.mem_image.1 h with ⟨u, hu, hu'⟩
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨u, by simp [subterms, hu], hu'⟩)
        · exact Finset.mem_union_right _ h

/-- Substitution costs at most the sum of the sizes: this is where the DAG size measure
(with sharing) is essential. -/
lemma size_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) :
    size (subst c σ) ≤ size c + ∑ i : Fin k, size (σ i) := by
  have h := Finset.card_le_card (subterms_subst c σ)
  have h2 : ((subterms c).image (fun t => subst t σ) ∪
      Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card
      ≤ ((subterms c).image (fun t => subst t σ)).card
        + (Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card :=
    Finset.card_union_le _ _
  have h3 : ((subterms c).image (fun t => subst t σ)).card ≤ (subterms c).card :=
    Finset.card_image_le
  have h4 : (Finset.univ.biUnion (fun i : Fin k => subterms (σ i))).card
      ≤ ∑ i : Fin k, (subterms (σ i)).card := Finset.card_biUnion_le
  simp only [size]
  omega

/-- The canonical circuit computing a function of the coordinates in the list `L`
(the other coordinates being fixed by `ρ`): a full binary decision tree. -/
def juntaCirc {n : ℕ} (h : (Fin n → Bool) → Bool) : List (Fin n) → (Fin n → Bool) → Circ n
  | [], ρ => const (h ρ)
  | i :: L, ρ =>
      or (and (var i) (juntaCirc h L (Function.update ρ i true)))
        (and (not (var i)) (juntaCirc h L (Function.update ρ i false)))

lemma eval_juntaCirc {n : ℕ} (h : (Fin n → Bool) → Bool) :
    ∀ (L : List (Fin n)) (ρ x : Fin n → Bool),
      eval (juntaCirc h L ρ) x = h (fun k => if k ∈ L then x k else ρ k) := by
  intro L
  induction L with
  | nil => intro ρ x; simp [juntaCirc, eval]
  | cons i L ih =>
      intro ρ x
      simp only [juntaCirc, eval, ih]
      cases hx : x i with
      | true =>
          simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
          congr 1
          funext k
          by_cases hk : k = i
          · subst hk
            by_cases hkL : k ∈ L <;> simp [hkL, hx]
          · by_cases hkL : k ∈ L <;> simp [hkL, hk]
      | false =>
          simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
          congr 1
          funext k
          by_cases hk : k = i
          · subst hk
            by_cases hkL : k ∈ L <;> simp [hkL, hx]
          · by_cases hkL : k ∈ L <;> simp [hkL, hk]

lemma size_juntaCirc {n : ℕ} (h : (Fin n → Bool) → Bool) :
    ∀ (L : List (Fin n)) (ρ : Fin n → Bool),
      size (juntaCirc h L ρ) + 6 ≤ 7 * 2 ^ L.length := by
  intro L
  induction L with
  | nil => intro ρ; simp [juntaCirc]
  | cons i L ih =>
      intro ρ
      have h1 := ih (Function.update ρ i true)
      have h0 := ih (Function.update ρ i false)
      have e1 := size_or (and (var i) (juntaCirc h L (Function.update ρ i true)))
        (and (not (var i)) (juntaCirc h L (Function.update ρ i false)))
      have e2 := size_and (var i) (juntaCirc h L (Function.update ρ i true))
      have e3 := size_and (not (var i)) (juntaCirc h L (Function.update ρ i false))
      have e4 := size_not (var i : Circ n)
      have e5 : size (var i : Circ n) = 1 := size_var i
      have hp : (1:ℕ) ≤ 2 ^ L.length := Nat.one_le_two_pow
      have : (7 : ℕ) * 2 ^ (i :: L).length = 7 * 2 ^ L.length + 7 * 2 ^ L.length := by
        simp [List.length_cons, pow_succ]; ring
      simp only [juntaCirc] at *
      omega

end Circ

/-! ## Real-valued indicators -/

/-- The real-valued indicator of a Boolean. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- The real-valued indicator of agreement of two Booleans. -/
def agree (a b : Bool) : ℝ := if a = b then 1 else 0

/-- The key pointwise identity behind the next-bit predictor: averaged over the value of the
random bit `r`, the predictor `x ↦ (A r == r)` (possibly negated) agrees with `fx` exactly with
probability `1/2` plus the distinguishing advantage. -/
lemma nw_pair_identity (A0 A1 r fx neg : Bool) :
    agree (xor neg ((cond r A1 A0) == r)) fx
        + agree (xor neg ((cond (!r) A1 A0) == (!r))) fx
      = 1 + (if neg then (-1 : ℝ) else 1) *
          ((b2r (cond fx A1 A0) - b2r (cond r A1 A0))
            + (b2r (cond fx A1 A0) - b2r (cond (!r) A1 A0))) := by
  cases A0 <;> cases A1 <;> cases r <;> cases fx <;> cases neg <;>
    norm_num [agree, b2r]

/-! ## Blocks of the seed -/

/-- Overwrite the coordinates of `z` lying in the image of `e` according to `x`. -/
noncomputable def setBlock {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool) (x : Fin ℓ → Bool) :
    Fin d → Bool :=
  fun k => if h : ∃ t, e t = k then x h.choose else z k

lemma setBlock_apply_mem {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool) (x : Fin ℓ → Bool)
    (t : Fin ℓ) : setBlock e z x (e t) = x t := by
  have h : ∃ u, e u = e t := ⟨t, rfl⟩
  simp only [setBlock, dif_pos h]
  congr 1
  exact e.injective h.choose_spec

lemma setBlock_apply_not_mem {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool)
    (x : Fin ℓ → Bool) {k : Fin d} (hk : ¬ ∃ t, e t = k) : setBlock e z x k = z k := by
  simp only [setBlock, dif_neg hk]

lemma setBlock_comp {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool) (x : Fin ℓ → Bool) :
    (setBlock e z x) ∘ e = x := by
  funext t; exact setBlock_apply_mem e z x t

lemma setBlock_setBlock {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool) (x : Fin ℓ → Bool) :
    setBlock e (setBlock e z x) (z ∘ e) = z := by
  funext k
  by_cases hk : ∃ t, e t = k
  · obtain ⟨t, rfl⟩ := hk
    simp [setBlock_apply_mem]
  · rw [setBlock_apply_not_mem _ _ _ hk, setBlock_apply_not_mem _ _ _ hk]

/-- Averaging over the seed and over a fresh block value is the same as averaging over the
seed, up to the factor `2 ^ ℓ`. -/
lemma sum_setBlock {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (g : (Fin d → Bool) → ℝ) :
    ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, g (setBlock e z x)
      = 2 ^ ℓ * ∑ z : Fin d → Bool, g z := by
  classical
  set Φ : ((Fin d → Bool) × (Fin ℓ → Bool)) → ((Fin d → Bool) × (Fin ℓ → Bool)) :=
    fun p => (setBlock e p.1 p.2, p.1 ∘ e) with hΦ
  have hinv : Function.Involutive Φ := by
    intro p
    obtain ⟨z, x⟩ := p
    simp only [hΦ]
    exact Prod.ext (setBlock_setBlock e z x) (setBlock_comp e z x)
  have h1 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g (Φ p).1
      = ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g p.1 :=
    Equiv.sum_comp (hinv.toPerm Φ) (fun p => g p.1)
  have h2 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g (Φ p).1
      = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, g (setBlock e z x) := by
    rw [Fintype.sum_prod_type]
  have h3 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g p.1
      = 2 ^ ℓ * ∑ z : Fin d → Bool, g z := by
    rw [Fintype.sum_prod_type]
    have hc : (Fintype.card (Fin ℓ → Bool) : ℝ) = 2 ^ ℓ := by simp
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    rw [← Finset.mul_sum]
  rw [← h2, h1, h3]

/-! ## The Nisan-Wigderson generator and the hybrid argument -/

/-- The `i`-th hybrid string: the first `i` bits are outputs of the generator, the `i`-th bit
is `b`, and the remaining bits are taken from the truly random string `y`. -/
def nwStr {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (i : Fin m) (z : Fin d → Bool) (y : Fin m → Bool) (b : Bool) : Fin m → Bool :=
  fun j => if (j : ℕ) < (i : ℕ) then f (z ∘ e j) else if j = i then b else y j

/-- The acceptance probability of the test `D` on the `i`-th hybrid distribution: the first `i`
coordinates are produced by the Nisan-Wigderson generator, the remaining ones are uniform. -/
noncomputable def hybAcc {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) (i : ℕ) : ℝ :=
  (∑ z : Fin d → Bool, ∑ y : Fin m → Bool,
      b2r (D.eval (fun j => if (j : ℕ) < i then f (z ∘ e j) else y j))) / (2 ^ d * 2 ^ m)

lemma hybAcc_zero {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) :
    hybAcc e f D 0 = (∑ y : Fin m → Bool, b2r (D.eval y)) / 2 ^ m := by
  have h : ∀ z : Fin d → Bool,
      (∑ y : Fin m → Bool, b2r (D.eval (fun j => if (j : ℕ) < 0 then f (z ∘ e j) else y j)))
        = ∑ y : Fin m → Bool, b2r (D.eval y) := by
    intro z; simp
  have hc : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
  rw [hybAcc, Finset.sum_congr rfl (fun z _ => h z), Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul, hc]
  exact mul_div_mul_left _ _ (by positivity)

lemma hybAcc_top {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) :
    hybAcc e f D m = (∑ z : Fin d → Bool, b2r (D.eval (fun i => f (z ∘ e i)))) / 2 ^ d := by
  have h : ∀ z : Fin d → Bool,
      (∑ _y : Fin m → Bool, b2r (D.eval (fun j => if (j : ℕ) < m then f (z ∘ e j) else _y j)))
        = (2 : ℝ) ^ m * b2r (D.eval (fun j => f (z ∘ e j))) := by
    intro z
    have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
    have : ∀ y : Fin m → Bool,
        b2r (D.eval (fun j => if (j : ℕ) < m then f (z ∘ e j) else y j))
          = b2r (D.eval (fun j => f (z ∘ e j))) := by
      intro y
      congr 1
      congr 1
      funext j
      simp [j.isLt]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul, hcm]
  rw [hybAcc, Finset.sum_congr rfl (fun z _ => h z), ← Finset.mul_sum]
  rw [mul_comm ((2:ℝ) ^ d) ((2:ℝ) ^ m), mul_div_mul_left _ _ (by positivity)]

/-- The difference of two consecutive hybrids, written in terms of the next-bit strings. -/
lemma hybAcc_succ_sub {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) (i : Fin m) :
    hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ)
      = (∑ z : Fin d → Bool, ∑ y : Fin m → Bool,
          (b2r (D.eval (nwStr e f i z y (f (z ∘ e i)))) - b2r (D.eval (nwStr e f i z y (y i)))))
        / (2 ^ d * 2 ^ m) := by
  have h1 : ∀ (z : Fin d → Bool) (y : Fin m → Bool),
      (fun j : Fin m => if (j : ℕ) < (i : ℕ) + 1 then f (z ∘ e j) else y j)
        = nwStr e f i z y (f (z ∘ e i)) := by
    intro z y
    funext j
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [nwStr, hj, Nat.lt_succ_of_lt hj]
    · by_cases hj2 : j = i
      · subst hj2; simp [nwStr]
      · have hlt : ¬ ((j : ℕ) < (i : ℕ) + 1) := by
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hj2 (Fin.ext h.symm)
          omega
        simp [nwStr, hj, hj2, hlt]
  have h2 : ∀ (z : Fin d → Bool) (y : Fin m → Bool),
      (fun j : Fin m => if (j : ℕ) < (i : ℕ) then f (z ∘ e j) else y j) = nwStr e f i z y (y i) := by
    intro z y
    funext j
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [nwStr, hj]
    · by_cases hj2 : j = i
      · subst hj2; simp [nwStr]
      · simp [nwStr, hj, hj2]
  rw [hybAcc, hybAcc, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [h1, h2]

/-- Construction of the next-bit predictor circuit, together with its size bound. -/
lemma nw_predictor_circuit {ℓ d m α : ℕ}
    (e : Fin m → (Fin ℓ ↪ Fin d))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (e i)) ∩ (Finset.univ.image (e j))).card ≤ α)
    (f : (Fin ℓ → Bool) → Bool) (D : Circ m) (i : Fin m)
    (z₀ : Fin d → Bool) (y₀ : Fin m → Bool) (neg : Bool) :
    ∃ C : Circ ℓ, C.size ≤ D.size + m * (7 * 2 ^ α) + 1 ∧
      ∀ x : Fin ℓ → Bool,
        C.eval x =
          xor neg ((D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) == y₀ i) := by
  classical
  set T : Fin m → Finset (Fin ℓ) :=
    fun j => Finset.univ.filter (fun t : Fin ℓ => ∃ u, e j u = e i t) with hT
  -- the blocks of a design overlap in few positions
  have hTcard : ∀ j : Fin m, j ≠ i → (T j).card ≤ α := by
    intro j hji
    have himg : (T j).image (e i) = (Finset.univ.image (e i)) ∩ (Finset.univ.image (e j)) := by
      ext k
      simp only [hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_inter]
      constructor
      · rintro ⟨t, ⟨u, hu⟩, rfl⟩
        exact ⟨⟨t, rfl⟩, ⟨u, by rw [hu]⟩⟩
      · rintro ⟨⟨t, rfl⟩, ⟨u, hu⟩⟩
        exact ⟨t, ⟨u, hu⟩, rfl⟩
    have hcard : (T j).card = ((T j).image (e i)).card :=
      (Finset.card_image_of_injective _ (e i).injective).symm
    rw [hcard, himg]
    exact hdesign i j (Ne.symm hji)
  -- the `j`-th output bit depends only on the positions of block `i` met by block `j`
  have hdep : ∀ (j : Fin m) (x₁ x₂ : Fin ℓ → Bool), (∀ t ∈ T j, x₁ t = x₂ t) →
      f (setBlock (e i) z₀ x₁ ∘ e j) = f (setBlock (e i) z₀ x₂ ∘ e j) := by
    intro j x₁ x₂ hx
    congr 1
    funext u
    simp only [Function.comp_apply]
    by_cases h : ∃ t, e i t = e j u
    · obtain ⟨t, ht⟩ := h
      rw [← ht, setBlock_apply_mem, setBlock_apply_mem]
      exact hx t (by simp [hT, ht])
    · rw [setBlock_apply_not_mem _ _ _ h, setBlock_apply_not_mem _ _ _ h]
  set σ : Fin m → Circ ℓ := fun j =>
    if (j : ℕ) < (i : ℕ) then
      Circ.juntaCirc (fun x => f (setBlock (e i) z₀ x ∘ e j)) (T j).toList (fun _ => false)
    else Circ.const (y₀ j) with hσ
  have hevalσ : ∀ (j : Fin m) (x : Fin ℓ → Bool),
      Circ.eval (σ j) x = nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i) j := by
    intro j x
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp only [hσ, nwStr, if_pos hj]
      rw [Circ.eval_juntaCirc]
      exact hdep j _ x (by intro t ht; simp [Finset.mem_toList, ht])
    · have hσj : σ j = Circ.const (y₀ j) := by
        simp only [hσ]; rw [if_neg hj]
      rw [hσj]
      by_cases hji : j = i
      · subst hji
        simp [nwStr, Circ.eval]
      · simp only [nwStr, Circ.eval, if_neg hj, if_neg hji]
  have hsizeσ : ∀ j : Fin m, Circ.size (σ j) ≤ 7 * 2 ^ α := by
    intro j
    have hp : (1 : ℕ) ≤ 2 ^ α := Nat.one_le_two_pow
    by_cases hj : (j : ℕ) < (i : ℕ)
    · have hji : j ≠ i := by
        intro h; rw [h] at hj; omega
      have hlen : (T j).toList.length ≤ α := by
        rw [Finset.length_toList]; exact hTcard j hji
      have hb := Circ.size_juntaCirc (fun x => f (setBlock (e i) z₀ x ∘ e j))
        (T j).toList (fun _ => false)
      have hmono : (7 : ℕ) * 2 ^ (T j).toList.length ≤ 7 * 2 ^ α :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlen)
      simp only [hσ, if_pos hj]
      omega
    · simp only [hσ, if_neg hj, Circ.size_const]
      omega
  set Acirc : Circ ℓ := Circ.subst D σ with hAc
  have hevalA : ∀ x : Fin ℓ → Bool,
      Circ.eval Acirc x = D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i)) := by
    intro x
    rw [hAc, Circ.eval_subst]
    congr 1
    funext j
    exact hevalσ j x
  have hsizeA : Circ.size Acirc ≤ D.size + m * (7 * 2 ^ α) := by
    have h1 := Circ.size_subst D σ
    rw [← hAc] at h1
    have h2 : ∑ j : Fin m, Circ.size (σ j) ≤ m * (7 * 2 ^ α) := by
      calc ∑ j : Fin m, Circ.size (σ j)
          ≤ ∑ _j : Fin m, 7 * 2 ^ α := Finset.sum_le_sum (fun j _ => hsizeσ j)
        _ = m * (7 * 2 ^ α) := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
    omega
  have hxor : ∀ a r ng : Bool, xor (xor ng (!r)) a = xor ng (a == r) := by decide
  by_cases hc : xor neg (!(y₀ i)) = true
  · refine ⟨Circ.not Acirc, ?_, ?_⟩
    · have hn := Circ.size_not Acirc
      omega
    · intro x
      have h := hxor (D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) (y₀ i) neg
      rw [hc] at h
      simp only [Circ.eval]
      rw [hevalA]
      simpa using h
  · simp only [Bool.not_eq_true] at hc
    refine ⟨Acirc, by omega, ?_⟩
    intro x
    have h := hxor (D.eval (nwStr e f i (setBlock (e i) z₀ x) y₀ (y₀ i))) (y₀ i) neg
    rw [hc] at h
    rw [hevalA]
    simpa using h

/-- If two functions have the same sums over each orbit of an involution, their total sums
agree. -/
lemma sum_eq_of_pair {β : Type*} [Fintype β] (T : β → β) (hT : Function.Involutive T)
    (F W : β → ℝ) (h : ∀ b, F b + F (T b) = W b + W (T b)) :
    ∑ b, F b = ∑ b, W b := by
  have h1 : ∑ b, F (T b) = ∑ b, F b := Equiv.sum_comp (hT.toPerm T) F
  have h2 : ∑ b, W (T b) = ∑ b, W b := Equiv.sum_comp (hT.toPerm T) W
  have h3 : ∑ b, (F b + F (T b)) = ∑ b, (W b + W (T b)) :=
    Finset.sum_congr rfl (fun b _ => h b)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at h3
  linarith

/-- The heart of the Nisan-Wigderson analysis: consecutive hybrids are close, since a
distinguisher between them yields a small circuit predicting the hard function. -/
lemma nw_hybrid_step {ℓ d m α s : ℕ} {ε : ℝ}
    (e : Fin m → (Fin ℓ ↪ Fin d))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (e i)) ∩ (Finset.univ.image (e j))).card ≤ α)
    (f : (Fin ℓ → Bool) → Bool)
    (hhard : ∀ C : Circ ℓ, C.size ≤ s →
      ((Finset.univ.filter (fun x : Fin ℓ → Bool => C.eval x = f x)).card : ℝ)
        ≤ (1 / 2 + ε / m) * 2 ^ ℓ)
    (D : Circ m) (hD : D.size + m * (7 * 2 ^ α) + 1 ≤ s) (i : Fin m) :
    |hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ)| ≤ ε / m := by
  classical
  set SB : (Fin d → Bool) → (Fin ℓ → Bool) → (Fin d → Bool) := setBlock (e i) with hSB
  set Aval : (Fin d → Bool) → (Fin m → Bool) → Bool → Bool :=
    fun z y b => D.eval (nwStr e f i z y b) with hAval
  set dfun : (Fin d → Bool) → (Fin m → Bool) → ℝ :=
    fun z y => b2r (Aval z y (f (z ∘ e i))) - b2r (Aval z y (y i)) with hdfun
  set Δ : ℝ := hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ) with hΔ
  have hpow : (0:ℝ) < 2 ^ d * 2 ^ m := by positivity
  have hΔeq : (∑ z : Fin d → Bool, ∑ y : Fin m → Bool, dfun z y) = (2 ^ d * 2 ^ m) * Δ := by
    rw [hΔ, hybAcc_succ_sub e f D i, hdfun, hAval]
    field_simp
  set flipAt : (Fin m → Bool) → (Fin m → Bool) := fun y => Function.update y i (!(y i))
    with hflipAt
  have hflip_i : ∀ y : Fin m → Bool, flipAt y i = !(y i) := by
    intro y; simp [hflipAt]
  have hflip_ne : ∀ (y : Fin m → Bool) (j : Fin m), j ≠ i → flipAt y j = y j := by
    intro y j hj; simp [hflipAt, Function.update_of_ne hj]
  have hflipinv : Function.Involutive flipAt := by
    intro y
    funext j
    by_cases hj : j = i
    · subst hj; simp [hflip_i]
    · rw [hflip_ne _ _ hj, hflip_ne _ _ hj]
  have hAflip : ∀ (z : Fin d → Bool) (y : Fin m → Bool) (b : Bool),
      Aval z (flipAt y) b = Aval z y b := by
    intro z y b
    have hs : nwStr e f i z (flipAt y) b = nwStr e f i z y b := by
      funext j
      by_cases hj : (j : ℕ) < (i : ℕ)
      · simp [nwStr, hj]
      · by_cases hji : j = i
        · simp [nwStr, hji]
        · simp [nwStr, hj, hji, hflip_ne y j hji]
    simp only [hAval, hs]
  have main : ∀ neg : Bool, (if neg then -Δ else Δ) ≤ ε / m := by
    intro neg
    set sgn : ℝ := if neg then -1 else 1 with hsgn
    set Fcorr : (Fin d → Bool) → (Fin ℓ → Bool) → (Fin m → Bool) → ℝ :=
      fun z x y => agree (xor neg ((Aval (SB z x) y (y i)) == y i)) (f x) with hFcorr
    -- averaging over the random bit in position `i`
    have hS1 : ∀ (z : Fin d → Bool) (x : Fin ℓ → Bool),
        ∑ y : Fin m → Bool, Fcorr z x y
          = ∑ y : Fin m → Bool, (1 / 2 + sgn * dfun (SB z x) y) := by
      intro z x
      refine sum_eq_of_pair flipAt hflipinv _ _ ?_
      intro y
      have hfx : f (SB z x ∘ e i) = f x := by rw [hSB, setBlock_comp]
      have hcond : ∀ b : Bool,
          cond b (Aval (SB z x) y true) (Aval (SB z x) y false) = Aval (SB z x) y b := by
        intro b; cases b <;> rfl
      have e1 : Fcorr z x y
          = agree (xor neg ((cond (y i) (Aval (SB z x) y true) (Aval (SB z x) y false)) == y i))
              (f x) := by
        simp only [hFcorr, hcond]
      have e2 : Fcorr z x (flipAt y)
          = agree (xor neg
              ((cond (!(y i)) (Aval (SB z x) y true) (Aval (SB z x) y false)) == !(y i)))
              (f x) := by
        simp only [hFcorr, hflip_i, hAflip, hcond]
      have e3 : dfun (SB z x) y
          = b2r (cond (f x) (Aval (SB z x) y true) (Aval (SB z x) y false))
            - b2r (cond (y i) (Aval (SB z x) y true) (Aval (SB z x) y false)) := by
        simp only [hdfun, hfx, hcond]
      have e4 : dfun (SB z x) (flipAt y)
          = b2r (cond (f x) (Aval (SB z x) y true) (Aval (SB z x) y false))
            - b2r (cond (!(y i)) (Aval (SB z x) y true) (Aval (SB z x) y false)) := by
        simp only [hdfun, hfx, hflip_i, hAflip, hcond]
      rw [e1, e2, e3, e4, hsgn]
      linear_combination nw_pair_identity (Aval (SB z x) y false) (Aval (SB z x) y true)
        (y i) (f x) neg
    -- summing over the fixed part of the seed and the remaining random bits
    have hstep1 : ∀ (z : Fin d → Bool) (x : Fin ℓ → Bool),
        ∑ y : Fin m → Bool, Fcorr z x y
          = 2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y) := by
      intro z x
      rw [hS1 z x, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcm]
    have hK : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y
        = 2 ^ d * 2 ^ ℓ * 2 ^ m * (1 / 2) + sgn * (2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ)) := by
      have hc1 : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y
          = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
              (2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y)) :=
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun x _ => hstep1 z x))
      rw [hc1]
      have hc2 : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
            (2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y))
          = (∑ _z : Fin d → Bool, ∑ _x : Fin ℓ → Bool, (2:ℝ) ^ m * (1 / 2))
            + sgn * (∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
                (∑ y : Fin m → Bool, dfun (SB z x) y)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hc2]
      have hc3 : (∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
            (∑ y : Fin m → Bool, dfun (SB z x) y))
          = 2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ) := by
        rw [hSB]
        rw [sum_setBlock (e i) (fun z' => ∑ y : Fin m → Bool, dfun z' y), hΔeq]
      rw [hc3]
      congr 1
      have hcd : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
      have hcl : ((Fintype.card (Fin ℓ → Bool) : ℕ) : ℝ) = 2 ^ ℓ := by simp
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
        nsmul_eq_mul, nsmul_eq_mul, hcd, hcl]
      ring
    -- an averaging argument fixes the seed outside block `i` and the remaining random bits
    have hpig : ∃ (z₀ : Fin d → Bool) (y₀ : Fin m → Bool),
        2 ^ ℓ * (1 / 2 + sgn * Δ) ≤ ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀ := by
      by_contra hcon
      push_neg at hcon
      have hlt : ∑ z : Fin d → Bool, ∑ y : Fin m → Bool, ∑ x : Fin ℓ → Bool, Fcorr z x y
          < ∑ _z : Fin d → Bool, ∑ _y : Fin m → Bool, (2:ℝ) ^ ℓ * (1 / 2 + sgn * Δ) := by
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun z _ => ?_)
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hcon z y)
      have hswap : ∑ z : Fin d → Bool, ∑ y : Fin m → Bool, ∑ x : Fin ℓ → Bool, Fcorr z x y
          = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y :=
        Finset.sum_congr rfl (fun z _ => Finset.sum_comm)
      have hrhs : (∑ _z : Fin d → Bool, ∑ _y : Fin m → Bool, (2:ℝ) ^ ℓ * (1 / 2 + sgn * Δ))
          = 2 ^ d * 2 ^ ℓ * 2 ^ m * (1 / 2) + sgn * (2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ)) := by
        have hcd : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
        have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul, hcd, hcm]
        ring
      rw [hswap, hK, hrhs] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨z₀, y₀, hz⟩ := hpig
    obtain ⟨C, hCsize, hCeval⟩ := nw_predictor_circuit e hdesign f D i z₀ y₀ neg
    have hcard : ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀
        = ((Finset.univ.filter (fun x : Fin ℓ → Bool => C.eval x = f x)).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hCeval x]
      simp only [hFcorr, agree, hAval, hSB]
    have hle : ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀ ≤ (1 / 2 + ε / m) * 2 ^ ℓ := by
      rw [hcard]
      exact hhard C (by omega)
    have hfin : 2 ^ ℓ * (1 / 2 + sgn * Δ) ≤ (1 / 2 + ε / m) * 2 ^ ℓ := le_trans hz hle
    have h2l : (0:ℝ) < 2 ^ ℓ := by positivity
    rw [mul_comm ((2:ℝ) ^ ℓ)] at hfin
    have h3 : (1 / 2 + sgn * Δ) ≤ (1 / 2 + ε / m) := le_of_mul_le_mul_right hfin h2l
    have h4 : sgn * Δ ≤ ε / m := by linarith
    rw [hsgn] at h4
    cases neg
    · norm_num at h4 ⊢
      linarith
    · norm_num at h4 ⊢
      linarith
  rw [abs_le]
  constructor
  · have h := main true
    norm_num at h
    linarith
  · have h := main false
    norm_num at h
    linarith

/-- **The Nisan-Wigderson pseudorandom generator.**

Let `e 0, …, e (m-1)` be a combinatorial design: `m` blocks of `ℓ` coordinates inside a seed of
`d` coordinates, any two of which intersect in at most `α` positions.  Let `f` be a Boolean
function on `ℓ` bits which is average-case hard, in the sense that no circuit of size at most
`s` agrees with `f` on more than a `1/2 + ε/m` fraction of the inputs.

Then the Nisan-Wigderson generator `z ↦ (f (z ∘ e 0), …, f (z ∘ e (m-1)))`, stretching `d`
random bits to `m` bits, fools every circuit `D` of size at most `s - m · 7 · 2 ^ α - 1`: the
acceptance probabilities of `D` on the output of the generator and on a uniformly random
`m`-bit string differ by at most `ε`. -/
theorem nisan_wigderson_prg {ℓ d m α s : ℕ} {ε : ℝ} (hm : 0 < m)
    (e : Fin m → (Fin ℓ ↪ Fin d))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (e i)) ∩ (Finset.univ.image (e j))).card ≤ α)
    (f : (Fin ℓ → Bool) → Bool)
    (hhard : ∀ C : Circ ℓ, C.size ≤ s →
      ((Finset.univ.filter (fun x : Fin ℓ → Bool => C.eval x = f x)).card : ℝ)
        ≤ (1 / 2 + ε / m) * 2 ^ ℓ)
    (D : Circ m) (hD : D.size + m * (7 * 2 ^ α) + 1 ≤ s) :
    |(∑ z : Fin d → Bool, b2r (D.eval (fun i => f (z ∘ e i)))) / 2 ^ d
        - (∑ y : Fin m → Bool, b2r (D.eval y)) / 2 ^ m| ≤ ε := by
  rw [← hybAcc_zero e f D, ← hybAcc_top e f D]
  have htel : hybAcc e f D m - hybAcc e f D 0
      = ∑ i ∈ Finset.range m, (hybAcc e f D (i + 1) - hybAcc e f D i) :=
    (Finset.sum_range_sub (fun i => hybAcc e f D i) m).symm
  rw [htel]
  calc |∑ i ∈ Finset.range m, (hybAcc e f D (i + 1) - hybAcc e f D i)|
      ≤ ∑ i ∈ Finset.range m, |hybAcc e f D (i + 1) - hybAcc e f D i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, ε / m := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hi' : i < m := Finset.mem_range.1 hi
        simpa using nw_hybrid_step e hdesign f hhard D hD ⟨i, hi'⟩
    _ = ε := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

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


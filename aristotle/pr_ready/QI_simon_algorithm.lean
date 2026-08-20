/-!
# Simon Algorithm
Category: External
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace QI

/-! ## Basic setup: the group `(ZMod 2)^n` -/

/-- The domain of Simon's problem: bit strings of length `n`, viewed as the
elementary abelian group `(ZMod 2)^n` under bitwise XOR (= addition). -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

@[simp] lemma vec_add_self (x : Vec n) : x + x = 0 := by
  funext i; exact zmod2_add_self _

@[simp] lemma vec_add_add_cancel (x s : Vec n) : x + s + s = x := by
  rw [add_assoc, vec_add_self, add_zero]

lemma vec_eq_iff_add {x y s : Vec n} : x + y = s ↔ y = x + s := by
  constructor
  · intro h; rw [← h, ← add_assoc, vec_add_self, zero_add]
  · intro h; rw [h, ← add_assoc, vec_add_self, zero_add]

lemma vec_shift {x y s : Vec n} (h : x + s = y) : x = y + s := by
  rw [← h, vec_add_add_cancel]

/-- The `ZMod 2`-valued inner product. -/
def dot (x y : Vec n) : ZMod 2 := ∑ i, x i * y i

lemma dot_add_left (x y z : Vec n) : dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-! ## The Simon promise -/

/-- `f` is a Simon function with secret `s`: `s ≠ 0` and `f x = f y` exactly when
`x = y` or `x ⊕ y = s`. Equivalently, `f` is two-to-one with period `s`. -/
def IsSimon {Y : Type*} (s : Vec n) (f : Vec n → Y) : Prop :=
  s ≠ 0 ∧ ∀ x y : Vec n, f x = f y ↔ (x = y ∨ x + y = s)

lemma IsSimon.period {Y : Type*} {s : Vec n} {f : Vec n → Y} (h : IsSimon s f)
    (x : Vec n) : f (x + s) = f x := by
  refine (h.2 _ _).2 (Or.inr ?_)
  rw [add_comm x s, add_assoc, vec_add_self, add_zero]

/-! ## Quantum part: one query of Simon's algorithm -/

/-- The character `(-1)^a` of `ZMod 2`. -/
noncomputable def chi (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

lemma chi_ne_zero (a : ZMod 2) : chi a ≠ 0 := by
  rcases zmod2_cases a with h | h <;> simp [chi, h]

@[simp] lemma chi_zero : chi 0 = 1 := by simp [chi]

@[simp] lemma chi_one : chi 1 = -1 := by simp [chi]

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    simp [ha, hb, h]

/-- The amplitude of the basis state `|y⟩|z⟩` in the state
`(1/2^n) ∑_{x,y} (-1)^{x·y} |y⟩|f(x)⟩`, i.e. the state obtained from `|0⟩|0⟩` by
Hadamard transforming the first register, applying one oracle query to `f`, and
Hadamard transforming the first register again. -/
noncomputable def amp {Y : Type*} [DecidableEq Y] (f : Vec n → Y) (y : Vec n) (z : Y) : ℂ :=
  (1 / 2 ^ n) * ∑ x : Vec n, chi (dot x y) * (if f x = z then 1 else 0)

/-- **Simon's interference identity.** If `y` is not orthogonal to the secret `s`,
then the amplitude of every outcome `(y, z)` vanishes: the measurement of the first
register always returns a vector orthogonal to `s`. -/
theorem amp_eq_zero_of_dot_ne_zero {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) {y : Vec n} (hy : dot s y ≠ 0) (z : Y) : amp f y z = 0 := by
  have key : ∑ x : Vec n, chi (dot x y) * (if f x = z then (1 : ℂ) else 0) = 0 := by
    set F : Vec n → ℂ := fun x => chi (dot x y) * (if f x = z then (1 : ℂ) else 0) with hF
    have hshift : ∑ x : Vec n, F (x + s) = ∑ x : Vec n, F x :=
      Fintype.sum_equiv (Equiv.addRight s) (fun x => F (x + s)) F (fun _ => rfl)
    have hneg : ∀ x : Vec n, F (x + s) = -F x := by
      intro x
      have h1 : chi (dot (x + s) y) = -chi (dot x y) := by
        rw [dot_add_left, chi_add, show chi (dot s y) = -1 by simp [chi, hy]]
        ring
      have h2 : f (x + s) = f x := h.period x
      simp only [hF, h1, h2]
      ring
    have h2 : ∑ x : Vec n, F x = -∑ x : Vec n, F x := by
      calc ∑ x : Vec n, F x = ∑ x : Vec n, F (x + s) := hshift.symm
        _ = ∑ x : Vec n, -F x := Finset.sum_congr rfl fun x _ => hneg x
        _ = -∑ x : Vec n, F x := by rw [Finset.sum_neg_distrib]
    have h4 : ∑ x : Vec n, F x + ∑ x : Vec n, F x = 0 := add_eq_zero_iff_eq_neg.mpr h2
    have h5 : (2 : ℂ) * ∑ x : Vec n, F x = 0 := by rw [two_mul]; exact h4
    simpa using h5
  rw [amp, key, mul_zero]

/-- If `y` is orthogonal to the secret, the amplitude of `(y, f x₀)` is
`2·(-1)^{x₀·y}/2^n`; in particular it is nonzero, so every `y ⊥ s` is a possible
measurement outcome. -/
theorem amp_of_dot_eq_zero {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) {y : Vec n} (hy : dot s y = 0) (x₀ : Vec n) :
    amp f y (f x₀) = (1 / 2 ^ n) * (2 * chi (dot x₀ y)) := by
  classical
  have hne : x₀ ≠ x₀ + s := by
    intro e
    apply h.1
    have h5 : x₀ + x₀ = s := vec_eq_iff_add.mpr e
    rw [vec_add_self] at h5
    exact h5.symm
  have hfib : ∀ x : Vec n, chi (dot x y) * (if f x = f x₀ then (1 : ℂ) else 0)
      = if x ∈ ({x₀, x₀ + s} : Finset (Vec n)) then chi (dot x y) else 0 := by
    intro x
    by_cases hx : f x = f x₀
    · rcases (h.2 x x₀).1 hx with h1 | h1
      · simp [h1]
      · have h2 : x = x₀ + s := vec_eq_iff_add.mp (by rw [add_comm]; exact h1)
        rw [if_pos hx, if_pos (show x ∈ ({x₀, x₀ + s} : Finset (Vec n)) by simp [h2]), mul_one]
    · have hx1 : x ≠ x₀ := fun e => hx (by rw [e])
      have hx2 : x ≠ x₀ + s := by
        intro e
        exact hx (by rw [e]; exact h.period x₀)
      simp [hx, hx1, hx2]
  have hsum : ∑ x : Vec n, chi (dot x y) * (if f x = f x₀ then (1 : ℂ) else 0)
      = 2 * chi (dot x₀ y) := by
    simp only [hfib]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
    rw [dot_add_left, chi_add, show chi (dot s y) = 1 by simp [chi, hy]]
    ring
  rw [amp, hsum]

/-! ### `n - 1` well chosen outcomes determine the secret -/

/-- The vectors used in the analysis: for `i ≠ j` (where `s j = 1`),
`simonBasis s j i = e_i + s_i · e_j` is orthogonal to `s`. -/
def simonBasis (s : Vec n) (j i : Fin n) : Vec n :=
  fun k => (if k = i then 1 else 0) + (if k = j then s i else 0)

lemma dot_simonBasis (t s : Vec n) (j i : Fin n) :
    dot t (simonBasis s j i) = t i + t j * s i := by
  simp only [dot, simonBasis, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;> simp

lemma dot_simonBasis_self {s : Vec n} {j : Fin n} (hj : s j = 1) (i : Fin n) :
    dot s (simonBasis s j i) = 0 := by
  rw [dot_simonBasis, hj, one_mul, zmod2_add_self]

/-- **Quantum upper bound (query count).** For any Simon function with secret `s`
there are `n - 1` measurement outcomes, each occurring with nonzero amplitude, whose
orthogonality constraints pin down `s` uniquely among nonzero vectors. Hence `n - 1`
quantum queries suffice to determine `s`. -/
theorem quantum_upper_bound {Y : Type*} [DecidableEq Y] {s : Vec n} {f : Vec n → Y}
    (h : IsSimon s f) :
    ∃ B : Finset (Vec n), B.card = n - 1 ∧
      (∀ y ∈ B, ∃ z : Y, amp f y z ≠ 0) ∧
      (∀ t : Vec n, (∀ y ∈ B, dot t y = 0) → t = 0 ∨ t = s) := by
  obtain ⟨j, hj0⟩ : ∃ j, s j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h.1 (funext hc)
  have hj : s j = 1 := (zmod2_cases (s j)).resolve_left hj0
  classical
  refine ⟨(Finset.univ.erase j).image (simonBasis s j), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    intro a ha b _ hab
    have h1 : simonBasis s j a a = simonBasis s j b a := by rw [hab]
    have haj : a ≠ j := Finset.ne_of_mem_erase (Finset.mem_coe.mp ha)
    by_contra hne
    simp [simonBasis, haj, hne] at h1
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, _, rfl⟩ := hy
    refine ⟨f 0, ?_⟩
    rw [amp_of_dot_eq_zero h (dot_simonBasis_self hj i) 0]
    have h1 := chi_ne_zero (dot (0 : Vec n) (simonBasis s j i))
    have h2 : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
    exact mul_ne_zero (one_div_ne_zero h2) (mul_ne_zero two_ne_zero h1)
  · intro t ht
    have key : ∀ i, i ≠ j → t i = t j * s i := by
      intro i hi
      have hd := ht (simonBasis s j i)
        (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩))
      rw [dot_simonBasis] at hd
      have h3 : t i + (t j * s i + t j * s i) = t j * s i := by
        rw [← add_assoc, hd, zero_add]
      rwa [zmod2_add_self, add_zero] at h3
    rcases zmod2_cases (t j) with h0 | h1
    · left
      funext k
      by_cases hk : k = j
      · simp [hk, h0]
      · simp [key k hk, h0]
    · right
      funext k
      by_cases hk : k = j
      · simp [hk, h1, hj]
      · simp [key k hk, h1]

/-! ## Classical part: deterministic decision trees -/

/-- A deterministic classical query algorithm: a decision tree whose internal nodes
query the oracle at a point of `Vec n` and branch on the (natural number) answer,
and whose leaves output a candidate secret. -/
inductive DTree (n : ℕ) : Type
  | leaf (out : Vec n) : DTree n
  | node (q : Vec n) (k : ℕ → DTree n) : DTree n

namespace DTree

/-- The output of the tree on the oracle `f`. -/
def run (f : Vec n → ℕ) : DTree n → Vec n
  | .leaf out => out
  | .node q k => run f (k (f q))

/-- The set of points queried along the computation path on the oracle `f`. -/
def queries (f : Vec n → ℕ) : DTree n → Finset (Vec n)
  | .leaf _ => ∅
  | .node q k => insert q (queries f (k (f q)))

/-- `DepthLE T d` says every computation path of `T` makes at most `d` queries. -/
inductive DepthLE : DTree n → ℕ → Prop
  | leaf (out : Vec n) (d : ℕ) : DepthLE (.leaf out) d
  | node (q : Vec n) (k : ℕ → DTree n) (d : ℕ) (h : ∀ m, DepthLE (k m) d) :
      DepthLE (.node q k) (d + 1)

lemma card_queries_le {T : DTree n} {d : ℕ} (hd : DepthLE T d) (f : Vec n → ℕ) :
    (T.queries f).card ≤ d := by
  induction hd with
  | leaf out d => simp [queries]
  | node q k d h ih =>
      have hle := ih (f q)
      calc (queries f (.node q k)).card
          ≤ (queries f (k (f q))).card + 1 := by
            simpa [queries] using Finset.card_insert_le q (queries f (k (f q)))
        _ ≤ d + 1 := by omega

/-- If two oracles agree on all points queried along the path of the first, the tree
behaves identically on both. -/
lemma run_congr (T : DTree n) (f g : Vec n → ℕ) (h : ∀ x ∈ T.queries f, f x = g x) :
    T.run g = T.run f ∧ T.queries g = T.queries f := by
  induction T with
  | leaf out => simp [run, queries]
  | node q k ih =>
      have hq : f q = g q := h q (by simp [queries])
      have h' : ∀ x ∈ (k (f q)).queries f, f x = g x := by
        intro x hx
        exact h x (by simp [queries, hx])
      obtain ⟨h1, h2⟩ := ih (f q) h'
      constructor
      · show run g (k (g q)) = run f (k (f q))
        rw [← hq]; exact h1
      · show insert q ((k (g q)).queries g) = insert q ((k (f q)).queries f)
        rw [← hq, h2]

end DTree

/-! ### The adversary function -/

/-- A fixed injective encoding of `Vec n` into `ℕ`. -/
noncomputable def enc (x : Vec n) : ℕ := ((Fintype.equivFin (Vec n)) x : ℕ)

lemma enc_injective : Function.Injective (enc : Vec n → ℕ) := by
  intro a b hab
  exact (Fintype.equivFin (Vec n)).injective (Fin.val_injective hab)

lemma enc_lt (x : Vec n) : enc x < Fintype.card (Vec n) := (Fintype.equivFin (Vec n) x).isLt

/-- Given a finite set `S` of already-queried points, no two of which differ by `s`,
this is a Simon function with secret `s` whose values on `S` are the reference
values `enc`. -/
noncomputable def advFn (S : Finset (Vec n)) (s : Vec n) : Vec n → ℕ := fun x =>
  if x ∈ S then enc x
  else if x + s ∈ S then enc (x + s)
  else Fintype.card (Vec n) + enc (if enc x ≤ enc (x + s) then x else x + s)

lemma advFn_agree {S : Finset (Vec n)} {s : Vec n} {x : Vec n} (hx : x ∈ S) :
    advFn S s x = enc x := by
  classical
  simp [advFn, hx]

lemma advFn_isSimon {S : Finset (Vec n)} {s : Vec n} (hs : s ≠ 0)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ s) : IsSimon s (advFn S s) := by
  classical
  have hne : ∀ x : Vec n, x ≠ x + s := by
    intro x e
    apply hs
    have h5 : x + x = s := vec_eq_iff_add.mpr e
    rw [vec_add_self] at h5
    exact h5.symm
  have hnotboth : ∀ x : Vec n, x ∈ S → x + s ∉ S := by
    intro x hx hxs
    exact hS x hx (x + s) hxs (hne x) (by rw [← add_assoc, vec_add_self, zero_add])
  set rep : Vec n → Vec n := fun x => if enc x ≤ enc (x + s) then x else x + s with hrep
  have hrep_mem : ∀ x : Vec n, rep x = x ∨ rep x = x + s := by
    intro x; by_cases hc : enc x ≤ enc (x + s) <;> simp [hrep, hc]
  have hrep_shift : ∀ x : Vec n, rep (x + s) = rep x := by
    intro x
    have hxx : enc x ≠ enc (x + s) := fun e => hne x (enc_injective e)
    have hxx' : enc x < enc (x + s) ∨ enc (x + s) < enc x := by omega
    by_cases hc : enc x ≤ enc (x + s)
    · have hc' : ¬ enc (x + s) ≤ enc x := by omega
      simp [hrep, hc, hc', vec_add_add_cancel]
    · have hc' : enc (x + s) ≤ enc x := by omega
      simp [hrep, hc, hc', vec_add_add_cancel]
  have hsmall : ∀ x : Vec n, (x ∈ S ∨ x + s ∈ S) →
      ∃ w ∈ S, (w = x ∨ w = x + s) ∧ advFn S s x = enc w := by
    intro x hx
    by_cases h1 : x ∈ S
    · exact ⟨x, h1, Or.inl rfl, by simp [advFn, h1]⟩
    · have h2 : x + s ∈ S := hx.resolve_left h1
      exact ⟨x + s, h2, Or.inr rfl, by simp [advFn, h1, h2]⟩
  have hbig : ∀ x : Vec n, x ∉ S → x + s ∉ S →
      advFn S s x = Fintype.card (Vec n) + enc (rep x) := by
    intro x h1 h2; simp [advFn, h1, h2, hrep]
  have hfin : ∀ a b : Vec n, (a = b ∨ a = b + s) → (a = b ∨ a + b = s) := by
    intro a b hab
    rcases hab with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [add_comm]; exact vec_eq_iff_add.mpr h)
  refine ⟨hs, ?_⟩
  intro x y
  constructor
  · intro hxy
    refine hfin x y ?_
    by_cases hx : x ∈ S ∨ x + s ∈ S
    · obtain ⟨w, _, hw, hwv⟩ := hsmall x hx
      by_cases hy : y ∈ S ∨ y + s ∈ S
      · obtain ⟨w', _, hw', hw'v⟩ := hsmall y hy
        have hww : w = w' := enc_injective (by rw [← hwv, ← hw'v, hxy])
        subst hww
        rcases hw with h1 | h1 <;> rcases hw' with h2 | h2
        · exact Or.inl (h1 ▸ h2)
        · exact Or.inr (h1 ▸ h2)
        · exact Or.inr (vec_shift (h1 ▸ h2))
        · exact Or.inl (add_right_cancel (h1 ▸ h2 : x + s = y + s))
      · push_neg at hy
        have hyv := hbig y hy.1 hy.2
        rw [hwv, hyv] at hxy
        exact absurd hxy (by have := enc_lt w; omega)
    · push_neg at hx
      have hxv := hbig x hx.1 hx.2
      by_cases hy : y ∈ S ∨ y + s ∈ S
      · obtain ⟨w', _, _, hw'v⟩ := hsmall y hy
        rw [hxv, hw'v] at hxy
        exact absurd hxy (by have := enc_lt w'; omega)
      · push_neg at hy
        have hyv := hbig y hy.1 hy.2
        rw [hxv, hyv] at hxy
        have hrr : rep x = rep y := enc_injective (by omega)
        rcases hrep_mem x with h1 | h1 <;> rcases hrep_mem y with h2 | h2
        · exact Or.inl (by rw [← h1, hrr, h2])
        · exact Or.inr (by rw [← h1, hrr, h2])
        · exact Or.inr (vec_shift (by rw [← h1, hrr, h2]))
        · exact Or.inl (add_right_cancel (by rw [← h1, hrr, h2] : x + s = y + s))
  · intro hxy
    rcases hxy with rfl | hxy
    · rfl
    · have hy : y = x + s := vec_eq_iff_add.mp hxy
      subst hy
      by_cases h1 : x ∈ S
      · have h2 : x + s ∉ S := hnotboth x h1
        have h3 : x + s + s ∈ S := by rwa [vec_add_add_cancel]
        simp [advFn, h1, h2, vec_add_add_cancel]
      · by_cases h2 : x + s ∈ S
        · simp [advFn, h1, h2]
        · have h3 : x + s + s ∉ S := by rwa [vec_add_add_cancel]
          rw [hbig (x + s) h2 h3, hbig x h1 h2, hrep_shift x]

/-! ### The classical lower bound -/

lemma card_vec (n : ℕ) : Fintype.card (Vec n) = 2 ^ n := by
  simp

/-- **Classical lower bound.** Any deterministic classical algorithm that solves
Simon's problem for all Simon functions with `n ≥ 2` must make at least
`2 ^ ((n-1)/2)` queries on some computation path. -/
theorem classical_lower_bound (hn : 2 ≤ n) (T : DTree n) (d : ℕ) (hd : DTree.DepthLE T d)
    (hcorrect : ∀ (s : Vec n) (f : Vec n → ℕ), IsSimon s f → T.run f = s) :
    2 ^ ((n - 1) / 2) ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  set S : Finset (Vec n) := T.queries enc with hSdef
  have hcard : S.card ≤ d := DTree.card_queries_le hd enc
  set D : Finset (Vec n) :=
    insert 0 (insert (T.run enc) ((S ×ˢ S).image (fun p => p.1 + p.2))) with hD
  have hDcard : D.card ≤ d * d + 2 := by
    have h1 : ((S ×ˢ S).image (fun p : Vec n × Vec n => p.1 + p.2)).card ≤ d * d := by
      refine le_trans Finset.card_image_le ?_
      rw [Finset.card_product]
      exact Nat.mul_le_mul hcard hcard
    calc D.card ≤ (insert (T.run enc) ((S ×ˢ S).image (fun p => p.1 + p.2))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (((S ×ˢ S).image (fun p => p.1 + p.2)).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ d * d + 2 := by omega
  have hlt2 : d * d + 2 < 2 ^ n := by
    have h1 : d + 1 ≤ 2 ^ ((n - 1) / 2) := hlt
    have h3 : (2 : ℕ) ^ ((n - 1) / 2) * 2 ^ ((n - 1) / 2) ≤ 2 ^ (n - 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h5 : (2 : ℕ) ^ 1 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : (d + 1) * (d + 1) ≤ 2 ^ (n - 1) := le_trans (Nat.mul_le_mul h1 h1) h3
    rw [h4]
    nlinarith [h6, h5]
  have hDlt : D.card < Fintype.card (Vec n) := by
    rw [card_vec]; omega
  obtain ⟨s, hs⟩ : ∃ s : Vec n, s ∉ D := by
    by_contra hc
    push_neg at hc
    have hu : D = Finset.univ := Finset.eq_univ_of_forall hc
    rw [hu, Finset.card_univ] at hDlt
    exact lt_irrefl _ hDlt
  have hs0 : s ≠ 0 := by
    intro e; exact hs (by rw [e, hD]; exact Finset.mem_insert_self _ _)
  have hsout : s ≠ T.run enc := by
    intro e
    exact hs (by rw [e, hD]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hSsum : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ≠ s := by
    intro x hx y hy _ e
    refine hs ?_
    rw [hD]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, e⟩
  have hsimon : IsSimon s (advFn S s) := advFn_isSimon hs0 hSsum
  have hagree : ∀ x ∈ T.queries enc, enc x = advFn S s x := by
    intro x hx
    exact (advFn_agree (S := S) (s := s) (hSdef ▸ hx)).symm
  have hrun : T.run (advFn S s) = T.run enc := (T.run_congr enc (advFn S s) hagree).1
  exact hsout (by rw [← hcorrect s _ hsimon, hrun])

/-! ## Main theorem -/

/-- **Simon's problem.**

*Quantum upper bound*: for every Simon function `f` with secret `s` (over `n ≥ 2`
bits) there are `n - 1` outcomes `y`, each of which occurs with nonzero amplitude in
the state produced by a single quantum query (`amp`), such that `s` is the unique
nonzero vector orthogonal to all of them.  So `O(n)` quantum queries determine `s`.

*Classical lower bound*: every deterministic classical query algorithm (decision
tree) that outputs the secret of every Simon function must make at least
`2 ^ ((n-1)/2) = Ω(2^{n/2})` queries. -/
theorem simon_algorithm (n : ℕ) (hn : 2 ≤ n) :
    (∀ (s : Vec n) (f : Vec n → Vec n), IsSimon s f →
        ∃ B : Finset (Vec n), B.card = n - 1 ∧
          (∀ y ∈ B, ∃ z : Vec n, amp f y z ≠ 0) ∧
          (∀ t : Vec n, (∀ y ∈ B, dot t y = 0) → t = 0 ∨ t = s)) ∧
    (∀ (T : DTree n) (d : ℕ), DTree.DepthLE T d →
        (∀ (s : Vec n) (f : Vec n → ℕ), IsSimon s f → T.run f = s) →
        2 ^ ((n - 1) / 2) ≤ d) :=
  ⟨fun _ _ hf => quantum_upper_bound hf, fun T d hd hc => classical_lower_bound hn T d hd hc⟩

end QI


import RequestProject.Basic

/-!
# Unbounded fan-in Boolean circuits, the class `AC⁰`, and `PARITY`

A `Circuit n` is a Boolean circuit on `n` inputs built from constants, input
variables, negations, and *unbounded fan-in* `AND`/`OR` gates.

* `Circuit.depth` counts the maximal number of `AND`/`OR` gates on a root-to-leaf
  path (negations are free, as is standard for `AC⁰`).
* `Circuit.size` counts the number of `AND`/`OR` gates.

`InAC0 f` says that the family `f` is computed by circuits of some fixed depth and
polynomial size.  Making negations free and not counting them in the size only
makes the class larger, hence the lower bound proved later stronger.
-/

namespace CS

/-- Boolean circuits with unbounded fan-in `AND`/`OR` gates. -/
inductive Circuit (n : ℕ) where
  | const : Bool → Circuit n
  | var : Fin n → Circuit n
  | neg : Circuit n → Circuit n
  | or : (m : ℕ) → (Fin m → Circuit n) → Circuit n
  | and : (m : ℕ) → (Fin m → Circuit n) → Circuit n

namespace Circuit

/-- The Boolean function computed by a circuit. -/
def eval {n : ℕ} : Circuit n → Bits n → Bool
  | const b, _ => b
  | var i, x => x i
  | neg c, x => !(eval c x)
  | or _ f, x => decide (∃ i, eval (f i) x = true)
  | and _ f, x => decide (∀ i, eval (f i) x = true)

/-- The depth of a circuit: the maximal number of `AND`/`OR` gates on a path. -/
def depth {n : ℕ} : Circuit n → ℕ
  | const _ => 0
  | var _ => 0
  | neg c => depth c
  | or _ f => 1 + Finset.univ.sup (fun i => depth (f i))
  | and _ f => 1 + Finset.univ.sup (fun i => depth (f i))

/-- The size of a circuit: the number of `AND`/`OR` gates. -/
def size {n : ℕ} : Circuit n → ℕ
  | const _ => 0
  | var _ => 0
  | neg c => size c
  | or _ f => 1 + ∑ i, size (f i)
  | and _ f => 1 + ∑ i, size (f i)

@[simp] lemma eval_const {n : ℕ} (b : Bool) (x : Bits n) : (const b).eval x = b := rfl
@[simp] lemma eval_var {n : ℕ} (i : Fin n) (x : Bits n) : (var i).eval x = x i := rfl
@[simp] lemma eval_neg {n : ℕ} (c : Circuit n) (x : Bits n) : (neg c).eval x = !(c.eval x) := rfl
@[simp] lemma eval_or {n m : ℕ} (f : Fin m → Circuit n) (x : Bits n) :
    (or m f).eval x = decide (∃ i, (f i).eval x = true) := rfl
@[simp] lemma eval_and {n m : ℕ} (f : Fin m → Circuit n) (x : Bits n) :
    (and m f).eval x = decide (∀ i, (f i).eval x = true) := rfl

@[simp] lemma depth_const {n : ℕ} (b : Bool) : (const b : Circuit n).depth = 0 := rfl
@[simp] lemma depth_var {n : ℕ} (i : Fin n) : (var i).depth = 0 := rfl
@[simp] lemma size_const {n : ℕ} (b : Bool) : (const b : Circuit n).size = 0 := rfl
@[simp] lemma size_var {n : ℕ} (i : Fin n) : (var i).size = 0 := rfl
@[simp] lemma depth_neg {n : ℕ} (c : Circuit n) : (neg c).depth = c.depth := rfl
@[simp] lemma depth_or {n m : ℕ} (f : Fin m → Circuit n) :
    (or m f).depth = 1 + Finset.univ.sup (fun i => (f i).depth) := rfl
@[simp] lemma depth_and {n m : ℕ} (f : Fin m → Circuit n) :
    (and m f).depth = 1 + Finset.univ.sup (fun i => (f i).depth) := rfl
@[simp] lemma size_neg {n : ℕ} (c : Circuit n) : (neg c).size = c.size := rfl
@[simp] lemma size_or {n m : ℕ} (f : Fin m → Circuit n) :
    (or m f).size = 1 + ∑ i, (f i).size := rfl
@[simp] lemma size_and {n m : ℕ} (f : Fin m → Circuit n) :
    (and m f).size = 1 + ∑ i, (f i).size := rfl

end Circuit

/-- A family of Boolean functions is in `AC⁰` when it is computed by circuits of
bounded depth and polynomial size. -/
def InAC0 (f : (n : ℕ) → Bits n → Bool) : Prop :=
  ∃ d c : ℕ, ∀ n : ℕ, ∃ C : Circuit n, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧
    ∀ x, C.eval x = f n x

/-- The parity function. -/
def parity (n : ℕ) (x : Bits n) : Bool :=
  decide (Odd ((Finset.univ.filter (fun i => x i = true)).card))

lemma prod_sgn_eq {n : ℕ} (x : Bits n) (s : Finset (Fin n)) :
    (∏ i ∈ s, sgn (x i)) = (-1 : ZMod 3) ^ ((s.filter (fun i => x i = true)).card) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.filter_insert]
      by_cases hxa : x a = true
      · have : a ∉ s.filter (fun i => x i = true) := fun h => ha (Finset.mem_filter.1 h).1
        rw [if_pos hxa, Finset.card_insert_of_notMem this]
        simp [sgn, hxa]
        ring
      · have hxa' : x a = false := by simpa using hxa
        rw [if_neg hxa]
        simp [sgn, hxa']

/-- The `±1`-encoding of parity is the full monomial. -/
lemma mon_univ_eq_sgn_parity {n : ℕ} (x : Bits n) :
    mon (Finset.univ : Finset (Fin n)) x = sgn (parity n x) := by
  classical
  rw [mon, prod_sgn_eq]
  by_cases h : Odd ((Finset.univ.filter (fun i => x i = true)).card)
  · rw [h.neg_one_pow]
    simp [parity, h, sgn]
  · rw [(Nat.not_odd_iff_even.1 h).neg_one_pow]
    simp [parity, h, sgn]

end CS

import RequestProject.Circuit

/-!
# Razborov's approximation of `AC⁰` circuits by low degree `ZMod 3` polynomials

The main result of this file is `CS.exists_approx`: every circuit `C` of depth `d`
and size `s` admits a function `f` in `Deg n ((2ℓ)^d)` (i.e. a polynomial of degree
at most `(2ℓ)^d` over `ZMod 3`, in the `±1` encoding of the cube) which is `0/1`
valued and disagrees with `C` on at most `s * 2^n / 3^ℓ` inputs.
-/

namespace CS

open Finset

section ZMod3

lemma ZMod3.sq_eq_one_of_ne_zero {a : ZMod 3} (h : a ≠ 0) : a * a = 1 := by
  revert h; revert a; decide

lemma ZMod3.sq_cases (a : ZMod 3) : a * a = 0 ∨ a * a = 1 := by revert a; decide

lemma ZMod3.eq_zero_of_sq_eq_zero {a : ZMod 3} (h : a * a = 0) : a = 0 := by
  revert h; revert a; decide

end ZMod3

/-- The number of vectors in the kernel of a nonzero linear functional over `ZMod 3`. -/
lemma card_kernel_mul {m : ℕ} (a : Fin m → ZMod 3) (i₀ : Fin m) (h : a i₀ = 1) :
    3 * ((Finset.univ : Finset (Fin m → ZMod 3)).filter
      (fun v => ∑ i, v i * a i = 0)).card = 3 ^ m := by
  classical
  set φ : (Fin m → ZMod 3) → ZMod 3 := fun v => ∑ i, v i * a i with hφ
  have hshift : ∀ (v : Fin m → ZMod 3) (t : ZMod 3),
      φ (v + fun i => if i = i₀ then t else 0) = φ v + t := by
    intro v t
    simp only [hφ, Pi.add_apply]
    have e1 : ∀ i : Fin m, (v i + if i = i₀ then t else 0) * a i
        = v i * a i + (if i = i₀ then t * a i else 0) := by
      intro i
      by_cases hi : i = i₀
      · simp [hi]; ring
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => t * a i)]
    simp [h]
  have hcard : ∀ t : ZMod 3,
      ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = t)).card
      = ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = 0)).card := by
    intro t
    apply Finset.card_bij (fun v _ => v + fun i => if i = i₀ then -t else 0)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hshift v (-t), hv]; ring
    · intro v _ w _ hvw
      exact add_right_cancel hvw
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨w + fun i => if i = i₀ then t else 0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hshift w t, hw]; ring
      · funext i; by_cases hi : i = i₀ <;> simp [hi]
  have htotal : ∑ t : ZMod 3,
      ((Finset.univ : Finset (Fin m → ZMod 3)).filter (fun v => φ v = t)).card = 3 ^ m := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := φ) (fun v _ => Finset.mem_univ _)]
    simp [Finset.card_univ, ZMod.card]
  have hgoal : (Finset.univ.filter (fun v : Fin m → ZMod 3 => ∑ i, v i * a i = 0))
      = Finset.univ.filter (fun v => φ v = 0) := rfl
  rw [hgoal, ← htotal, Finset.sum_congr rfl (fun t _ => hcard t), Finset.sum_const,
    Finset.card_univ, ZMod.card, smul_eq_mul]

/-- Counting matrices all of whose rows lie in a fixed set of vectors. -/
lemma card_rows_filter {m ℓ : ℕ} (P : (Fin m → ZMod 3) → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter (fun c => ∀ j, P (c j))).card
      = ((Finset.univ : Finset (Fin m → ZMod 3)).filter P).card ^ ℓ := by
  classical
  have : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter (fun c => ∀ j, P (c j)))
      = Fintype.piFinset (fun _ : Fin ℓ => (Finset.univ : Finset (Fin m → ZMod 3)).filter P) := by
    ext c
    simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp

/-- Approximating an unbounded fan-in `OR` of `0/1`-valued low degree functions. -/
lemma exists_or_approx {n m ℓ E : ℕ} (q : Fin m → Fn n)
    (hq : ∀ i, q i ∈ Deg n E) (hq01 : ∀ i x, q i x = 0 ∨ q i x = 1) :
    ∃ F : Fn n, F ∈ Deg n (2 * ℓ * E) ∧ (∀ x, F x = 0 ∨ F x = 1) ∧
      ((Finset.univ : Finset (Bits n)).filter
        (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card * 3 ^ ℓ ≤ 2 ^ n := by
  classical
  set Sf : (Fin ℓ → Fin m → ZMod 3) → Fin ℓ → Fn n := fun c j => ∑ i, c j i • q i with hSf
  set Gad : (Fin ℓ → Fin m → ZMod 3) → Fn n :=
    fun c => 1 - ∏ j : Fin ℓ, (1 - Sf c j * Sf c j) with hGad
  have hSval : ∀ c j x, Sf c j x = ∑ i, c j i * q i x := by
    intro c j x
    simp only [hSf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hGval : ∀ c x, Gad c x = 1 - ∏ j : Fin ℓ, (1 - Sf c j x * Sf c j x) := by
    intro c x
    simp only [hGad, Pi.sub_apply, Pi.one_apply, Finset.prod_apply, Pi.mul_apply]
  -- the degree bound
  have hdeg : ∀ c, Gad c ∈ Deg n (2 * ℓ * E) := by
    intro c
    have hS : ∀ j, Sf c j ∈ Deg n E := fun j =>
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hq i))
    have hfac : ∀ j : Fin ℓ, (1 - Sf c j * Sf c j) ∈ Deg n (E + E) := fun j =>
      Submodule.sub_mem _ one_mem_Deg (Deg_mul (hS j) (hS j))
    have hprod : (∏ j : Fin ℓ, (1 - Sf c j * Sf c j)) ∈ Deg n (∑ _j : Fin ℓ, (E + E)) :=
      Deg_prod _ _ _ (fun j _ => hfac j)
    have hsum : (∑ _j : Fin ℓ, (E + E)) = 2 * ℓ * E := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
    rw [hsum] at hprod
    exact Submodule.sub_mem _ one_mem_Deg hprod
  -- the approximators are `0/1`-valued
  have hval01 : ∀ c x, Gad c x = 0 ∨ Gad c x = 1 := by
    intro c x
    rw [hGval]
    by_cases hz : ∃ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 0
    · obtain ⟨j, hj⟩ := hz
      right
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]
      ring
    · push_neg at hz
      left
      have hone : ∀ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 1 := by
        intro j
        rcases ZMod3.sq_cases (Sf c j x) with h | h
        · rw [h]; ring
        · exact absurd (by rw [h]; ring) (hz j)
      rw [Finset.prod_congr rfl (fun j _ => hone j)]
      simp
  -- they are always correct when the `OR` is false
  have hzero : ∀ c x, (∀ i, q i x = 0) → Gad c x = 0 := by
    intro c x h0
    rw [hGval]
    have hone : ∀ j : Fin ℓ, (1 - Sf c j x * Sf c j x) = 1 := by
      intro j
      have hs : Sf c j x = 0 := by
        rw [hSval]
        exact Finset.sum_eq_zero (fun i _ => by rw [h0 i]; ring)
      rw [hs]; ring
    rw [Finset.prod_congr rfl (fun j _ => hone j)]
    simp
  -- an error forces all the random linear forms to vanish
  have hne : ∀ c x, Gad c x ≠ 1 → ∀ j, Sf c j x = 0 := by
    intro c x hcx j
    have hprodne : (∏ j : Fin ℓ, (1 - Sf c j x * Sf c j x)) ≠ 0 := by
      intro h0
      apply hcx
      rw [hGval, h0]; ring
    have hfacne : (1 - Sf c j x * Sf c j x) ≠ 0 := fun h0 =>
      hprodne (Finset.prod_eq_zero (Finset.mem_univ j) h0)
    rcases ZMod3.sq_cases (Sf c j x) with h | h
    · exact ZMod3.eq_zero_of_sq_eq_zero h
    · exact absurd (by rw [h]; ring) hfacne
  set badFor : (Fin ℓ → Fin m → ZMod 3) → Finset (Bits n) := fun c =>
    (Finset.univ : Finset (Bits n)).filter
      (fun x => Gad c x ≠ bit (decide (∃ i, q i x = 1))) with hbadFor
  -- for each input, few choices of the random coefficients are bad
  have hpoint : ∀ x : Bits n,
      ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
        (fun c => x ∈ badFor c)).card * 3 ^ ℓ ≤ 3 ^ (m * ℓ) := by
    intro x
    by_cases hx : ∃ i, q i x = 1
    · obtain ⟨i₀, hi₀⟩ := hx
      have hbit : bit (decide (∃ i, q i x = 1)) = 1 := by
        have : (∃ i, q i x = 1) := ⟨i₀, hi₀⟩
        simp [this]
      have hsub : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c))
          ⊆ (Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => ∀ j, (∑ i, c j i * q i x) = 0) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hbadFor] at hc ⊢
        intro j
        rw [← hSval]
        refine hne c x ?_ j
        rw [hbit] at hc
        exact hc
      have hker := card_kernel_mul (fun i => q i x) i₀ hi₀
      have hrows := card_rows_filter (m := m) (ℓ := ℓ) (fun v => (∑ i, v i * q i x) = 0)
      calc ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card * 3 ^ ℓ
          ≤ ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
              (fun c => ∀ j, (∑ i, c j i * q i x) = 0)).card * 3 ^ ℓ :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ = ((Finset.univ : Finset (Fin m → ZMod 3)).filter
              (fun v => (∑ i, v i * q i x) = 0)).card ^ ℓ * 3 ^ ℓ := by rw [hrows]
        _ = (3 * ((Finset.univ : Finset (Fin m → ZMod 3)).filter
              (fun v => (∑ i, v i * q i x) = 0)).card) ^ ℓ := by
            rw [mul_pow]; ring
        _ = (3 ^ m) ^ ℓ := by rw [hker]
        _ = 3 ^ (m * ℓ) := by rw [← pow_mul]
    · push_neg at hx
      have h0 : ∀ i, q i x = 0 := by
        intro i
        rcases hq01 i x with h | h
        · exact h
        · exact absurd h (hx i)
      have hempty : ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
          (fun c => x ∈ badFor c)) = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, hbadFor]
        intro hc
        apply hc
        rw [hzero c x h0]
        have : ¬ (∃ i, q i x = 1) := by
          rintro ⟨i, hi⟩
          exact hx i hi
        simp [this]
      rw [hempty]
      simp
  -- averaging over the random coefficients
  have hswap : ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card
      = ∑ x : Bits n, ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
          (fun c => x ∈ badFor c)).card := by
    simp only [hbadFor, Finset.card_filter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.sum_comm]
  have hcardc : (Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).card = 3 ^ (m * ℓ) := by
    simp [Finset.card_univ, ZMod.card, pow_mul]
  have hsum : ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card * 3 ^ ℓ
      ≤ ∑ _c : (Fin ℓ → Fin m → ZMod 3), 2 ^ n := by
    calc ∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card * 3 ^ ℓ
        = (∑ c : (Fin ℓ → Fin m → ZMod 3), (badFor c).card) * 3 ^ ℓ := by rw [Finset.sum_mul]
      _ = (∑ x : Bits n, ((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card) * 3 ^ ℓ := by rw [hswap]
      _ = ∑ x : Bits n, (((Finset.univ : Finset (Fin ℓ → Fin m → ZMod 3)).filter
            (fun c => x ∈ badFor c)).card * 3 ^ ℓ) := by rw [Finset.sum_mul]
      _ ≤ ∑ _x : Bits n, 3 ^ (m * ℓ) := Finset.sum_le_sum (fun x _ => hpoint x)
      _ = 2 ^ n * 3 ^ (m * ℓ) := by
          simp [Finset.sum_const, Finset.card_univ]
      _ = ∑ _c : (Fin ℓ → Fin m → ZMod 3), 2 ^ n := by
          rw [Finset.sum_const, hcardc, smul_eq_mul, mul_comm]
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨Gad c₀, hdeg c₀, hval01 c₀, hc₀⟩

lemma bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> decide

lemma bit_eq_one_iff (b : Bool) : bit b = 1 ↔ b = true := by cases b <;> decide

/-- The error set of `1 - f` for `!b` is the error set of `f` for `b`. -/
lemma filter_bad_neg {n : ℕ} (f : Fn n) (b : Bits n → Bool) :
    ((Finset.univ : Finset (Bits n)).filter (fun x => (1 - f x) ≠ bit (!(b x))))
      = (Finset.univ : Finset (Bits n)).filter (fun x => f x ≠ bit (b x)) := by
  apply Finset.filter_congr
  intro x _
  rw [bit_not]
  exact not_congr sub_right_inj

/-- Union bound for the error set of an approximated gate. -/
lemma bad_card_le {n m : ℕ} (F : Fn n) (bfun : Bits n → Bool) (q : Fin m → Fn n)
    (bs : Fin m → Bits n → Bool)
    (hcorr : ∀ x, (∀ i, q i x = bit (bs i x)) → F x = bit (decide (∃ i, q i x = 1)) →
      F x = bit (bfun x)) :
    ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x))).card ≤
      ((Finset.univ : Finset (Bits n)).filter
        (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card +
      ∑ i, ((Finset.univ : Finset (Bits n)).filter (fun x => q i x ≠ bit (bs i x))).card := by
  classical
  have hsub : ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x)))
      ⊆ ((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))) ∪
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x)))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hcon
    rw [Finset.mem_union] at hcon
    push_neg at hcon
    obtain ⟨h1', h2'⟩ := hcon
    have h1 : F x = bit (decide (∃ i, q i x = 1)) := by
      by_contra hh
      exact h1' (Finset.mem_filter.2 ⟨Finset.mem_univ x, hh⟩)
    have h2 : ∀ i, q i x = bit (bs i x) := by
      intro i
      by_contra hh
      exact h2' (Finset.mem_biUnion.2
        ⟨i, Finset.mem_univ i, Finset.mem_filter.2 ⟨Finset.mem_univ x, hh⟩⟩)
    exact hx (hcorr x h2 h1)
  calc ((Finset.univ : Finset (Bits n)).filter (fun x => F x ≠ bit (bfun x))).card
      ≤ (((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))) ∪
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x))))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Bits n)).filter
          (fun x => F x ≠ bit (decide (∃ i, q i x = 1)))).card +
        (Finset.univ.biUnion (fun i => (Finset.univ : Finset (Bits n)).filter
          (fun x => q i x ≠ bit (bs i x)))).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (Finset.card_biUnion_le) _

/-- **Razborov's approximation lemma**. -/
theorem exists_approx {n : ℕ} (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Circuit n) :
    ∃ f : Fn n, f ∈ Deg n ((2 * ℓ) ^ C.depth) ∧ (∀ x, f x = 0 ∨ f x = 1) ∧
      ((Finset.univ : Finset (Bits n)).filter (fun x => f x ≠ bit (C.eval x))).card * 3 ^ ℓ
        ≤ C.size * 2 ^ n := by
  classical
  induction C with
  | const b =>
      refine ⟨(bit b) • (1 : Fn n), Submodule.smul_mem _ _ one_mem_Deg, ?_, ?_⟩
      · intro x
        simpa using bit_eq_zero_or_one b
      · have : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((bit b) • (1 : Fn n)) x ≠ bit ((Circuit.const b).eval x))) = ∅ := by
          ext x; simp
        rw [this]
        simp
  | var i =>
      refine ⟨(2 : ZMod 3) • ((1 : Fn n) - mon ({i} : Finset (Fin n))), ?_, ?_, ?_⟩
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ one_mem_Deg (mon_mem_Deg (by simp)))
      · intro x
        cases hxi : x i
        · left; simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn]
        · right; simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn]; decide
      · have : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((2 : ZMod 3) • ((1 : Fn n) - mon ({i} : Finset (Fin n)))) x
              ≠ bit ((Circuit.var i).eval x))) = ∅ := by
          ext x
          cases hxi : x i
          · simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn, bit]
          · simp [Pi.smul_apply, Pi.sub_apply, mon, hxi, sgn, bit]; decide
        rw [this]
        simp
  | neg C ih =>
      obtain ⟨f, hf1, hf2, hf3⟩ := ih
      refine ⟨(1 : Fn n) - f, Submodule.sub_mem _ one_mem_Deg hf1, ?_, ?_⟩
      · intro x
        rcases hf2 x with h | h <;> simp [Pi.sub_apply, h]
      · have heq : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - f) x ≠ bit ((Circuit.neg C).eval x)))
            = (Finset.univ : Finset (Bits n)).filter (fun x => f x ≠ bit (C.eval x)) := by
          have := filter_bad_neg f (fun x => C.eval x)
          simpa [Pi.sub_apply] using this
        rw [heq]
        simpa using hf3
  | or m g ih =>
      choose f hf1 hf2 hf3 using ih
      set Dm : ℕ := Finset.univ.sup (fun i => (g i).depth) with hDm
      have hfE : ∀ i, f i ∈ Deg n ((2 * ℓ) ^ Dm) := by
        intro i
        refine Deg_mono (Nat.pow_le_pow_right (by omega) ?_) (hf1 i)
        exact Finset.le_sup (f := fun i => (g i).depth) (Finset.mem_univ i)
      obtain ⟨F, hF1, hF2, hF3⟩ := exists_or_approx (ℓ := ℓ) f hfE hf2
      refine ⟨F, ?_, hF2, ?_⟩
      · have : 2 * ℓ * (2 * ℓ) ^ Dm = (2 * ℓ) ^ (Circuit.or m g).depth := by
          rw [Circuit.depth_or, ← hDm, add_comm 1 Dm, pow_succ]
          ring
        rwa [this] at hF1
      · have hcorr : ∀ x, (∀ i, f i x = bit ((g i).eval x)) →
            F x = bit (decide (∃ i, f i x = 1)) → F x = bit ((Circuit.or m g).eval x) := by
          intro x hall hFx
          rw [hFx, Circuit.eval_or]
          congr 1
          refine decide_eq_decide.2 ?_
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨i, by rw [hall i] at hi; exact (bit_eq_one_iff _).1 hi⟩
          · rintro ⟨i, hi⟩
            exact ⟨i, by rw [hall i, hi]; rfl⟩
        have hbc := bad_card_le F (fun x => (Circuit.or m g).eval x) f
          (fun i x => (g i).eval x) hcorr
        calc ((Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit ((Circuit.or m g).eval x))).card * 3 ^ ℓ
            ≤ (((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, f i x = 1)))).card +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card) * 3 ^ ℓ :=
              Nat.mul_le_mul_right _ hbc
          _ = ((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, f i x = 1)))).card * 3 ^ ℓ +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card * 3 ^ ℓ := by
              rw [add_mul, Finset.sum_mul]
          _ ≤ 2 ^ n + ∑ i, (g i).size * 2 ^ n :=
              Nat.add_le_add hF3 (Finset.sum_le_sum (fun i _ => hf3 i))
          _ = (1 + ∑ i, (g i).size) * 2 ^ n := by rw [add_mul, Finset.sum_mul]; ring
          _ = (Circuit.or m g).size * 2 ^ n := by rw [Circuit.size_or]
  | and m g ih =>
      choose f hf1 hf2 hf3 using ih
      set Dm : ℕ := Finset.univ.sup (fun i => (g i).depth) with hDm
      have hfE : ∀ i, ((1 : Fn n) - f i) ∈ Deg n ((2 * ℓ) ^ Dm) := by
        intro i
        refine Submodule.sub_mem _ one_mem_Deg (Deg_mono (Nat.pow_le_pow_right (by omega) ?_)
          (hf1 i))
        exact Finset.le_sup (f := fun i => (g i).depth) (Finset.mem_univ i)
      have hq01 : ∀ i x, ((1 : Fn n) - f i) x = 0 ∨ ((1 : Fn n) - f i) x = 1 := by
        intro i x
        rcases hf2 i x with h | h <;> simp [Pi.sub_apply, h]
      obtain ⟨F, hF1, hF2, hF3⟩ := exists_or_approx (ℓ := ℓ) (fun i => (1 : Fn n) - f i) hfE hq01
      refine ⟨(1 : Fn n) - F, ?_, ?_, ?_⟩
      · have hpow : 2 * ℓ * (2 * ℓ) ^ Dm = (2 * ℓ) ^ (Circuit.and m g).depth := by
          rw [Circuit.depth_and, ← hDm, add_comm 1 Dm, pow_succ]
          ring
        rw [hpow] at hF1
        exact Submodule.sub_mem _ one_mem_Deg hF1
      · intro x
        rcases hF2 x with h | h <;> simp [Pi.sub_apply, h]
      · have hcorr : ∀ x, (∀ i, ((1 : Fn n) - f i) x = bit (!((g i).eval x))) →
            F x = bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)) →
            F x = bit (!((Circuit.and m g).eval x)) := by
          intro x hall hFx
          rw [hFx, Circuit.eval_and]
          congr 1
          rw [← decide_not]
          refine decide_eq_decide.2 ?_
          constructor
          · rintro ⟨i, hi⟩ hcon
            rw [hall i] at hi
            have h1 : (!((g i).eval x)) = true := (bit_eq_one_iff _).1 hi
            rw [hcon i] at h1
            exact Bool.noConfusion h1
          · intro hcon
            simp only [not_forall] at hcon
            obtain ⟨i, hi⟩ := hcon
            refine ⟨i, ?_⟩
            rw [hall i]
            have hgi : (g i).eval x = false := by
              cases h : (g i).eval x
              · rfl
              · exact absurd h hi
            rw [hgi]
            rfl
        have hbc := bad_card_le F (fun x => !((Circuit.and m g).eval x))
          (fun i => (1 : Fn n) - f i) (fun i x => !((g i).eval x)) hcorr
        have hbadneg : ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - F) x ≠ bit ((Circuit.and m g).eval x)))
            = (Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit (!((Circuit.and m g).eval x))) := by
          apply Finset.filter_congr
          intro x _
          rw [Pi.sub_apply, Pi.one_apply, bit_not]
          constructor
          · intro h hc
            exact h (by rw [hc]; ring)
          · intro h hc
            exact h (by rw [← hc]; ring)
        have hchild : ∀ i, ((Finset.univ : Finset (Bits n)).filter
            (fun x => ((1 : Fn n) - f i) x ≠ bit (!((g i).eval x))))
            = (Finset.univ : Finset (Bits n)).filter (fun x => f i x ≠ bit ((g i).eval x)) := by
          intro i
          have := filter_bad_neg (f i) (fun x => (g i).eval x)
          simpa [Pi.sub_apply] using this
        rw [hbadneg]
        calc ((Finset.univ : Finset (Bits n)).filter
              (fun x => F x ≠ bit (!((Circuit.and m g).eval x)))).card * 3 ^ ℓ
            ≤ (((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)))).card +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => ((1 : Fn n) - f i) x ≠ bit (!((g i).eval x)))).card) * 3 ^ ℓ :=
              Nat.mul_le_mul_right _ hbc
          _ = ((Finset.univ : Finset (Bits n)).filter
                (fun x => F x ≠ bit (decide (∃ i, ((1 : Fn n) - f i) x = 1)))).card * 3 ^ ℓ +
              ∑ i, ((Finset.univ : Finset (Bits n)).filter
                (fun x => f i x ≠ bit ((g i).eval x))).card * 3 ^ ℓ := by
              rw [add_mul, Finset.sum_mul]
              congr 1
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hchild i]
          _ ≤ 2 ^ n + ∑ i, (g i).size * 2 ^ n :=
              Nat.add_le_add hF3 (Finset.sum_le_sum (fun i _ => hf3 i))
          _ = (1 + ∑ i, (g i).size) * 2 ^ n := by rw [add_mul, Finset.sum_mul]; ring
          _ = (Circuit.and m g).size * 2 ^ n := by rw [Circuit.size_and]

end CS

import Mathlib

/-!
# Basic setup: the space of `ZMod 3`-valued functions on the Boolean cube

We encode a Boolean value `b` by the sign `sgn b = (-1)^b ∈ ZMod 3`, so that the
Boolean cube becomes `{1, -1}^n ⊆ (ZMod 3)^n`.  For `T ⊆ Fin n` the monomial
function `mon T` is `x ↦ ∏_{i ∈ T} sgn (x i)`, and `Deg n k` is the `ZMod 3`-span
of the monomials of degree at most `k`.  This is the ambient algebra used for the
Razborov–Smolensky approximation method.
-/

namespace CS

open Finset

/-- Boolean inputs. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- `ZMod 3`-valued functions on the Boolean cube. -/
abbrev Fn (n : ℕ) := Bits n → ZMod 3

/-- The `±1` encoding of a Boolean value inside `ZMod 3`. -/
def sgn (b : Bool) : ZMod 3 := if b then -1 else 1

/-- The `0/1` encoding of a Boolean value inside `ZMod 3`. -/
def bit (b : Bool) : ZMod 3 := if b then 1 else 0

@[simp] lemma sgn_true : sgn true = -1 := rfl
@[simp] lemma sgn_false : sgn false = 1 := rfl
@[simp] lemma bit_true : bit true = 1 := rfl
@[simp] lemma bit_false : bit false = 0 := rfl

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> decide

lemma bit_eq_zero_or_one (b : Bool) : bit b = 0 ∨ bit b = 1 := by
  cases b <;> simp

/-- `sgn b = 1 - 2 * bit b`, i.e. `sgn b = 1 + bit b` in `ZMod 3`. -/
lemma sgn_eq (b : Bool) : sgn b = 1 + bit b := by cases b <;> decide

/-- The monomial function attached to a subset of coordinates. -/
def mon {n : ℕ} (T : Finset (Fin n)) : Fn n := fun x => ∏ i ∈ T, sgn (x i)

@[simp] lemma mon_empty {n : ℕ} : mon (∅ : Finset (Fin n)) = 1 := by
  funext x; simp [mon]

lemma mon_mul {n : ℕ} (T U : Finset (Fin n)) : mon T * mon U = mon (symmDiff T U) := by
  funext x
  set a : Fin n → ZMod 3 := fun i => sgn (x i) with ha
  have d1 : Disjoint (T \ U) (T ∩ U) := by
    simp [Finset.disjoint_left]; tauto
  have d2 : Disjoint (U \ T) (T ∩ U) := by
    simp [Finset.disjoint_left]; tauto
  have d3 : Disjoint (T \ U) (U \ T) := by
    simp [Finset.disjoint_left]; tauto
  have e1 : (∏ i ∈ T, a i) = (∏ i ∈ T \ U, a i) * ∏ i ∈ T ∩ U, a i := by
    rw [← Finset.prod_union d1]
    congr 1
    ext i; by_cases h : i ∈ U <;> simp [h]
  have e2 : (∏ i ∈ U, a i) = (∏ i ∈ U \ T, a i) * ∏ i ∈ T ∩ U, a i := by
    rw [← Finset.prod_union d2]
    congr 1
    ext i; by_cases h : i ∈ T <;> simp [h]
  have e3 : (∏ i ∈ symmDiff T U, a i) = (∏ i ∈ T \ U, a i) * ∏ i ∈ U \ T, a i := by
    rw [← Finset.prod_union d3]; rfl
  have hsq : (∏ i ∈ T ∩ U, a i) * (∏ i ∈ T ∩ U, a i) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => sgn_sq (x i))
  show (∏ i ∈ T, a i) * (∏ i ∈ U, a i) = ∏ i ∈ symmDiff T U, a i
  rw [e1, e2, e3]
  calc (∏ i ∈ T \ U, a i) * (∏ i ∈ T ∩ U, a i) * ((∏ i ∈ U \ T, a i) * ∏ i ∈ T ∩ U, a i)
      = ((∏ i ∈ T \ U, a i) * (∏ i ∈ U \ T, a i)) *
        ((∏ i ∈ T ∩ U, a i) * (∏ i ∈ T ∩ U, a i)) := by ring
    _ = (∏ i ∈ T \ U, a i) * ∏ i ∈ U \ T, a i := by rw [hsq]; ring

lemma card_symmDiff_le {n : ℕ} (T U : Finset (Fin n)) :
    (symmDiff T U).card ≤ T.card + U.card := by
  have : symmDiff T U ⊆ T ∪ U := by
    intro i hi
    simp [Finset.mem_symmDiff] at hi
    simp
    tauto
  exact le_trans (Finset.card_le_card this) (Finset.card_union_le _ _)

/-- The finite set of monomials of degree at most `k`. -/
def monSet (n k : ℕ) : Finset (Fn n) :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ k)).image mon

/-- The span of the monomials of degree at most `k`. -/
def Deg (n k : ℕ) : Submodule (ZMod 3) (Fn n) :=
  Submodule.span (ZMod 3) (monSet n k : Set (Fn n))

lemma mon_mem_Deg {n k : ℕ} {T : Finset (Fin n)} (h : T.card ≤ k) : mon T ∈ Deg n k := by
  apply Submodule.subset_span
  simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
  exact ⟨T, ⟨Finset.mem_univ _, h⟩, rfl⟩

lemma one_mem_Deg {n k : ℕ} : (1 : Fn n) ∈ Deg n k := by
  have := @mon_mem_Deg n k ∅ (by simp)
  simpa using this

lemma Deg_mono {n : ℕ} {k k' : ℕ} (h : k ≤ k') : Deg n k ≤ Deg n k' := by
  apply Submodule.span_le.2
  intro f hf
  simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
  obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hf
  exact mon_mem_Deg (le_trans hT h)

lemma Deg_mul {n k k' : ℕ} {f g : Fn n} (hf : f ∈ Deg n k) (hg : g ∈ Deg n k') :
    f * g ∈ Deg n (k + k') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨T, ⟨-, hT⟩, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe,
            Finset.mem_filter] at hg
          obtain ⟨U, ⟨-, hU⟩, rfl⟩ := hg
          rw [mon_mul]
          exact mon_mem_Deg (le_trans (card_symmDiff_le T U) (Nat.add_le_add hT hU))
      | zero => simp
      | add g₁ g₂ _ _ ih₁ ih₂ =>
          have : mon T * (g₁ + g₂) = mon T * g₁ + mon T * g₂ := by ring
          rw [this]; exact Submodule.add_mem _ ih₁ ih₂
      | smul a g _ ih =>
          have : mon T * (a • g) = a • (mon T * g) := by
            funext x; simp [Pi.smul_apply]; ring
          rw [this]; exact Submodule.smul_mem _ _ ih
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ =>
      have : (f₁ + f₂) * g = f₁ * g + f₂ * g := by ring
      rw [this]; exact Submodule.add_mem _ ih₁ ih₂
  | smul a f _ ih =>
      have : (a • f) * g = a • (f * g) := by
        funext x; simp [Pi.smul_apply]; ring
      rw [this]; exact Submodule.smul_mem _ _ ih

lemma Deg_prod {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fn n) (k : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ Deg n (k i)) : (∏ i ∈ s, f i) ∈ Deg n (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one_mem_Deg
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact Deg_mul (hf a (by simp)) (ih (fun i hi => hf i (by simp [hi])))

end CS

import RequestProject.Basic

/-!
# Counting estimates

Three elementary estimates used in the final assembly:

* `CS.centralBinom_sq_mul_le` : `C(2m, m)^2 * (3m+1) ≤ 16^m`, the standard
  `C(2m,m) ≤ 4^m / √(3m+1)` bound in square-free form;
* `CS.card_subsets_le` : the number of subsets of a `2m`-element set of size at
  most `m + D` is at most `4^m / 2 + (D+1) * C(2m,m)`;
* `CS.exists_two_pow_dominates` : exponentials beat polynomials.
-/

namespace CS

open Finset

/-- `C(2m,m)^2 * (3m+1) ≤ 16^m`, i.e. `C(2m,m) ≤ 4^m / √(3m+1)`. -/
lemma centralBinom_sq_mul_le (m : ℕ) :
    (Nat.centralBinom m) ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp [Nat.centralBinom]
  | succ m ih =>
      have hid : (m + 1) * Nat.centralBinom (m + 1) = 2 * (2 * m + 1) * Nat.centralBinom m :=
        Nat.succ_mul_centralBinom_succ m
      set A := Nat.centralBinom m with hA
      set B := Nat.centralBinom (m + 1) with hB
      have hsq : ((m + 1) * B) ^ 2 = 4 * (2 * m + 1) ^ 2 * A ^ 2 := by
        rw [hid]; ring
      -- the key polynomial inequality
      have hpoly : 4 * (2 * m + 1) ^ 2 * (3 * (m + 1) + 1) ≤ 16 * (m + 1) ^ 2 * (3 * m + 1) := by
        nlinarith [sq_nonneg m, Nat.zero_le m]
      have hstep : ((m + 1) ^ 2) * (B ^ 2 * (3 * (m + 1) + 1))
          ≤ ((m + 1) ^ 2) * (16 ^ (m + 1)) := by
        calc ((m + 1) ^ 2) * (B ^ 2 * (3 * (m + 1) + 1))
            = ((m + 1) * B) ^ 2 * (3 * (m + 1) + 1) := by ring
          _ = (4 * (2 * m + 1) ^ 2 * (3 * (m + 1) + 1)) * A ^ 2 := by rw [hsq]; ring
          _ ≤ (16 * (m + 1) ^ 2 * (3 * m + 1)) * A ^ 2 := Nat.mul_le_mul_right _ hpoly
          _ = (16 * (m + 1) ^ 2) * (A ^ 2 * (3 * m + 1)) := by ring
          _ ≤ (16 * (m + 1) ^ 2) * 16 ^ m := Nat.mul_le_mul_left _ ih
          _ = ((m + 1) ^ 2) * (16 ^ (m + 1)) := by ring
      exact Nat.le_of_mul_le_mul_left hstep (by positivity)

/-- The number of subsets of size at most `K` of an `N`-element set. -/
lemma card_filter_card_le (N K : ℕ) :
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun T => T.card ≤ K)).card
      = ∑ k ∈ Finset.range (K + 1), N.choose k := by
  classical
  have hmaps : Set.MapsTo Finset.card
      (((Finset.univ : Finset (Finset (Fin N))).filter (fun T => T.card ≤ K)) : Set (Finset (Fin N)))
      ((Finset.range (K + 1) : Finset ℕ) : Set ℕ) := by
    intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hT
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  have hset : ({T ∈ {T ∈ (Finset.univ : Finset (Finset (Fin N))) | T.card ≤ K} | T.card = k})
      = Finset.powersetCard k (Finset.univ : Finset (Fin N)) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    omega
  rw [hset, Finset.card_powersetCard]
  simp

/-- Half of the binomial coefficients of `2m` sum to at most `4^m / 2`. -/
lemma two_mul_sum_range_choose_lt (m : ℕ) :
    2 * ∑ k ∈ Finset.range m, (2 * m).choose k + Nat.centralBinom m = 4 ^ m := by
  classical
  have hsplit : ∑ k ∈ Finset.range (2 * m + 1), (2 * m).choose k
      = (∑ k ∈ Finset.range m, (2 * m).choose k) + (2 * m).choose m
        + ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose k := by
    have h1 : Finset.range (2 * m + 1)
        = (Finset.range (m + 1)) ∪ Finset.Ico (m + 1) (2 * m + 1) := by
      ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.range (m + 1)) (Finset.Ico (m + 1) (2 * m + 1)) := by
      simp [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_union hd, Finset.sum_range_succ]
  have hmirror : ∑ k ∈ Finset.Ico (m + 1) (2 * m + 1), (2 * m).choose k
      = ∑ k ∈ Finset.range m, (2 * m).choose k := by
    apply Finset.sum_nbij' (fun k => 2 * m - k) (fun k => 2 * m - k)
    · intro k hk; simp [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro k hk; simp [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega
    · intro k hk; simp [Finset.mem_Ico] at hk; omega
    · intro k hk; simp [Finset.mem_range] at hk; omega
    · intro k hk
      simp [Finset.mem_Ico] at hk
      rw [Nat.choose_symm (by omega)]
  have htotal : ∑ k ∈ Finset.range (2 * m + 1), (2 * m).choose k = 4 ^ m := by
    rw [Nat.sum_range_choose (2 * m)]
    rw [pow_mul]
    norm_num
  have hCm : Nat.centralBinom m = (2 * m).choose m := rfl
  rw [hCm]
  omega

/-- The number of subsets of size at most `m + D` of a `2m`-element set. -/
lemma card_subsets_le (m D : ℕ) :
    2 * ((Finset.univ : Finset (Finset (Fin (2 * m)))).filter (fun T => T.card ≤ m + D)).card
      ≤ 4 ^ m + 2 * (D + 1) * Nat.centralBinom m := by
  classical
  rw [card_filter_card_le]
  have hsplit : ∑ k ∈ Finset.range (m + D + 1), (2 * m).choose k
      = (∑ k ∈ Finset.range m, (2 * m).choose k)
        + ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k := by
    have h1 : Finset.range (m + D + 1) = Finset.range m ∪ Finset.Ico m (m + D + 1) := by
      ext k; simp [Finset.mem_range, Finset.mem_Ico]; omega
    have hd : Disjoint (Finset.range m) (Finset.Ico m (m + D + 1)) := by
      simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Ico, not_and]
      intro a ha hb
      omega
    rw [h1, Finset.sum_union hd]
  have hupper : ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k
      ≤ (D + 1) * Nat.centralBinom m := by
    calc ∑ k ∈ Finset.Ico m (m + D + 1), (2 * m).choose k
        ≤ ∑ _k ∈ Finset.Ico m (m + D + 1), Nat.centralBinom m := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have := Nat.choose_le_middle k (2 * m)
          simpa [Nat.centralBinom, Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
      _ = (D + 1) * Nat.centralBinom m := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
          congr 1
          omega
  have hhalf := two_mul_sum_range_choose_lt m
  have hprod : 2 * (D + 1) * Nat.centralBinom m = 2 * ((D + 1) * Nat.centralBinom m) := by ring
  rw [hsplit, hprod]
  omega

/-- `k * (q+1) ≤ 2^q` once `q ≥ k^2 + k`. -/
lemma linear_le_two_pow {k q : ℕ} (h : k ^ 2 + k ≤ q) : k * (q + 1) ≤ 2 ^ q := by
  obtain ⟨r, rfl⟩ : ∃ r, q = k + r := ⟨q - k, by omega⟩
  have hr : k ^ 2 ≤ r + 1 := by nlinarith
  have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h2 : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
  calc k * (k + r + 1) ≤ (k + 1) * (r + 1) := by nlinarith
    _ ≤ 2 ^ k * 2 ^ r := Nat.mul_le_mul h1 h2
    _ = 2 ^ (k + r) := by rw [← pow_add]

/-- Polynomials are dominated by the exponential: `i^k ≤ 2^i` for `i` large. -/
lemma pow_le_two_pow {k i : ℕ} (h : k * (k + k ^ 2 + 1) ≤ i) : i ^ k ≤ 2 ^ i := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simpa using Nat.one_le_two_pow
  set q := i / k with hq
  have hik : i = k * q + i % k := (Nat.div_add_mod i k).symm
  have hmod : i % k < k := Nat.mod_lt _ hk
  have hqge : k ^ 2 + k ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hk]
    nlinarith
  have hilt : i ≤ k * (q + 1) := by nlinarith
  have hkey : k * (q + 1) ≤ 2 ^ q := linear_le_two_pow hqge
  calc i ^ k ≤ (2 ^ q) ^ k := Nat.pow_le_pow_left (le_trans hilt hkey) k
    _ = 2 ^ (q * k) := by rw [← pow_mul]
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm q k]; omega)

/-- Exponentials dominate polynomials: `B * (A * (i+2))^K ≤ 2^i` for some `i`. -/
lemma exists_two_pow_dominates (A K B : ℕ) : ∃ i : ℕ, B * (A * (i + 2)) ^ K ≤ 2 ^ i := by
  set k := 3 * K + 3 with hk
  refine ⟨max (max A B) (max 2 (k * (k + k ^ 2 + 1))), ?_⟩
  set i := max (max A B) (max 2 (k * (k + k ^ 2 + 1))) with hi
  have hiA : A ≤ i := le_trans (le_max_left _ _) (le_max_left _ _)
  have hiB : B ≤ i := le_trans (le_max_right _ _) (le_max_left _ _)
  have hi2 : 2 ≤ i := le_trans (le_max_left _ _) (le_max_right _ _)
  have hik : k * (k + k ^ 2 + 1) ≤ i := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB3 : B ≤ i ^ 3 := le_trans hiB (Nat.le_self_pow (by norm_num) i)
  have hA3 : A * (i + 2) ≤ i ^ 3 := by
    have h1 : A * (i + 2) ≤ i * (i + 2) := Nat.mul_le_mul_right _ hiA
    have h2 : i * (i + 2) ≤ i * (2 * i) := Nat.mul_le_mul_left _ (by omega)
    have h3 : i * (2 * i) ≤ i * (i * i) := Nat.mul_le_mul_left _ (by nlinarith)
    calc A * (i + 2) ≤ i * (i * i) := by omega
      _ = i ^ 3 := by ring
  calc B * (A * (i + 2)) ^ K ≤ i ^ 3 * (i ^ 3) ^ K :=
        Nat.mul_le_mul hB3 (Nat.pow_le_pow_left hA3 K)
    _ = i ^ (3 * K + 3) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ = i ^ k := by rw [hk]
    _ ≤ 2 ^ i := pow_le_two_pow hik

end CS

import RequestProject.Circuit

/-!
# Smolensky's degree lower bound for parity

If a function `g` of degree at most `D` (over `ZMod 3`, in the `±1` encoding)
agrees with `PARITY` on a set `G` of inputs, then `G` cannot be large:
`|G| ≤ #{T ⊆ [n] : |T| ≤ K}` whenever `n + D ≤ 2K`.

The argument is Smolensky's: on the agreement set every monomial of high degree
can be traded, using `g`, for one of degree at most `K`; since the point
indicators span all functions on `G`, the restrictions of the monomials of degree
at most `K` span the whole `|G|`-dimensional space of functions on `G`.
-/

namespace CS

open Finset

/-- The indicator function of a point of the cube, as a product of linear factors. -/
noncomputable def deltaFn {n : ℕ} (a : Bits n) : Fn n :=
  ∏ i : Fin n, (fun x : Bits n => -(1 + sgn (a i) * sgn (x i)))

lemma deltaFn_apply {n : ℕ} (a x : Bits n) :
    deltaFn a x = ∏ i : Fin n, (-(1 + sgn (a i) * sgn (x i))) := by
  rw [deltaFn, Finset.prod_apply]

lemma deltaFn_mem {n : ℕ} (a : Bits n) : deltaFn a ∈ Deg n n := by
  have h : ∀ i : Fin n, (fun x : Bits n => -(1 + sgn (a i) * sgn (x i))) ∈ Deg n 1 := by
    intro i
    have hfac : (fun x : Bits n => -(1 + sgn (a i) * sgn (x i)))
        = (-1 : ZMod 3) • (1 : Fn n) + (-(sgn (a i))) • mon ({i} : Finset (Fin n)) := by
      funext x
      simp [mon, Pi.smul_apply, Pi.add_apply]
      ring
    rw [hfac]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ one_mem_Deg)
      (Submodule.smul_mem _ _ (mon_mem_Deg (by simp)))
  have := Deg_prod (Finset.univ : Finset (Fin n))
    (fun i => (fun x : Bits n => -(1 + sgn (a i) * sgn (x i)))) (fun _ => 1) (fun i _ => h i)
  simpa [deltaFn] using this

lemma deltaFn_self {n : ℕ} (a : Bits n) : deltaFn a a = 1 := by
  rw [deltaFn_apply]
  refine Finset.prod_eq_one (fun i _ => ?_)
  rw [sgn_sq]
  decide

lemma deltaFn_ne {n : ℕ} {a x : Bits n} (h : x ≠ a) : deltaFn a x = 0 := by
  rw [deltaFn_apply]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  cases hxa : a i <;> cases hxi : x i <;> simp [hxa, hxi] at hi ⊢

/-- `symmDiff Tᶜ univ = T`. -/
lemma symmDiff_compl_univ {n : ℕ} (T : Finset (Fin n)) :
    symmDiff (Tᶜ) (Finset.univ : Finset (Fin n)) = T := by
  ext i
  simp [Finset.mem_symmDiff]

theorem smolensky_card_le {n D K : ℕ} (hK : n + D ≤ 2 * K) (G : Finset (Bits n)) (g : Fn n)
    (hg : g ∈ Deg n D) (hgG : ∀ x ∈ G, g x = sgn (parity n x)) :
    G.card ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ K)).card := by
  classical
  -- the restriction map to `G`
  let R : Fn n →ₗ[ZMod 3] (↥G → ZMod 3) :=
    { toFun := fun f a => f a.1
      map_add' := by intro f₁ f₂; rfl
      map_smul' := by intro c f; rfl }
  set W : Submodule (ZMod 3) (↥G → ZMod 3) := Submodule.map R (Deg n K) with hW
  -- every monomial restricts into `W`
  have step1 : ∀ T : Finset (Fin n), R (mon T) ∈ W := by
    intro T
    by_cases hT : T.card ≤ K
    · exact Submodule.mem_map_of_mem (mon_mem_Deg hT)
    · push_neg at hT
      have hcompl : (Tᶜ).card + D ≤ K := by
        have h1 : T.card + (Tᶜ).card = n := by
          simp
        omega
      have hmem : mon (Tᶜ) * g ∈ Deg n K := Deg_mono hcompl (Deg_mul (mon_mem_Deg le_rfl) hg)
      have heq : R (mon (Tᶜ) * g) = R (mon T) := by
        funext a
        have ha : (a : Bits n) ∈ G := a.2
        show (mon (Tᶜ) * g) (a : Bits n) = mon T (a : Bits n)
        rw [Pi.mul_apply, hgG _ ha, ← mon_univ_eq_sgn_parity, ← Pi.mul_apply, mon_mul,
          symmDiff_compl_univ]
      rw [← heq]
      exact Submodule.mem_map_of_mem hmem
  -- the restrictions of all monomials span everything
  have hspan : Submodule.map R (Deg n n) ≤ W := by
    rw [Deg, Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro h ⟨f, hf, rfl⟩
    simp only [monSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
    obtain ⟨T, -, rfl⟩ := hf
    exact step1 T
  have hWtop : W = ⊤ := by
    refine eq_top_iff.2 (fun h _ => ?_)
    have hF : (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) ∈ Deg n n :=
      Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (deltaFn_mem _))
    have hRF : R (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) = h := by
      funext b
      show (∑ a ∈ G.attach, (h a) • deltaFn (a : Bits n)) (b : Bits n) = h b
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single b]
      · simp [Pi.smul_apply, deltaFn_self]
      · intro a _ hab
        have : (a : Bits n) ≠ (b : Bits n) := fun hc => hab (Subtype.ext hc)
        simp [Pi.smul_apply, deltaFn_ne (Ne.symm this)]
      · intro hb
        exact absurd (Finset.mem_attach _ _) hb
    rw [← hRF]
    exact hspan (Submodule.mem_map_of_mem hF)
  -- dimension count
  have hcard : Module.finrank (ZMod 3) (↥G → ZMod 3) = G.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have himg : W = Submodule.span (ZMod 3) (((monSet n K).image R : Finset (↥G → ZMod 3)) :
      Set (↥G → ZMod 3)) := by
    rw [hW, Deg, Submodule.map_span, Finset.coe_image]
  have hle : Module.finrank (ZMod 3) ↥W ≤ ((monSet n K).image R).card := by
    rw [himg]
    have := finrank_span_le_card (R := ZMod 3)
      (((monSet n K).image R : Finset (↥G → ZMod 3)) : Set (↥G → ZMod 3))
    simpa using this
  have hWrank : Module.finrank (ZMod 3) ↑W = G.card := by
    rw [hWtop, finrank_top, hcard]
  have hfinal : G.card ≤ ((monSet n K).image R).card := by
    rw [← hWrank]; exact hle
  calc G.card ≤ ((monSet n K).image R).card := hfinal
    _ ≤ (monSet n K).card := Finset.card_image_le
    _ ≤ _ := by rw [monSet]; exact Finset.card_image_le

end CS

import Mathlib
import RequestProject.Basic
import RequestProject.Circuit
import RequestProject.Approx
import RequestProject.Counting
import RequestProject.Smolensky

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- Sanity check that the class `AC⁰` as formalised here is not degenerate: the
unbounded fan-in `OR` family is in `AC⁰`. -/
theorem or_in_ac0 : InAC0 (fun _n x => decide (∃ i, x i = true)) := by
  refine ⟨1, 0, fun n => ⟨Circuit.or n (fun i => Circuit.var i), ?_, ?_, ?_⟩⟩
  · simp
  · simp
  · intro x; simp

/-- **PARITY is not in `AC⁰`** (Razborov–Smolensky / Håstad).

There is no family of constant-depth, polynomial-size, unbounded fan-in Boolean
circuits computing the parity function. -/
theorem parity_not_ac0 : ¬ InAC0 parity := by
  rintro ⟨d, c, hC⟩
  obtain ⟨i, hi⟩ := exists_two_pow_dominates (2 * c + 4) (2 * d) 144
  set m : ℕ := 2 ^ i with hm
  set l : ℕ := c * (i + 2) + 2 with hl
  set D : ℕ := (2 * l) ^ d with hD
  have hl1 : 1 ≤ l := by omega
  -- The polynomial bound on the circuit size is beaten by `3 ^ l`.
  have hF1 : 4 * (2 * m + 2) ^ c ≤ 3 ^ l := by
    have h1 : 2 * m + 2 ≤ 3 ^ (i + 2) := by
      calc 2 * m + 2 = 2 ^ (i + 1) + 2 := by rw [hm, pow_succ]; ring
        _ ≤ 2 ^ (i + 1) + 2 ^ (i + 1) := by
            have : (2:ℕ) ≤ 2 ^ (i + 1) := by
              calc (2:ℕ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
        _ = 2 ^ (i + 2) := by ring
        _ ≤ 3 ^ (i + 2) := Nat.pow_le_pow_left (by norm_num) _
    calc 4 * (2 * m + 2) ^ c ≤ 9 * (3 ^ (i + 2)) ^ c := by
          exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h1 c)
      _ = 3 ^ (c * (i + 2) + 2) := by rw [← pow_mul]; ring
      _ = 3 ^ l := by rw [hl]
  -- The degree bound is beaten by `√(3m)`.
  have hF2 : 16 * (D + 2) ^ 2 ≤ 3 * m := by
    have hQ1 : 1 ≤ ((2 * c + 4) * (i + 2)) ^ d := Nat.one_le_pow _ _ (by positivity)
    have hDQ : D ≤ ((2 * c + 4) * (i + 2)) ^ d := by
      rw [hD]
      exact Nat.pow_le_pow_left (by rw [hl]; nlinarith) d
    have h3Q : D + 2 ≤ 3 * ((2 * c + 4) * (i + 2)) ^ d := by omega
    calc 16 * (D + 2) ^ 2 ≤ 16 * (3 * ((2 * c + 4) * (i + 2)) ^ d) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3Q 2)
      _ = 144 * (((2 * c + 4) * (i + 2)) ^ d) ^ 2 := by ring
      _ = 144 * ((2 * c + 4) * (i + 2)) ^ (2 * d) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ i := hi
      _ ≤ 3 * m := by rw [hm]; omega
  -- The circuit computing parity on `2m` bits.
  obtain ⟨C, hdepth, hsize, heval⟩ := hC (2 * m)
  obtain ⟨f, hfDeg, -, hfbad⟩ := exists_approx l hl1 C
  have hfDeg' : f ∈ Deg (2 * m) D := by
    refine Deg_mono ?_ hfDeg
    rw [hD]
    exact Nat.pow_le_pow_right (by omega) hdepth
  -- The set of inputs where the approximation is correct.
  have hbadeq : (Finset.univ.filter (fun x : Bits (2 * m) => f x ≠ bit (C.eval x)))
      = Finset.univ.filter (fun x : Bits (2 * m) => ¬ (f x = bit (parity (2 * m) x))) := by
    apply Finset.filter_congr
    intro x _
    rw [heval x]
  set bad := Finset.univ.filter (fun x : Bits (2 * m) => ¬ (f x = bit (parity (2 * m) x)))
    with hbad
  set G := Finset.univ.filter (fun x : Bits (2 * m) => f x = bit (parity (2 * m) x)) with hGdef
  have hpart : G.card + bad.card = 2 ^ (2 * m) := by
    rw [hGdef, hbad, Finset.card_filter_add_card_filter_not]
    simp
  have h4bad : 4 * bad.card ≤ 2 ^ (2 * m) := by
    rw [hbadeq] at hfbad
    have hb : bad.card * 3 ^ l ≤ C.size * 2 ^ (2 * m) := hfbad
    have key : (4 * bad.card) * 3 ^ l ≤ 2 ^ (2 * m) * 3 ^ l := by
      calc (4 * bad.card) * 3 ^ l = 4 * (bad.card * 3 ^ l) := by ring
        _ ≤ 4 * (C.size * 2 ^ (2 * m)) := Nat.mul_le_mul_left _ hb
        _ = (4 * C.size) * 2 ^ (2 * m) := by ring
        _ ≤ (4 * (2 * m + 2) ^ c) * 2 ^ (2 * m) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsize)
        _ ≤ 3 ^ l * 2 ^ (2 * m) := Nat.mul_le_mul_right _ hF1
        _ = 2 ^ (2 * m) * 3 ^ l := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  have h3G : 3 * 2 ^ (2 * m) ≤ 4 * G.card := by omega
  -- Smolensky's bound.
  have hgmem : (1 + f) ∈ Deg (2 * m) D := Submodule.add_mem _ one_mem_Deg hfDeg'
  have hgG : ∀ x ∈ G, (1 + f) x = sgn (parity (2 * m) x) := by
    intro x hx
    rw [hGdef, Finset.mem_filter] at hx
    rw [Pi.add_apply, Pi.one_apply, hx.2, ← sgn_eq]
  have hsm := smolensky_card_le (n := 2 * m) (D := D) (K := m + (D + 1)) (by omega) G (1 + f)
    hgmem hgG
  have hcount := card_subsets_le m (D + 1)
  set N := ((Finset.univ : Finset (Finset (Fin (2 * m)))).filter
    (fun T => T.card ≤ m + (D + 1))).card with hN
  set C0 := Nat.centralBinom m with hC0
  -- Arithmetic contradiction.
  have hpow : (2:ℕ) ^ (2 * m) = 4 ^ m := by
    rw [pow_mul]; norm_num
  have hcount' : 2 * N ≤ 4 ^ m + 2 * ((D + 2) * C0) := by
    calc 2 * N ≤ 4 ^ m + 2 * (D + 1 + 1) * C0 := hcount
      _ = 4 ^ m + 2 * ((D + 2) * C0) := by ring
  have hXY : 4 ^ m ≤ 4 * ((D + 2) * C0) := by
    rw [hpow] at h3G
    omega
  have hC0pos : 0 < C0 := Nat.centralBinom_pos m
  have h1 : (4 ^ m : ℕ) ^ 2 ≤ (4 * ((D + 2) * C0)) ^ 2 := Nat.pow_le_pow_left hXY 2
  have h2 : (4 * ((D + 2) * C0)) ^ 2 = (16 * (D + 2) ^ 2) * C0 ^ 2 := by ring
  have h3 : (16 * (D + 2) ^ 2) * C0 ^ 2 ≤ (3 * m) * C0 ^ 2 :=
    Nat.mul_le_mul_right _ hF2
  have h4 : (3 * m) * C0 ^ 2 < (3 * m + 1) * C0 ^ 2 := by
    have : 0 < C0 ^ 2 := by positivity
    nlinarith
  have h5 : C0 ^ 2 * (3 * m + 1) ≤ 16 ^ m := centralBinom_sq_mul_le m
  have h6 : ((4:ℕ) ^ m) ^ 2 = 16 ^ m := by
    rw [← pow_mul, mul_comm m 2, pow_mul]; norm_num
  rw [h6] at h1
  rw [h2] at h1
  have : (16:ℕ) ^ m < 16 ^ m := by
    calc (16:ℕ) ^ m ≤ (16 * (D + 2) ^ 2) * C0 ^ 2 := h1
      _ ≤ (3 * m) * C0 ^ 2 := h3
      _ < (3 * m + 1) * C0 ^ 2 := h4
      _ = C0 ^ 2 * (3 * m + 1) := by ring
      _ ≤ 16 ^ m := h5
  exact absurd this (lt_irrefl _)

end CS


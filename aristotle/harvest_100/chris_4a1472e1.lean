/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

lemma zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

lemma BV.add_self (x : BV n) : x + x = 0 := by
  funext i; simpa using zmod2_add_self (x i)

lemma BV.add_add_cancel (x s : BV n) : x + s + s = x := by
  rw [add_assoc, BV.add_self, add_zero]

/-- The `ZMod 2`-valued inner product of two bit strings. -/
def dotp (x y : BV n) : ZMod 2 := ∑ i, x i * y i

lemma dotp_add_left (x z y : BV n) : dotp (x + z) y = dotp x y + dotp z y := by
  simp [dotp, add_mul, Finset.sum_add_distrib]

/-! ## The Simon promise -/

/-- `f` satisfies Simon's promise with hidden shift `s`: `s ≠ 0` and `f` is exactly
two-to-one, with fibers the cosets of `{0, s}`. -/
def IsSimon (f : BV n → BV n) (s : BV n) : Prop :=
  s ≠ 0 ∧ ∀ x z, (f x = f z ↔ (z = x ∨ z = x + s))

lemma IsSimon.shift {f : BV n → BV n} {s : BV n} (h : IsSimon f s) (x : BV n) :
    f (x + s) = f x := ((h.2 x (x + s)).2 (Or.inr rfl)).symm

/-! ## Quantum part: one query produces an outcome orthogonal to `s` -/

/-- The character `ZMod 2 → ℂ`, `b ↦ (-1)^b`. -/
def chi (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [chi] <;> decide

lemma chi_one : chi 1 = -1 := by simp [chi]

/-- The amplitude of measuring `y` in the first register and `v` in the second register,
after running the standard Simon circuit (uniform superposition, one oracle query,
Hadamard transform on the first register), up to the global normalisation `2⁻ⁿ`. -/
noncomputable def amp (f : BV n → BV n) (y v : BV n) : ℂ :=
  ∑ x : BV n, (if f x = v then chi (dotp x y) else 0)

/-- **Quantum query step.** Any measurement outcome `y` with nonzero amplitude is orthogonal
to the hidden shift `s`. -/
theorem amp_eq_zero_of_dotp_ne_zero {f : BV n → BV n} {s : BV n} (h : IsSimon f s)
    (y v : BV n) (hy : dotp s y = 1) : amp f y v = 0 := by
  set g : BV n → ℂ := fun x => if f x = v then chi (dotp x y) else 0 with hg
  have hstep : ∀ x, g (x + s) = - g x := by
    intro x
    simp only [hg, h.shift x, dotp_add_left, hy, chi_add, chi_one]
    split <;> ring
  have h1 : ∑ x : BV n, g (x + s) = ∑ x : BV n, g x :=
    Equiv.sum_comp (Equiv.addRight s) g
  have h2 : ∑ x : BV n, g (x + s) = - ∑ x : BV n, g x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => hstep x)
  have hS : (∑ x : BV n, g x) = - ∑ x : BV n, g x := h1.symm.trans h2
  show (∑ x : BV n, g x) = 0
  linear_combination (1 / 2 : ℂ) * hS

theorem dotp_eq_zero_of_amp_ne_zero {f : BV n → BV n} {s : BV n} (h : IsSimon f s)
    (y v : BV n) (hy : amp f y v ≠ 0) : dotp s y = 0 := by
  rcases zmod2_cases (dotp s y) with h0 | h1
  · exact h0
  · exact absurd (amp_eq_zero_of_dotp_ne_zero h y v h1) hy

/-! ## Quantum part: `O(n)` outcomes determine `s` -/

/-- **Quantum query count.** For any hidden shift `s ≠ 0` there is a set `Y` of at most `n`
possible measurement outcomes (all orthogonal to `s`) which pins `s` down: the only vectors
orthogonal to all of `Y` are `0` and `s`.  Hence `O(n)` quantum queries suffice. -/
theorem exists_determining_set (s : BV n) (hs : s ≠ 0) :
    ∃ Y : Finset (BV n), Y.card ≤ n ∧ (∀ y ∈ Y, dotp s y = 0) ∧
      ∀ t : BV n, (∀ y ∈ Y, dotp t y = 0) → t = 0 ∨ t = s := by
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hs (funext hc)
  have hi1 : s i = 1 := (zmod2_cases (s i)).resolve_left hi
  set yv : Fin n → BV n :=
    fun j k => (if k = j then 1 else 0) + (if k = i then s j else 0) with hyv
  have hdot : ∀ (t : BV n) (j : Fin n), dotp t (yv j) = t j + t i * s j := by
    intro t j
    simp [dotp, hyv, mul_add, Finset.sum_add_distrib, mul_ite,
      Finset.sum_ite_eq' Finset.univ j t]
  refine ⟨(Finset.univ.erase i).image yv, ?_, ?_, ?_⟩
  · exact le_trans (Finset.card_image_le.trans Finset.card_erase_le) (by simp)
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨j, _, rfl⟩ := hy
    rw [hdot, hi1]
    generalize s j = a
    revert a
    decide
  · intro t ht
    have key : ∀ j, j ≠ i → t j = t i * s j := by
      intro j hj
      have hj0 :=
        ht (yv j) (Finset.mem_image_of_mem yv (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩))
      rw [hdot] at hj0
      have h2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h2 _ _ hj0
    rcases zmod2_cases (t i) with h0 | h1
    · left
      funext k
      by_cases hk : k = i
      · subst hk; simpa using h0
      · simpa [h0] using key k hk
    · right
      funext k
      by_cases hk : k = i
      · subst hk; rw [h1, hi1]
      · simpa [h1] using key k hk

/-! ## Classical part -/

/-- A deterministic classical query algorithm: it chooses its next query as a function of the
list of answers received so far, and finally outputs a guess for `s`. -/
structure ClassicalAlgo (n : ℕ) where
  query : List (BV n) → BV n
  output : List (BV n) → BV n

/-- The list of answers received during the first `k` queries. -/
def transcript (A : ClassicalAlgo n) (f : BV n → BV n) : ℕ → List (BV n)
  | 0 => []
  | (k + 1) => transcript A f k ++ [f (A.query (transcript A f k))]

/-- The set of points queried during the first `k` queries. -/
def queries (A : ClassicalAlgo n) (f : BV n → BV n) : ℕ → Finset (BV n)
  | 0 => ∅
  | (k + 1) => insert (A.query (transcript A f k)) (queries A f k)

lemma queries_card_le (A : ClassicalAlgo n) (f : BV n → BV n) (k : ℕ) :
    (queries A f k).card ≤ k := by
  induction k with
  | zero => simp [queries]
  | succ m ih =>
      have := Finset.card_insert_le (A.query (transcript A f m)) (queries A f m)
      simp only [queries]
      omega

lemma queries_subset_succ (A : ClassicalAlgo n) (f : BV n → BV n) (m : ℕ) :
    queries A f m ⊆ queries A f (m + 1) := by
  simp only [queries]
  exact Finset.subset_insert _ _

lemma queries_mono (A : ClassicalAlgo n) (f : BV n → BV n) {j k : ℕ} (hjk : j ≤ k) :
    queries A f j ⊆ queries A f k :=
  monotone_nat_of_le_succ (f := fun m => queries A f m)
    (fun m => queries_subset_succ A f m) hjk

lemma query_mem_queries (A : ClassicalAlgo n) (f : BV n → BV n) (j : ℕ) :
    A.query (transcript A f j) ∈ queries A f (j + 1) := by
  simp [queries]

/-- If an oracle agrees with the identity on all points queried in the identity run,
the two runs are indistinguishable. -/
lemma transcript_eq_of_agree (A : ClassicalAlgo n) (f : BV n → BV n) (k : ℕ)
    (hf : ∀ x ∈ queries A id k, f x = x) :
    ∀ j ≤ k, transcript A f j = transcript A id j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hm' : m ≤ k := by omega
      have h1 := ih hm'
      have hmem : A.query (transcript A id m) ∈ queries A id k :=
        queries_mono A id hm (query_mem_queries A id m)
      simp only [transcript, h1, hf _ hmem, id_eq]

/-! ### The adversary oracle -/

/-- An arbitrary injective numbering of bit strings, used to pick coset representatives. -/
noncomputable def ord (x : BV n) : ℕ := (Fintype.equivFin (BV n) x : ℕ)

lemma ord_injective : Function.Injective (ord (n := n)) := by
  intro x y h
  exact (Fintype.equivFin (BV n)).injective (Fin.val_injective h)

/-- The chosen representative of the coset `{x, x + s}`. -/
noncomputable def rep (s x : BV n) : BV n := if ord x ≤ ord (x + s) then x else x + s

lemma rep_mem (s x : BV n) : rep s x = x ∨ rep s x = x + s := by
  unfold rep; split <;> simp

lemma rep_shift (s x : BV n) : rep s (x + s) = rep s x := by
  unfold rep
  rw [BV.add_add_cancel]
  by_cases h : ord x ≤ ord (x + s)
  · by_cases h' : ord (x + s) ≤ ord x
    · have : x = x + s := ord_injective (le_antisymm h h')
      simp [← this]
    · simp [h, h']
  · have h' : ord (x + s) ≤ ord x := le_of_not_ge h
    simp [h, h']

/-- The adversary's oracle: two-to-one with hidden shift `s`, but equal to the identity on
the queried set `Q`, provided `Q` contains no pair differing by `s`. -/
noncomputable def adv (Q : Finset (BV n)) (s : BV n) (x : BV n) : BV n :=
  if rep s x ∈ Q then rep s x else if rep s x + s ∈ Q then rep s x + s else rep s x

lemma adv_mem_rep (Q : Finset (BV n)) (s x : BV n) :
    adv Q s x = rep s x ∨ adv Q s x = rep s x + s := by
  unfold adv
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

lemma adv_mem (Q : Finset (BV n)) (s x : BV n) :
    adv Q s x = x ∨ adv Q s x = x + s := by
  rcases rep_mem s x with hr | hr <;> rcases adv_mem_rep Q s x with h | h
  · exact Or.inl (by rw [h, hr])
  · exact Or.inr (by rw [h, hr])
  · exact Or.inr (by rw [h, hr])
  · exact Or.inl (by rw [h, hr, BV.add_add_cancel])

lemma adv_shift (Q : Finset (BV n)) (s x : BV n) : adv Q s (x + s) = adv Q s x := by
  simp [adv, rep_shift]

lemma isSimon_adv (Q : Finset (BV n)) (s : BV n) (hs : s ≠ 0) : IsSimon (adv Q s) s := by
  refine ⟨hs, fun x z => ⟨?_, ?_⟩⟩
  · intro heq
    rcases adv_mem Q s x with hx | hx <;> rcases adv_mem Q s z with hz | hz
    · exact Or.inl (by rw [← hz, ← heq, hx])
    · have hxz : x = z + s := by rw [← hx, heq, hz]
      exact Or.inr (by rw [hxz, BV.add_add_cancel])
    · have hxz : x + s = z := by rw [← hx, heq, hz]
      exact Or.inr hxz.symm
    · have hxz : x + s = z + s := by rw [← hx, heq, hz]
      exact Or.inl (add_right_cancel hxz).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (adv_shift Q s x).symm

lemma adv_eq_self (Q : Finset (BV n)) (s : BV n) (hQ : ∀ x ∈ Q, x + s ∉ Q)
    {x : BV n} (hx : x ∈ Q) : adv Q s x = x := by
  rcases rep_mem s x with hr | hr
  · unfold adv
    rw [hr]
    simp [hx]
  · unfold adv
    rw [hr, BV.add_add_cancel]
    simp [hQ x hx, hx]

/-! ### The classical lower bound -/

/-- The set of pairwise sums of a query set. -/
noncomputable def diffs (Q : Finset (BV n)) : Finset (BV n) :=
  (Q ×ˢ Q).image (fun p => p.1 + p.2)

lemma diffs_card_le (Q : Finset (BV n)) : (diffs Q).card ≤ Q.card * Q.card := by
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_product]

lemma not_mem_diffs (Q : Finset (BV n)) {s : BV n} (hs : s ∉ diffs Q) :
    ∀ x ∈ Q, x + s ∉ Q := by
  intro x hx hxs
  refine hs (Finset.mem_image.2 ⟨(x, x + s), Finset.mem_product.2 ⟨hx, hxs⟩, ?_⟩)
  show x + (x + s) = s
  rw [← add_assoc, BV.add_self, zero_add]

/-- **Classical lower bound (raw form).**  A deterministic classical algorithm that always
identifies the hidden shift using `k` queries must satisfy `2 ^ n ≤ k * k + 2`. -/
theorem classical_lower_bound_raw (k : ℕ) (A : ClassicalAlgo n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → A.output (transcript A f k) = s) :
    2 ^ n ≤ k * k + 2 := by
  by_contra hcon
  push_neg at hcon
  set Q : Finset (BV n) := queries A id k with hQdef
  have hQcard : Q.card ≤ k := queries_card_le A id k
  set D : Finset (BV n) := insert 0 (diffs Q) with hDdef
  have hD : D.card ≤ k * k + 1 := by
    have h1 : D.card ≤ (diffs Q).card + 1 := by
      rw [hDdef]; exact Finset.card_insert_le _ _
    have h2 := diffs_card_le Q
    have h3 : Q.card * Q.card ≤ k * k := Nat.mul_le_mul hQcard hQcard
    omega
  have hcard : (Finset.univ : Finset (BV n)).card = 2 ^ n := by simp
  have h1 : 1 < (Finset.univ \ D).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ D), hcard]
    omega
  obtain ⟨s1, hs1, s2, hs2, hne⟩ := Finset.one_lt_card.mp h1
  have key : ∀ s ∈ Finset.univ \ D, A.output (transcript A id k) = s := by
    intro s hsm
    have hsD : s ∉ D := (Finset.mem_sdiff.mp hsm).2
    have hs0 : s ≠ 0 := by
      intro h
      exact hsD (by rw [hDdef, h]; exact Finset.mem_insert_self _ _)
    have hsd : s ∉ diffs Q := fun h => hsD (Finset.mem_insert_of_mem h)
    have hf : ∀ x ∈ queries A id k, adv Q s x = x :=
      fun x hx => adv_eq_self Q s (not_mem_diffs Q hsd) hx
    have ht := transcript_eq_of_agree A (adv Q s) k hf k le_rfl
    have hout := hA (adv Q s) s (isSimon_adv Q s hs0)
    rwa [ht] at hout
  exact hne ((key s1 hs1).symm.trans (key s2 hs2))

/-- **Classical lower bound.**  A deterministic classical algorithm that always identifies the
hidden shift needs at least `2 ^ (n / 2) - 2` queries: `Ω(2 ^ (n / 2))`. -/
theorem classical_lower_bound (k : ℕ) (A : ClassicalAlgo n)
    (hA : ∀ (f : BV n → BV n) (s : BV n), IsSimon f s → A.output (transcript A f k) = s) :
    2 ^ (n / 2) ≤ k + 2 := by
  have h := classical_lower_bound_raw k A hA
  have h2 : 2 ^ (n / 2) * 2 ^ (n / 2) ≤ (k + 2) * (k + 2) := by
    calc 2 ^ (n / 2) * 2 ^ (n / 2) = 2 ^ (n / 2 + n / 2) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ k * k + 2 := h
      _ ≤ (k + 2) * (k + 2) := by nlinarith
  by_contra hlt
  push_neg at hlt
  nlinarith

/-! ## Main theorem -/

/--
**Simon's problem**: solved with `O(n)` quantum queries, but requiring `Ω(2 ^ (n/2))`
classical queries.

1. (Quantum step) Every measurement outcome of the standard Simon circuit with nonzero
   amplitude is orthogonal to the hidden shift `s`.
2. (Quantum query count) At most `n` such outcomes suffice to determine `s` uniquely among
   all nonzero strings.
3. (Classical lower bound) Every deterministic classical algorithm that always finds `s`
   with `k` queries satisfies `2 ^ (n/2) ≤ k + 2`.
-/
theorem simon_algorithm :
    (∀ (n : ℕ) (f : BV n → BV n) (s y v : BV n), IsSimon f s → amp f y v ≠ 0 →
        dotp s y = 0) ∧
    (∀ (n : ℕ) (s : BV n), s ≠ 0 → ∃ Y : Finset (BV n), Y.card ≤ n ∧
        (∀ y ∈ Y, dotp s y = 0) ∧
        ∀ t : BV n, (∀ y ∈ Y, dotp t y = 0) → t = 0 ∨ t = s) ∧
    (∀ (n k : ℕ) (A : ClassicalAlgo n),
        (∀ (f : BV n → BV n) (s : BV n), IsSimon f s → A.output (transcript A f k) = s) →
        2 ^ (n / 2) ≤ k + 2) :=
  ⟨fun _ _ _ _ _ h hy => dotp_eq_zero_of_amp_ne_zero h _ _ hy,
   fun _ s hs => exists_determining_set s hs,
   fun _ k A hA => classical_lower_bound k A hA⟩

end QI


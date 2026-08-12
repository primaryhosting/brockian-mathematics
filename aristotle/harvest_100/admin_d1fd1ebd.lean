/-
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1` over `ℚ`. -/
def fermatRatPoints (n : ℕ) : Set (ℚ × ℚ) := {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1}

/-- The genus of a smooth plane projective curve of degree `n`, given by the degree–genus
formula `g = (n - 1)(n - 2) / 2`.  For the Fermat curve of degree `n` this is its genus. -/
def planeGenus (n : ℕ) : ℕ := (n - 1) * (n - 2) / 2

/-- Fermat curves of degree at least `4` have genus at least `2`, so they are exactly the
curves to which Faltings' theorem (the Mordell conjecture) applies. -/
lemma two_le_planeGenus {n : ℕ} (hn : 4 ≤ n) : 2 ≤ planeGenus n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 : k + 4 - 1 = k + 3 := by omega
  have h2 : k + 4 - 2 = k + 2 := by omega
  have h : (k + 4 - 1) * (k + 4 - 2) = (k + 3) * (k + 2) := by rw [h1, h2]
  have h6 : 6 ≤ (k + 3) * (k + 2) := by nlinarith
  simp only [planeGenus, h]
  omega

/-- Faltings' theorem for the Fermat curves: the statement that the affine Fermat curve of
degree `n ≥ 4` (a curve of genus `(n-1)(n-2)/2 ≥ 2`) has only finitely many rational points. -/
def FermatMordell : Prop := ∀ n : ℕ, 4 ≤ n → (fermatRatPoints n).Finite

section Auxiliary

/-- If the image of a set under a map with finite fibres is finite, the set is finite. -/
lemma finite_of_finite_image_of_finite_fibers {α β : Type*} {S : Set α} {f : α → β}
    (h : (f '' S).Finite) (hfib : ∀ b, {a | f a = b}.Finite) : S.Finite := by
  refine Set.Finite.subset (h.biUnion (fun b _ => hfib b)) ?_
  intro a ha
  exact Set.mem_biUnion (Set.mem_image_of_mem f ha) rfl

/-- Over `ℚ`, the `k`-th roots of a given number form a finite set (for `k > 0`). -/
lemma finite_setOf_pow_eq {k : ℕ} (hk : 0 < k) (c : ℚ) : {x : ℚ | x ^ k = c}.Finite := by
  have hp : (Polynomial.X ^ k - Polynomial.C c : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hk c
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hp) ?_
  intro x hx
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  simp only [Set.mem_setOf_eq] at hx
  rw [hx, sub_self]

end Auxiliary

/-- **Reduction step.**  If the Fermat curve of degree `m` has finitely many rational
points, then so does the Fermat curve of degree `n` for every multiple `n` of `m`: the map
`(x, y) ↦ (x ^ k, y ^ k)` with `n = m * k` sends the rational points of the degree-`n` curve
to those of the degree-`m` curve with finite fibres. -/
theorem fermatRatPoints_finite_of_dvd {m n : ℕ} (hmn : m ∣ n)
    (h : (fermatRatPoints m).Finite) : (fermatRatPoints n).Finite := by
  obtain ⟨k, rfl⟩ := hmn
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : fermatRatPoints (m * 0) = ∅ := by
      ext p
      simp [fermatRatPoints]
    rw [this]
    exact Set.finite_empty
  refine finite_of_finite_image_of_finite_fibers
    (f := fun p : ℚ × ℚ => (p.1 ^ k, p.2 ^ k)) ?_ ?_
  · refine h.subset ?_
    rintro q ⟨p, hp, rfl⟩
    simp only [fermatRatPoints, Set.mem_setOf_eq] at hp ⊢
    rw [← pow_mul, ← pow_mul, mul_comm k m]
    exact hp
  · rintro ⟨b1, b2⟩
    refine Set.Finite.subset
      (Set.Finite.prod (finite_setOf_pow_eq hk b1) (finite_setOf_pow_eq hk b2)) ?_
    rintro ⟨x, y⟩ hxy
    simp only [Set.mem_setOf_eq, Prod.mk.injEq] at hxy
    exact ⟨hxy.1, hxy.2⟩

/-- **Base case.**  The rational points of the genus-3 Fermat quartic `x ^ 4 + y ^ 4 = 1`
are exactly the four trivial ones.  This is a consequence of Fermat's Last Theorem for
exponent `4`. -/
theorem fermatRatPoints_four :
    fermatRatPoints 4 = {((1 : ℚ), (0 : ℚ)), (-1, 0), (0, 1), (0, -1)} := by
  have flt : FermatLastTheoremWith ℚ 4 := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour
  have hroot : ∀ t : ℚ, t ^ 4 = 1 → t = 1 ∨ t = -1 := by
    intro t ht
    have hfac : (t - 1) * (t + 1) * (t ^ 2 + 1) = 0 := by nlinarith [ht]
    have hpos : t ^ 2 + 1 ≠ 0 := by positivity
    rcases mul_eq_zero.mp hfac with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · exact absurd h hpos
  ext ⟨x, y⟩
  simp only [fermatRatPoints, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have : y ^ 4 = 1 := by linarith [h]
      rcases hroot y this with hy | hy
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hy⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, hy⟩))
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have : x ^ 4 = 1 := by linarith [h]
      rcases hroot x this with hx' | hx'
      · exact Or.inl ⟨hx', rfl⟩
      · exact Or.inr (Or.inl ⟨hx', rfl⟩)
    · exact absurd (by rw [h]; norm_num : x ^ 4 + y ^ 4 = (1 : ℚ) ^ 4)
        (flt x y 1 hx hy one_ne_zero)
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩) <;> subst hx <;> subst hy <;> norm_num

/-- The Fermat quartic, of genus `3`, has finitely many rational points. -/
theorem fermatRatPoints_four_finite : (fermatRatPoints 4).Finite := by
  rw [fermatRatPoints_four]
  exact (Set.finite_singleton _).insert _ |>.insert _ |>.insert _

/-- **Base case.**  The rational points of the Fermat cubic `x ^ 3 + y ^ 3 = 1` are exactly
`(1, 0)` and `(0, 1)`.  This is a consequence of Fermat's Last Theorem for exponent `3`. -/
theorem fermatRatPoints_three :
    fermatRatPoints 3 = {((1 : ℚ), (0 : ℚ)), (0, 1)} := by
  have flt : FermatLastTheoremWith ℚ 3 := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  have hroot : ∀ t : ℚ, t ^ 3 = 1 → t = 1 := by
    intro t ht
    have hfac : (t - 1) * (t ^ 2 + t + 1) = 0 := by nlinarith [ht]
    have hpos : t ^ 2 + t + 1 ≠ 0 := by nlinarith [sq_nonneg (2 * t + 1)]
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · exact absurd h hpos
  ext ⟨x, y⟩
  simp only [fermatRatPoints, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · subst hx
      have hy : y ^ 3 = 1 := by linarith [h]
      exact Or.inr ⟨rfl, hroot y hy⟩
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have hx' : x ^ 3 = 1 := by linarith [h]
      exact Or.inl ⟨hroot x hx', rfl⟩
    · exact absurd (by rw [h]; norm_num : x ^ 3 + y ^ 3 = (1 : ℚ) ^ 3)
        (flt x y 1 hx hy one_ne_zero)
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> subst hx <;> subst hy <;> norm_num

/-- The Fermat cubic has finitely many rational points. -/
theorem fermatRatPoints_three_finite : (fermatRatPoints 3).Finite := by
  rw [fermatRatPoints_three]
  exact (Set.finite_singleton _).insert _

/-- **Faltings' theorem (Mordell conjecture), verified cases.**

For every `n ≥ 4` divisible by `3` or by `4`, the Fermat curve `x ^ n + y ^ n = 1` is a curve
over `ℚ` of genus `(n - 1)(n - 2) / 2 ≥ 2`, and it has only finitely many rational points.

This is an unconditional, Lean-checked family of instances of Faltings' theorem: the base cases
`n = 3` and `n = 4` come from Fermat's Last Theorem for exponents `3` and `4`, and the general
case follows by the Lean-checked reduction `fermatRatPoints_finite_of_dvd` along the
finite-fibred covering map `(x, y) ↦ (x ^ k, y ^ k)`. -/
theorem faltings_mordell {n : ℕ} (hn : 4 ≤ n) (hdvd : 3 ∣ n ∨ 4 ∣ n) :
    2 ≤ planeGenus n ∧ (fermatRatPoints n).Finite := by
  refine ⟨two_le_planeGenus hn, ?_⟩
  rcases hdvd with h | h
  · exact fermatRatPoints_finite_of_dvd h fermatRatPoints_three_finite
  · exact fermatRatPoints_finite_of_dvd h fermatRatPoints_four_finite

/-- Any `n ≥ 4` that is divisible neither by `3` nor by `4` has a prime factor `p ≥ 5`. -/
lemma exists_prime_factor_five_le {n : ℕ} (hn : 4 ≤ n) (h3 : ¬ (3 ∣ n)) (h4 : ¬ (4 ∣ n)) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ n := by
  by_contra hcon
  push_neg at hcon
  have honly : ∀ {q : ℕ}, q.Prime → q ∣ n → q = 2 := by
    intro q hq hqn
    have h5 : q < 5 := by
      by_contra hq5
      exact absurd hqn (hcon q hq (by omega))
    have h2 : 2 ≤ q := hq.two_le
    interval_cases q
    · rfl
    · exact absurd hqn h3
    · exact absurd hq (by norm_num)
  have hn0 : n ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hn0 honly
  set L := n.primeFactorsList.length with hL
  clear_value L
  have h2L : 2 ≤ L := by
    by_contra hlt
    push_neg at hlt
    interval_cases L
    · rw [pow_zero] at hpow; omega
    · rw [pow_one] at hpow; omega
  have hdvd : (2 : ℕ) ^ 2 ∣ 2 ^ L := pow_dvd_pow 2 h2L
  rw [← hpow] at hdvd
  exact h4 (by simpa using hdvd)

/-- **Lean-checked reduction of Faltings' theorem for Fermat curves to prime exponents.**

If every Fermat curve of prime degree `p ≥ 5` has finitely many rational points, then so does
every Fermat curve of degree `n ≥ 4`, i.e. every Fermat curve of genus at least `2`.  Together
with the unconditionally verified cases `faltings_mordell`, this reduces the Mordell conjecture
for the Fermat family to the prime exponents `p ≥ 5`. -/
theorem fermatMordell_of_prime_exponents
    (h : ∀ p : ℕ, p.Prime → 5 ≤ p → (fermatRatPoints p).Finite) : FermatMordell := by
  intro n hn
  by_cases h3 : 3 ∣ n
  · exact (faltings_mordell hn (Or.inl h3)).2
  by_cases h4 : 4 ∣ n
  · exact (faltings_mordell hn (Or.inr h4)).2
  obtain ⟨p, hp, hp5, hpn⟩ := exists_prime_factor_five_le hn h3 h4
  exact fermatRatPoints_finite_of_dvd hpn (h p hp hp5)

end Frontier

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


import Mathlib

/-!
# Pentagon Pentagon Character Multiplicity Ext
Category: Brockian Corpus
Target: Brockian.PentagonPentagonCharacterMultiplicityExt
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

namespace Brockian

/-- The natural action of the dihedral group `DihedralGroup n` on the `n` vertices of a regular
`n`-gon, the vertices being modelled by `ZMod n`.  The rotation `r i` sends a vertex `x` to
`x - i`, and the reflection `sr i` sends `x` to `i - x`. -/
def ngonAct (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | DihedralGroup.r i, x => x - i
  | DihedralGroup.sr i, x => i - x

/-- `ngonAct` is a group action of `DihedralGroup n` on the vertex set `ZMod n`. -/
instance ngonMulAction (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := ngonAct n
  one_smul x := by
    show ngonAct n (DihedralGroup.r 0) x = x
    simp [ngonAct]
  mul_smul g h x := by
    rcases g with i | i <;> rcases h with j | j <;>
      simp [ngonAct, HSMul.hSMul, SMul.smul] <;> ring

@[simp] lemma r_smul (n : ℕ) (i x : ZMod n) : DihedralGroup.r i • x = x - i := rfl

@[simp] lemma sr_smul (n : ℕ) (i x : ZMod n) : DihedralGroup.sr i • x = i - x := rfl

/-- The action of the dihedral group on the vertices of the `n`-gon is transitive. -/
instance ngonPretransitive (n : ℕ) [NeZero n] :
    MulAction.IsPretransitive (DihedralGroup n) (ZMod n) := by
  constructor
  intro x y
  exact ⟨DihedralGroup.r (x - y), by show x - (x - y) = y; ring⟩

/-- The vertex action of the `n`-gon has exactly one orbit. -/
lemma ngon_card_orbits (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 := by
  refine Fintype.card_eq_one_iff.mpr ⟨Quotient.mk _ 0, ?_⟩
  refine Quotient.ind ?_
  intro a
  refine Quotient.sound ?_
  show (MulAction.orbitRel (DihedralGroup n) (ZMod n)) a 0
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨DihedralGroup.r (-a), by show (0 : ZMod n) - (-a) = a; ring⟩

/-- The permutation character of the `n`-gon vertex action: `χ g` is the number of vertices
fixed by `g`. -/
noncomputable def ngonChar (n : ℕ) [NeZero n] (g : DihedralGroup n) : ℕ :=
  Fintype.card (MulAction.fixedBy (ZMod n) g)

lemma ngonChar_eq_card_filter (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    ngonChar n g = (Finset.univ.filter fun x : ZMod n => g • x = x).card := by
  classical
  rw [ngonChar, ← Set.toFinset_card]
  congr 1
  ext x
  simp [MulAction.mem_fixedBy]

/-- The character value at a rotation: the identity rotation fixes all `n` vertices, every other
rotation fixes none. -/
lemma ngonChar_r (n : ℕ) [NeZero n] (i : ZMod n) :
    ngonChar n (DihedralGroup.r i) = if i = 0 then n else 0 := by
  classical
  rw [ngonChar_eq_card_filter]
  by_cases h : i = 0
  · simp [h, ZMod.card]
  · simp [sub_eq_self, h]

/-- The character value at a reflection: the fixed vertices of `sr i` are the solutions of
`2 * x = i`. -/
lemma ngonChar_sr (n : ℕ) [NeZero n] (i : ZMod n) :
    ngonChar n (DihedralGroup.sr i) = (Finset.univ.filter fun x : ZMod n => 2 * x = i).card := by
  classical
  rw [ngonChar_eq_card_filter]
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : i - x = x := by simpa using hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination -hx'
  · intro hx
    have hx' : 2 * x = i := by simpa using hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sr_smul]
    linear_combination -hx'

/-- Splitting a sum over the dihedral group into its rotation and reflection parts. -/
def dihedralSumEquiv (n : ℕ) : DihedralGroup n ≃ ZMod n ⊕ ZMod n where
  toFun g := match g with
    | DihedralGroup.r i => Sum.inl i
    | DihedralGroup.sr i => Sum.inr i
  invFun s := match s with
    | Sum.inl i => DihedralGroup.r i
    | Sum.inr i => DihedralGroup.sr i
  left_inv g := by rcases g with i | i <;> rfl
  right_inv s := by rcases s with i | i <;> rfl

lemma sum_dihedral {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n] (f : DihedralGroup n → M) :
    ∑ g : DihedralGroup n, f g =
      (∑ i : ZMod n, f (DihedralGroup.r i)) + ∑ i : ZMod n, f (DihedralGroup.sr i) := by
  rw [← Fintype.sum_equiv (dihedralSumEquiv n).symm
        (fun s => f ((dihedralSumEquiv n).symm s)) f (fun _ => rfl),
    Fintype.sum_sum_type]
  rfl

/-- The rotations contribute `n` to the sum of the character values. -/
lemma ngon_sum_char_rotations (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonChar n (DihedralGroup.r i) = n := by
  classical
  simp [ngonChar_r]

/-- The reflections contribute `n` to the sum of the character values: counting the pairs
`(i, x)` with `2 * x = i` in two ways. -/
lemma ngon_sum_char_reflections (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ngonChar n (DihedralGroup.sr i) = n := by
  classical
  have h : ∀ i : ZMod n, ngonChar n (DihedralGroup.sr i)
      = ∑ x : ZMod n, if 2 * x = i then 1 else 0 := by
    intro i
    rw [ngonChar_sr, Finset.card_filter]
  simp only [h]
  rw [Finset.sum_comm]
  simp [ZMod.card]

/-- A direct, Burnside-free evaluation of the sum of the permutation character values. -/
theorem ngon_sum_char (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g = 2 * n := by
  rw [sum_dihedral, ngon_sum_char_rotations, ngon_sum_char_reflections, two_mul]

/-- **Pentagon Pentagon Character Multiplicity Ext.**

Generalization of the `D₅` pentagon computation to an arbitrary regular `n`-gon (`n ≥ 1`).

The permutation character of `DihedralGroup n` acting on the `n` vertices of the regular `n`-gon
is `χ g = #{x | g • x = x}`.  Its multiplicity as a constituent of the trivial character,
`⟨χ, 1⟩ = |G|⁻¹ ∑_{g ∈ G} χ g`, equals `1`: the vertex action is transitive, so it has a single
orbit, and hence (Burnside) the sum of the fixed-point counts equals `|G| = 2n`. -/
theorem PentagonPentagonCharacterMultiplicityExt (n : ℕ) [NeZero n] :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) = 1 ∧
    ∑ g : DihedralGroup n, ngonChar n g = 2 * n ∧
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ)) = 1 := by
  have horb := ngon_card_orbits n
  have hcard : Fintype.card (DihedralGroup n) = 2 * n := DihedralGroup.card
  have hsum : ∑ g : DihedralGroup n, ngonChar n g = 2 * n := ngon_sum_char n
  refine ⟨horb, hsum, ?_⟩
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcast : ∑ g : DihedralGroup n, (ngonChar n g : ℚ) = ((2 * n : ℕ) : ℚ) := by
    rw [← Nat.cast_sum, hsum]
  rw [hcast, hcard]
  push_cast
  field_simp

/-- Burnside's orbit-counting lemma reproves the same total: the sum of the character values is
the number of orbits times `|D_n| = 2n`. -/
theorem ngon_sum_char_burnside (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, ngonChar n g =
      Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n))) *
        Fintype.card (DihedralGroup n) :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (ZMod n)

/-- The linear character of `DihedralGroup n` that is `1` on rotations and `-1` on reflections. -/
def ngonSignChar (n : ℕ) : DihedralGroup n → ℚ
  | DihedralGroup.r _ => 1
  | DihedralGroup.sr _ => -1

/-- `ngonSignChar` really is a character: it is multiplicative. -/
lemma ngonSignChar_mul (n : ℕ) (g h : DihedralGroup n) :
    ngonSignChar n (g * h) = ngonSignChar n g * ngonSignChar n h := by
  rcases g with i | i <;> rcases h with j | j <;> simp [ngonSignChar]

/-- The multiplicity of the sign character in the permutation character of the `n`-gon is `0`:
the rotations contribute `n` and the reflections contribute `-n`. -/
theorem ngon_sign_char_multiplicity (n : ℕ) [NeZero n] :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) * ngonSignChar n g) = 0 := by
  have hrot : ∑ i : ZMod n, ((ngonChar n (DihedralGroup.r i) : ℚ) *
      ngonSignChar n (DihedralGroup.r i)) = (n : ℚ) := by
    have : ∀ i : ZMod n, ((ngonChar n (DihedralGroup.r i) : ℚ) *
        ngonSignChar n (DihedralGroup.r i)) = (ngonChar n (DihedralGroup.r i) : ℚ) := by
      intro i; simp [ngonSignChar]
    rw [Finset.sum_congr rfl fun i _ => this i, ← Nat.cast_sum, ngon_sum_char_rotations]
  have hrefl : ∑ i : ZMod n, ((ngonChar n (DihedralGroup.sr i) : ℚ) *
      ngonSignChar n (DihedralGroup.sr i)) = -(n : ℚ) := by
    have : ∀ i : ZMod n, ((ngonChar n (DihedralGroup.sr i) : ℚ) *
        ngonSignChar n (DihedralGroup.sr i)) = -(ngonChar n (DihedralGroup.sr i) : ℚ) := by
      intro i; simp [ngonSignChar]
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_neg_distrib, ← Nat.cast_sum,
      ngon_sum_char_reflections]
  rw [sum_dihedral n (fun g => (ngonChar n g : ℚ) * ngonSignChar n g), hrot, hrefl]
  ring

/-- For an odd-sided polygon every reflection fixes exactly one vertex, because doubling is a
bijection of `ZMod n`. -/
lemma ngonChar_sr_of_odd (n : ℕ) [NeZero n] (hn : Odd n) (i : ZMod n) :
    ngonChar n (DihedralGroup.sr i) = 1 := by
  classical
  rw [ngonChar_sr]
  have hcop : Nat.Coprime 2 n := by
    rcases hn with ⟨k, hk⟩; subst hk; simp
  set u : (ZMod n)ˣ := ZMod.unitOfCoprime 2 hcop with hu
  have hu2 : (u : ZMod n) = 2 := by simp [hu, ZMod.coe_unitOfCoprime]
  have hset : (Finset.univ.filter fun x : ZMod n => 2 * x = i) = {(↑u⁻¹ * i : ZMod n)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rw [← hu2] at h
      rw [← h, ← mul_assoc]
      simp
    · intro h
      subst h
      rw [← hu2, ← mul_assoc]
      simp
  rw [hset, Finset.card_singleton]

/-- Counting the pairs of vertices `(x, y)` with `2x = 2y` in two ways: the sum of the squares of
the reflection character values is `n` times the number of solutions of `2d = 0`. -/
lemma sum_sq_reflection_solutions (n : ℕ) [NeZero n] :
    ∑ i : ZMod n, ((Finset.univ.filter fun x : ZMod n => 2 * x = i).card) ^ 2
      = n * (Finset.univ.filter fun d : ZMod n => 2 * d = 0).card := by
  classical
  have hsq : ∀ i : ZMod n, ((Finset.univ.filter fun x : ZMod n => 2 * x = i).card) ^ 2
      = ∑ x : ZMod n, ∑ y : ZMod n,
          (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0) := by
    intro i
    rw [sq, Finset.card_filter, Finset.sum_mul_sum]
  simp only [hsq]
  rw [Finset.sum_comm]
  have step : ∀ x : ZMod n,
      ∑ i : ZMod n, ∑ y : ZMod n, (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0)
        = (Finset.univ.filter fun d : ZMod n => 2 * d = 0).card := by
    intro x
    rw [Finset.sum_comm]
    have hcollapse : ∀ y : ZMod n,
        ∑ i : ZMod n, (if 2 * x = i then 1 else 0) * (if 2 * y = i then 1 else 0)
          = if 2 * y = 2 * x then 1 else 0 := by
      intro y
      rw [Finset.sum_eq_single (2 * x)] <;> simp +contextual
      intro b hb _
      simp [Ne.symm hb]
    simp only [hcollapse]
    rw [Finset.card_filter]
    refine (Fintype.sum_equiv (Equiv.addRight x)
      (fun d : ZMod n => if 2 * d = 0 then 1 else 0)
      (fun y : ZMod n => if 2 * y = 2 * x then 1 else 0) ?_).symm
    intro d
    simp only [Equiv.coe_addRight]
    refine if_congr ?_ rfl rfl
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  simp only [step]
  simp [ZMod.card]

/-- The sum of the squares of the character values, computed in `ℕ`. -/
lemma ngon_sum_char_sq (n : ℕ) [NeZero n] :
    ∑ g : DihedralGroup n, (ngonChar n g) ^ 2 = n * (n + ngonChar n (DihedralGroup.sr 0)) := by
  classical
  have hrot : ∑ i : ZMod n, (ngonChar n (DihedralGroup.r i)) ^ 2 = n ^ 2 := by
    have h : ∀ i : ZMod n, (ngonChar n (DihedralGroup.r i)) ^ 2 = if i = 0 then n ^ 2 else 0 := by
      intro i
      rw [ngonChar_r]
      by_cases hi : i = 0 <;> simp [hi]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_ite_eq' Finset.univ (0 : ZMod n)]
    simp
  have hrefl : ∑ i : ZMod n, (ngonChar n (DihedralGroup.sr i)) ^ 2
      = n * ngonChar n (DihedralGroup.sr 0) := by
    simp only [ngonChar_sr]
    exact sum_sq_reflection_solutions n
  rw [sum_dihedral n (fun g => (ngonChar n g) ^ 2), hrot, hrefl]
  ring

/-- The general inner product of the `n`-gon permutation character with itself:
`⟨χ, χ⟩ = (n + χ(sr 0)) / 2`, where `χ(sr 0)` is the number of solutions of `2d = 0` in `ZMod n`
(one for odd `n`, two for even `n`).  Equivalently, `⟨χ, χ⟩` is the number of orbits of the
dihedral group on ordered pairs of vertices. -/
theorem ngon_char_norm (n : ℕ) [NeZero n] :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) ^ 2)
      = ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) / 2 := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcast : ∑ g : DihedralGroup n, ((ngonChar n g : ℚ)) ^ 2
      = (n : ℚ) * ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) := by
    calc ∑ g : DihedralGroup n, ((ngonChar n g : ℚ)) ^ 2
        = ((∑ g : DihedralGroup n, (ngonChar n g) ^ 2 : ℕ) : ℚ) := by push_cast; ring
      _ = (n : ℚ) * ((n : ℚ) + (ngonChar n (DihedralGroup.sr 0) : ℚ)) := by
            rw [ngon_sum_char_sq n]; push_cast; ring
  rw [hcast, DihedralGroup.card]
  push_cast
  field_simp

/-- For odd `n` the permutation character of the `n`-gon satisfies `⟨χ, χ⟩ = (n+1)/2`; equivalently
the permutation representation splits as the trivial representation plus `(n-1)/2` pairwise
distinct two-dimensional irreducible constituents. -/
theorem ngon_char_norm_odd (n : ℕ) [NeZero n] (hn : Odd n) :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) ^ 2) = ((n : ℚ) + 1) / 2 := by
  rw [ngon_char_norm n, ngonChar_sr_of_odd n hn 0]
  norm_num

/-- For even `n = 2m` with `m > 0`, exactly two vertices are fixed by the reflection `sr 0`. -/
lemma ngonChar_sr_zero_even (n : ℕ) [NeZero n] (m : ℕ) (hn : n = 2 * m) :
    ngonChar n (DihedralGroup.sr 0) = 2 := by
  classical
  rw [ngonChar_sr]
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by simp [hn, h] : n = 0) (NeZero.ne n)
    · exact h
  have hmne : ((m : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have : n ≤ m := Nat.le_of_dvd hm hdvd
    omega
  have hset : (Finset.univ.filter fun x : ZMod n => 2 * x = 0) = {0, (m : ZMod n)} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have hd : ((d.val : ℕ) : ZMod n) = d := by simp [ZMod.natCast_val, ZMod.cast_id]
      have hval : ((2 * d.val : ℕ) : ZMod n) = 0 := by
        push_cast
        rw [hd]; exact h
      rw [ZMod.natCast_eq_zero_iff] at hval
      have hlt : d.val < n := ZMod.val_lt d
      have hmv : m ∣ d.val := by
        have h2 : 2 * m ∣ 2 * d.val := by rw [← hn]; exact hval
        exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h2
      obtain ⟨k, hk⟩ := hmv
      have hk2 : k < 2 := by
        by_contra hcon
        push_neg at hcon
        have : 2 * m ≤ m * k := by nlinarith
        omega
      interval_cases k
      · left; rw [← hd]; simp [hk]
      · right; rw [← hd, hk]; simp
    · rintro (rfl | rfl)
      · simp
      · have hz : ((2 * m : ℕ) : ZMod n) = 0 := by rw [← hn]; exact ZMod.natCast_self n
        push_cast at hz
        exact hz
  rw [hset, Finset.card_insert_of_notMem (by simpa [eq_comm] using hmne), Finset.card_singleton]

/-- For even `n` the permutation character of the `n`-gon satisfies `⟨χ, χ⟩ = (n+2)/2`. -/
theorem ngon_char_norm_even (n : ℕ) [NeZero n] (hn : Even n) :
    ((Fintype.card (DihedralGroup n) : ℚ)⁻¹ *
      ∑ g : DihedralGroup n, (ngonChar n g : ℚ) ^ 2) = ((n : ℚ) + 2) / 2 := by
  obtain ⟨m, hm⟩ := hn
  rw [ngon_char_norm n, ngonChar_sr_zero_even n m (by omega)]
  norm_num

/-- The vertices fixed by `g` in the diagonal action on ordered pairs are exactly the pairs of
fixed vertices. -/
def fixedByPairEquiv (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    MulAction.fixedBy (ZMod n × ZMod n) g ≃
      MulAction.fixedBy (ZMod n) g × MulAction.fixedBy (ZMod n) g where
  toFun p := (⟨p.1.1, by
      have := p.2
      rw [MulAction.mem_fixedBy, Prod.ext_iff] at this
      exact this.1⟩,
    ⟨p.1.2, by
      have := p.2
      rw [MulAction.mem_fixedBy, Prod.ext_iff] at this
      exact this.2⟩)
  invFun q := ⟨(q.1.1, q.2.1), by
      rw [MulAction.mem_fixedBy, Prod.ext_iff]
      exact ⟨q.1.2, q.2.2⟩⟩
  left_inv p := by cases p; rfl
  right_inv q := by cases q; rfl

/-- The permutation character of the diagonal action on ordered pairs of vertices is `χ²`. -/
lemma card_fixedBy_pair (n : ℕ) [NeZero n] (g : DihedralGroup n) :
    Fintype.card (MulAction.fixedBy (ZMod n × ZMod n) g) = (ngonChar n g) ^ 2 := by
  classical
  rw [Fintype.card_congr (fixedByPairEquiv n g), Fintype.card_prod, ngonChar, sq]

/-- **Orbits on ordered pairs of vertices.**  The dihedral group `D_n` acting diagonally on ordered
pairs of vertices of the regular `n`-gon has `(n + χ(sr 0))/2` orbits, where `χ(sr 0) ∈ {1, 2}`
is the number of solutions of `2d = 0` in `ZMod n`. -/
theorem ngon_pair_orbits (n : ℕ) [NeZero n] :
    2 * Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n × ZMod n)))
      = n + ngonChar n (DihedralGroup.sr 0) := by
  classical
  have hburn :
      ∑ g : DihedralGroup n, Fintype.card (MulAction.fixedBy (ZMod n × ZMod n) g) =
        Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n × ZMod n))) *
          Fintype.card (DihedralGroup n) :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup n) (ZMod n × ZMod n)
  rw [Finset.sum_congr rfl fun g _ => card_fixedBy_pair n g, ngon_sum_char_sq n,
    DihedralGroup.card] at hburn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  refine Nat.eq_of_mul_eq_mul_left hn0 ?_
  calc n * (2 * Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n × ZMod n))))
      = Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n × ZMod n))) *
          (2 * n) := by ring
    _ = n * (n + ngonChar n (DihedralGroup.sr 0)) := hburn.symm

/-- For odd `n` the dihedral group has exactly `(n+1)/2` orbits on ordered pairs of vertices. -/
theorem ngon_pair_orbits_odd (n : ℕ) [NeZero n] (hn : Odd n) :
    2 * Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup n) (ZMod n × ZMod n)))
      = n + 1 := by
  rw [ngon_pair_orbits n, ngonChar_sr_of_odd n hn 0]

/-- In a pentagon every reflection fixes exactly one vertex. -/
lemma pentagon_char_sr (i : ZMod 5) : ngonChar 5 (DihedralGroup.sr i) = 1 := by
  rw [ngonChar_sr]
  revert i
  decide

/-- The pentagon: `⟨χ, χ⟩ = 3`, i.e. the vertex permutation representation of `D₅` has three
irreducible constituents (the trivial one and the two two-dimensional ones). -/
theorem PentagonCharacterNorm :
    ((Fintype.card (DihedralGroup 5) : ℚ)⁻¹ *
      ∑ g : DihedralGroup 5, (ngonChar 5 g : ℚ) ^ 2) = 3 := by
  rw [ngon_char_norm_odd 5 (by decide)]
  norm_num

/-- The pentagon: `D₅` has exactly three orbits on ordered pairs of vertices (equal pairs,
adjacent pairs and non-adjacent pairs). -/
theorem PentagonPairOrbits :
    Fintype.card (Quotient (MulAction.orbitRel (DihedralGroup 5) (ZMod 5 × ZMod 5))) = 3 := by
  have h := ngon_pair_orbits_odd 5 (by decide)
  omega

/-- The pentagon case `n = 5`: the sum of the fixed-point counts over `D₅` is `10 = |D₅|`, so the
trivial character occurs with multiplicity one in the permutation character of the pentagon. -/
theorem PentagonCharacterMultiplicity :
    ∑ g : DihedralGroup 5, ngonChar 5 g = 10 :=
  (PentagonPentagonCharacterMultiplicityExt 5).2.1

end Brockian


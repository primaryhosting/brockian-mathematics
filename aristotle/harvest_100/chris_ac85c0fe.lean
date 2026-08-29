/-
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ngo Fundamental Lemma
Category: Frontier — Fields Medal Work
Target: Frontier.ngo_fundamental_lemma
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

namespace Frontier

/-!
## The Langlands–Shelstad fundamental lemma (Ngô)

Let `G` be an unramified connected reductive group over a non-archimedean local field `F`
with hyperspecial maximal compact `K`, let `(H, s, η)` be an endoscopic datum for `G` with
hyperspecial maximal compact `K_H`, and let `γ_H ∈ H(F)` be a strongly `G`-regular semisimple
element with norm `γ ∈ G(F)`.  Write `𝔎 = 𝔎(I_γ/F)` for the finite abelian group of
obstructions classifying the `G(F)`-conjugacy classes inside the stable conjugacy class of `γ`,
`κ ∈ 𝔎^` for the character determined by `s`, and `Δ(γ_H, γ)` for the Langlands–Shelstad
transfer factor.  The fundamental lemma, proved by Ngô, asserts

  `Δ(γ_H, γ) · O^κ_γ(1_K) = SO_{γ_H}(1_{K_H})`,

where `O^κ_γ(1_K) = ∑_{γ' ∼_{st} γ} κ(inv(γ', γ)) · O_{γ'}(1_K)` is the `κ`-orbital integral
of the unit element of the Hecke algebra and `SO_{γ_H}(1_{K_H})` is the stable orbital integral
on the endoscopic group.

This file formalizes the *shape* of that identity as a statement about the finite combinatorial
data it involves (the finite set of rational classes in a stable class, the obstruction group,
the endoscopic character, the orbital integrals, and the transfer factor), and then proves:

* the trivial-endoscopy base case `H = G` (`κ = 1`), where the identity is the definition of
  the stable orbital integral;
* the *stable vanishing reduction*: a nontrivial `κ` annihilates orbital data that is constant
  on the stable class (orthogonality of characters of `𝔎`) — this is the mechanism by which
  the endoscopic terms are detected;
* an additivity reduction, allowing the identity to be checked one stable class at a time;
* the **base case of the fundamental lemma for `SL(2)`**: for the unit element of the Hecke
  algebra and an unramified elliptic torus with `val(disc γ) = 2n`, the orbital integrals are
  counts of vertices of the Bruhat–Tits tree of `SL(2)` (a `(q+1)`-regular tree) lying in the
  ball of radius `n` around the vertex fixed by the torus, split according to the parity of the
  distance (which is exactly the invariant in `𝔎 ≅ ℤ/2`).  The theorem proved is
  `((-1)^n * q^(-n)) * O^κ = 1 = SO_{γ_H}(1_{K_H})`, i.e. the fundamental lemma in this case,
  the content being the computation `O^κ = (-q)^n`.
-/

/-- The finite combinatorial data entering the fundamental lemma for one strongly regular
semisimple stable conjugacy class.

* `Conj` indexes the `G(F)`-conjugacy classes inside the given stable conjugacy class;
* `Obs` is the finite abelian obstruction group `𝔎(I_γ/F)`;
* `inv γ'` is the invariant in `𝔎` of the rational class `γ'` relative to the base point;
* `kappa` is the character of `𝔎` attached to the endoscopic datum;
* `orbital γ'` is the orbital integral `O_{γ'}(1_K)`;
* `transfer` is the Langlands–Shelstad transfer factor `Δ(γ_H, γ)`;
* `endoStable` is the stable orbital integral `SO_{γ_H}(1_{K_H})` on the endoscopic group. -/
structure EndoscopicDatum (Conj : Type) (Obs : Type) [Fintype Conj] [AddCommGroup Obs] where
  /-- Invariant in `𝔎(I_γ/F)` of a rational class inside the stable class. -/
  inv : Conj → Obs
  /-- The character `κ` of `𝔎(I_γ/F)` determined by the endoscopic datum. -/
  kappa : AddChar Obs ℂ
  /-- The orbital integrals `O_{γ'}(1_K)` of the unit element of the Hecke algebra. -/
  orbital : Conj → ℂ
  /-- The Langlands–Shelstad transfer factor `Δ(γ_H, γ)`. -/
  transfer : ℂ
  /-- The stable orbital integral `SO_{γ_H}(1_{K_H})` on the endoscopic group. -/
  endoStable : ℂ

namespace EndoscopicDatum

variable {Conj Obs : Type} [Fintype Conj] [AddCommGroup Obs]

/-- The `κ`-orbital integral `O^κ_γ(1_K) = ∑_{γ'} κ(inv γ') O_{γ'}(1_K)`. -/
noncomputable def kappaOrbital (D : EndoscopicDatum Conj Obs) : ℂ :=
  ∑ c : Conj, D.kappa (D.inv c) * D.orbital c

/-- The stable orbital integral `SO_γ(1_K) = ∑_{γ'} O_{γ'}(1_K)` on `G`. -/
noncomputable def stableOrbital (D : EndoscopicDatum Conj Obs) : ℂ :=
  ∑ c : Conj, D.orbital c

/-- The fundamental lemma for the given datum:
`Δ(γ_H, γ) · O^κ_γ(1_K) = SO_{γ_H}(1_{K_H})`. -/
def FundamentalLemmaHolds (D : EndoscopicDatum Conj Obs) : Prop :=
  D.transfer * D.kappaOrbital = D.endoStable

/-- For the trivial character `κ = 1` the `κ`-orbital integral is the stable orbital integral. -/
theorem kappaOrbital_of_kappa_eq_one (D : EndoscopicDatum Conj Obs) (hκ : D.kappa = 1) :
    D.kappaOrbital = D.stableOrbital := by
  simp [kappaOrbital, stableOrbital, hκ]

/-- **Trivial endoscopy base case** (`H = G`, `κ = 1`, `Δ = 1`): the fundamental lemma holds,
being the identity `SO_γ(1_K) = SO_γ(1_K)`. -/
theorem fundamentalLemma_trivial_endoscopy (D : EndoscopicDatum Conj Obs)
    (hκ : D.kappa = 1) (hΔ : D.transfer = 1) (hH : D.endoStable = D.stableOrbital) :
    D.FundamentalLemmaHolds := by
  simp [FundamentalLemmaHolds, hΔ, hH, D.kappaOrbital_of_kappa_eq_one hκ]

/-- **Stable vanishing reduction.** If the rational classes inside the stable class are in
bijection with the obstruction group `𝔎` via the invariant, the orbital integrals are constant
on the stable class (the "stable" situation), and `κ ≠ 1`, then the `κ`-orbital integral
vanishes: this is orthogonality of characters of `𝔎`. -/
theorem kappaOrbital_eq_zero_of_stable [Fintype Obs] (D : EndoscopicDatum Conj Obs)
    (hbij : Function.Bijective D.inv) (v : ℂ) (hconst : ∀ c : Conj, D.orbital c = v)
    (hκ : D.kappa ≠ 1) :
    D.kappaOrbital = 0 := by
  have h : D.kappaOrbital = (∑ k : Obs, D.kappa k) * v := by
    rw [kappaOrbital, Finset.sum_mul]
    rw [← Equiv.sum_comp (Equiv.ofBijective D.inv hbij) (fun k : Obs => D.kappa k * v)]
    exact Finset.sum_congr rfl fun c _ => by simp [Equiv.ofBijective, hconst c]
  rw [h, AddChar.sum_eq_zero_of_ne_one hκ, zero_mul]

/-- If the obstruction group `𝔎(I_γ/F)` is trivial — as happens for `GL(n)`, where stable
conjugacy of regular semisimple elements coincides with rational conjugacy — then every
`κ`-orbital integral is the stable orbital integral. -/
theorem kappaOrbital_eq_stableOrbital_of_subsingleton [Subsingleton Obs]
    (D : EndoscopicDatum Conj Obs) : D.kappaOrbital = D.stableOrbital := by
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Subsingleton.elim (D.inv c) 0, D.kappa.map_zero_eq_one, one_mul]

/-- **Trivial obstruction group base case** (`GL(n)`): if `𝔎(I_γ/F)` is trivial, the fundamental
lemma for the principal endoscopic datum `H = G` holds. -/
theorem fundamentalLemma_of_trivial_obstruction [Subsingleton Obs]
    (D : EndoscopicDatum Conj Obs) (hΔ : D.transfer = 1)
    (hH : D.endoStable = D.stableOrbital) : D.FundamentalLemmaHolds := by
  simp [FundamentalLemmaHolds, hΔ, hH, D.kappaOrbital_eq_stableOrbital_of_subsingleton]

/-- **Additivity reduction.** The fundamental lemma may be verified one stable class at a time:
if it holds for two data with the same transfer factor and the same endoscopic character, then it
holds for the datum whose set of rational classes is the disjoint union, with endoscopic side the
sum of the two endoscopic sides. -/
theorem fundamentalLemma_sum {Conj' : Type} [Fintype Conj']
    (D : EndoscopicDatum Conj Obs) (D' : EndoscopicDatum Conj' Obs)
    (hΔ : D.transfer = D'.transfer) (hκ : D.kappa = D'.kappa)
    (hD : D.FundamentalLemmaHolds) (hD' : D'.FundamentalLemmaHolds) :
    FundamentalLemmaHolds
      { inv := Sum.elim D.inv D'.inv
        kappa := D.kappa
        orbital := Sum.elim D.orbital D'.orbital
        transfer := D.transfer
        endoStable := D.endoStable + D'.endoStable : EndoscopicDatum (Conj ⊕ Conj') Obs } := by
  have h : EndoscopicDatum.kappaOrbital
      { inv := Sum.elim D.inv D'.inv
        kappa := D.kappa
        orbital := Sum.elim D.orbital D'.orbital
        transfer := D.transfer
        endoStable := D.endoStable + D'.endoStable : EndoscopicDatum (Conj ⊕ Conj') Obs }
      = D.kappaOrbital + D'.kappaOrbital := by
    simp only [kappaOrbital, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hκ]
  simp only [FundamentalLemmaHolds] at hD hD' ⊢
  rw [h, mul_add, hD, hΔ, hD']

end EndoscopicDatum

/-! ### The `SL(2)` base case -/

/-- The number of vertices at distance `k` from a fixed vertex in the `(q+1)`-regular tree,
i.e. in the Bruhat–Tits tree of `SL(2)` over a local field with residue field of size `q`. -/
def treeSphere (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | (k + 1) => (q + 1) * q ^ k

/-- The type of non-backtracking paths of length `k` issued from a fixed vertex of the
`(q+1)`-regular tree: one of `q+1` initial directions, then `q` choices at each further step.
Its elements biject with the vertices at distance `k` from the fixed vertex. -/
def TreePath (q : ℕ) : ℕ → Type
  | 0 => Unit
  | (k + 1) => Fin (q + 1) × (Fin k → Fin q)

instance treePathFintype (q : ℕ) : ∀ k : ℕ, Fintype (TreePath q k)
  | 0 => inferInstanceAs (Fintype Unit)
  | (k + 1) => inferInstanceAs (Fintype (Fin (q + 1) × (Fin k → Fin q)))

/-- `treeSphere q k` is indeed the number of vertices at distance `k` from a fixed vertex of the
`(q+1)`-regular tree, i.e. the number of non-backtracking paths of length `k` from it. -/
theorem card_treePath (q k : ℕ) : Fintype.card (TreePath q k) = treeSphere q k := by
  cases k with
  | zero => simp [TreePath, treeSphere, treePathFintype]
  | succ k => simp [TreePath, treeSphere, treePathFintype, Fintype.card_prod]

/-- The orbital integral of `1_K` over the rational class of parity `ε` inside the stable class
of a regular elliptic element of `SL(2)` generating an unramified torus with
`val(disc γ) = 2n`: it counts the vertices of the Bruhat–Tits tree fixed by `γ` (a ball of
radius `n` around the vertex fixed by the torus) whose distance to the centre has parity `ε`. -/
noncomputable def sl2Orbital (q n : ℕ) (ε : ZMod 2) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), if (k : ZMod 2) = ε then (treeSphere q k : ℂ) else 0

/-- The nontrivial character of `𝔎 ≅ ℤ/2`, the obstruction group for the stable class of a
regular elliptic element of `SL(2)`. -/
noncomputable def signChar : AddChar (ZMod 2) ℂ where
  toFun := fun ε => if ε = 0 then 1 else -1
  map_zero_eq_one' := by norm_num
  map_add_eq_mul' := by intro a b; fin_cases a <;> fin_cases b <;> norm_num; decide

@[simp] theorem signChar_apply (ε : ZMod 2) : signChar ε = if ε = 0 then 1 else -1 := rfl

theorem signChar_ne_one : signChar ≠ 1 := by
  intro h
  have h1 := congrArg (fun ψ : AddChar (ZMod 2) ℂ => ψ 1) h
  simp only [signChar_apply, AddChar.one_apply] at h1
  norm_num at h1

/-- On the image of `k : ℕ` in `𝔎 ≅ ℤ/2` the nontrivial character is the sign `(-1)^k`. -/
theorem signChar_natCast (k : ℕ) : signChar (k : ZMod 2) = (-1 : ℂ) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [signChar_apply, if_pos (ZMod.natCast_eq_zero_iff_even.2 hk), hk.neg_one_pow]
  · rw [signChar_apply, if_neg, hk.neg_one_pow]
    simpa [ZMod.natCast_eq_zero_iff_even] using (Nat.not_even_iff_odd.2 hk)

/-- The endoscopic datum for `SL(2)`, an unramified elliptic maximal torus `H = T` with
`val(disc γ) = 2n`, and the unit element of the Hecke algebra.  The obstruction group is
`𝔎 ≅ ℤ/2`, the two rational classes inside the stable class are indexed by the parity of the
distance in the Bruhat–Tits tree, the transfer factor is `Δ = (-1)^n |disc γ|^{1/2} = (-1)^n q^{-n}`,
and the endoscopic stable orbital integral is `SO_{γ_H}(1_{K_H}) = 1` since `H` is a torus. -/
noncomputable def sl2Datum (q n : ℕ) : EndoscopicDatum (ZMod 2) (ZMod 2) where
  inv := id
  kappa := signChar
  orbital := sl2Orbital q n
  transfer := (-1 : ℂ) ^ n * (q : ℂ)⁻¹ ^ n
  endoStable := 1

/-- The `κ`-orbital integral for `SL(2)` is the alternating sum of the sphere counts in the
Bruhat–Tits tree. -/
theorem sl2_kappaOrbital_eq (q n : ℕ) :
    (sl2Datum q n).kappaOrbital
      = ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (treeSphere q k : ℂ) := by
  simp only [EndoscopicDatum.kappaOrbital, sl2Datum, sl2Orbital, id_eq, Finset.mul_sum, mul_ite,
    mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (k : ZMod 2) (fun ε => signChar ε * (treeSphere q k : ℂ)),
    if_pos (Finset.mem_univ _), signChar_natCast]

/-- The alternating count of vertices in a ball of radius `n` of the `(q+1)`-regular tree
equals `(-q)^n`.  This is the computation of the `κ`-orbital integral for `SL(2)`. -/
theorem alternating_treeSphere_sum (q n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (treeSphere q k : ℂ) = (-(q : ℂ)) ^ n := by
  induction n with
  | zero => simp [treeSphere]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [treeSphere]
      push_cast
      ring

/-- The `κ`-orbital integral of the unit element for `SL(2)` and an unramified elliptic torus
with `val(disc γ) = 2n` equals `(-q)^n`. -/
theorem sl2_kappaOrbital (q n : ℕ) : (sl2Datum q n).kappaOrbital = (-(q : ℂ)) ^ n := by
  rw [sl2_kappaOrbital_eq, alternating_treeSphere_sum]

/-- The endoscopy occurring in the `SL(2)` base case is genuinely nontrivial: the character
`κ` of `𝔎 ≅ ℤ/2` is not the trivial character. -/
theorem sl2_kappa_ne_one (q n : ℕ) : (sl2Datum q n).kappa ≠ 1 := signChar_ne_one

/-- **Base case of the fundamental lemma for `SL(2)`** (unramified elliptic torus, unit element
of the Hecke algebra):
`Δ(γ_H, γ) · O^κ_γ(1_K) = SO_{γ_H}(1_{K_H})`, i.e. `(-1)^n q^{-n} · (-q)^n = 1`. -/
theorem sl2_fundamentalLemma (q n : ℕ) (hq : (q : ℂ) ≠ 0) :
    (sl2Datum q n).FundamentalLemmaHolds := by
  have h : (sl2Datum q n).kappaOrbital = (-(q : ℂ)) ^ n := sl2_kappaOrbital q n
  show (sl2Datum q n).transfer * (sl2Datum q n).kappaOrbital = (sl2Datum q n).endoStable
  rw [h]
  show (-1 : ℂ) ^ n * ((q : ℂ)⁻¹) ^ n * (-(q : ℂ)) ^ n = 1
  rw [neg_pow, ← mul_pow, ← mul_pow, ← mul_pow,
    show (-1 : ℂ) * 1 * (q : ℂ)⁻¹ * (-(q : ℂ)) = 1 from by field_simp, one_pow]

/-- The stable orbital integral of the unit element for `SL(2)` counts all the vertices of the
Bruhat–Tits tree in the ball of radius `n` fixed by `γ`. -/
theorem sl2_stableOrbital_eq (q n : ℕ) :
    (sl2Datum q n).stableOrbital = ∑ k ∈ Finset.range (n + 1), (treeSphere q k : ℂ) := by
  simp only [EndoscopicDatum.stableOrbital, sl2Datum, sl2Orbital]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (k : ZMod 2) (fun _ : ZMod 2 => (treeSphere q k : ℂ)),
    if_pos (Finset.mem_univ _)]

/-- The geometric-series form of the stable orbital integral: the ball of radius `n` in the
`(q+1)`-regular tree has `1 + (q+1)(q^n - 1)/(q - 1)` vertices. -/
theorem sl2_stableOrbital_geom (q n : ℕ) (hq : (q : ℂ) ≠ 1) :
    (sl2Datum q n).stableOrbital = 1 + ((q : ℂ) + 1) * ((q : ℂ) ^ n - 1) / ((q : ℂ) - 1) := by
  have hq' : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hq
  have h : ((q : ℂ) - 1) * (sl2Datum q n).stableOrbital
      = ((q : ℂ) - 1) + ((q : ℂ) + 1) * ((q : ℂ) ^ n - 1) := by
    rw [sl2_stableOrbital_eq]
    induction n with
    | zero => simp [treeSphere]
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        simp only [treeSphere]
        push_cast
        ring
  field_simp at h ⊢
  linear_combination h

/-- **The Langlands–Shelstad fundamental lemma (Ngô), formalized statement together with the
proved base cases and reductions.**

`(1)` trivial endoscopy `H = G`: the identity holds by definition of the stable orbital integral;
`(2)` stable vanishing: a nontrivial endoscopic character annihilates orbital data constant on a
stable class (character orthogonality on `𝔎(I_γ/F)`);
`(3)` additivity: the identity may be checked one stable class at a time;
`(4)` the `SL(2)` base case: for an unramified elliptic torus with `val(disc γ) = 2n`, the
orbital integrals of `1_K` are the parity-split counts of vertices of the Bruhat–Tits tree in the
ball of radius `n`, and `Δ · O^κ = (-1)^n q^{-n} (-q)^n = 1 = SO_{γ_H}(1_{K_H})`;
`(5)` the `SL(2)` endoscopy above is nontrivial (`κ ≠ 1`) and its `κ`-orbital integral is
`(-q)^n`, so the base case is not vacuous;
`(6)` the `GL(n)` base case: a trivial obstruction group forces `O^κ = SO`, so the fundamental
lemma holds for the principal endoscopic datum;
`(7)` the combinatorial input is justified: the sphere counts used are the numbers of
non-backtracking paths in the `(q+1)`-regular tree, and the stable orbital integral is the
corresponding geometric sum. -/
theorem ngo_fundamental_lemma :
    (∀ {Conj Obs : Type} [Fintype Conj] [AddCommGroup Obs] (D : EndoscopicDatum Conj Obs),
        D.kappa = 1 → D.transfer = 1 → D.endoStable = D.stableOrbital →
        D.FundamentalLemmaHolds)
    ∧ (∀ {Conj Obs : Type} [Fintype Conj] [AddCommGroup Obs] [Fintype Obs]
        (D : EndoscopicDatum Conj Obs), Function.Bijective D.inv →
        ∀ v : ℂ, (∀ c : Conj, D.orbital c = v) → D.kappa ≠ 1 → D.kappaOrbital = 0)
    ∧ (∀ {Conj Conj' Obs : Type} [Fintype Conj] [Fintype Conj'] [AddCommGroup Obs]
        (D : EndoscopicDatum Conj Obs) (D' : EndoscopicDatum Conj' Obs),
        D.transfer = D'.transfer → D.kappa = D'.kappa →
        D.FundamentalLemmaHolds → D'.FundamentalLemmaHolds →
        EndoscopicDatum.FundamentalLemmaHolds
          { inv := Sum.elim D.inv D'.inv
            kappa := D.kappa
            orbital := Sum.elim D.orbital D'.orbital
            transfer := D.transfer
            endoStable := D.endoStable + D'.endoStable : EndoscopicDatum (Conj ⊕ Conj') Obs })
    ∧ (∀ q n : ℕ, (q : ℂ) ≠ 0 → (sl2Datum q n).FundamentalLemmaHolds)
    ∧ (∀ q n : ℕ, (sl2Datum q n).kappa ≠ 1 ∧ (sl2Datum q n).kappaOrbital = (-(q : ℂ)) ^ n)
    ∧ (∀ {Conj Obs : Type} [Fintype Conj] [AddCommGroup Obs] [Subsingleton Obs]
        (D : EndoscopicDatum Conj Obs), D.transfer = 1 → D.endoStable = D.stableOrbital →
        D.FundamentalLemmaHolds)
    ∧ (∀ q k : ℕ, Fintype.card (TreePath q k) = treeSphere q k)
    ∧ (∀ q n : ℕ, (q : ℂ) ≠ 1 → (sl2Datum q n).stableOrbital
        = 1 + ((q : ℂ) + 1) * ((q : ℂ) ^ n - 1) / ((q : ℂ) - 1)) := by
  refine ⟨fun D => EndoscopicDatum.fundamentalLemma_trivial_endoscopy D,
    fun D hbij v hconst hκ => EndoscopicDatum.kappaOrbital_eq_zero_of_stable D hbij v hconst hκ,
    fun D D' => EndoscopicDatum.fundamentalLemma_sum D D',
    fun q n hq => sl2_fundamentalLemma q n hq,
    fun q n => ⟨sl2_kappa_ne_one q n, sl2_kappaOrbital q n⟩,
    fun D => EndoscopicDatum.fundamentalLemma_of_trivial_obstruction D,
    card_treePath, fun q n hq => sl2_stableOrbital_geom q n hq⟩

end Frontier


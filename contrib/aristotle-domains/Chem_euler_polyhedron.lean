/-!
# Euler Polyhedron
Category: Chemistry
Target: Chem.euler_polyhedron
Statement: For a convex polyhedron (e.g. fullerene cage) V−E+F=2 (Euler's formula).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.OrbitCount
import RequestProject.SphericalMap

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/
noncomputable def numOrbits (f : Perm ι) : ℕ := Nat.card (Quotient (SameCycle.setoid f))

omit [Fintype ι] [DecidableEq ι] in
lemma quotient_eq_iff_sameCycle (f : Perm ι) (a b : ι) :
    (Quotient.mk (SameCycle.setoid f) a = Quotient.mk (SameCycle.setoid f) b) ↔
      f.SameCycle a b := Quotient.eq''

lemma card_subtype_ne_add_one {β : Type*} [Finite β] (b : β) :
    Nat.card {q : β // q ≠ b} + 1 = Nat.card β := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe b)
  rw [Finite.card_option] at h
  exact h

omit [Fintype ι] in
/-- Every `SameCycle` relation for `f * swap x y` is contained in the "merged" relation
built from `f`. -/
lemma sameCycle_mul_swap_imp {f : Perm ι} {x y a b : ι}
    (h : (f * swap x y).SameCycle a b) :
    f.SameCycle a b ∨ (f.SameCycle a x ∧ f.SameCycle y b) ∨
      (f.SameCycle a y ∧ f.SameCycle x b) := by
  set g : Perm ι := f * swap x y with hg
  set T : ι → ι → Prop := fun u v => f.SameCycle u v ∨ (f.SameCycle u x ∧ f.SameCycle y v) ∨
      (f.SameCycle u y ∧ f.SameCycle x v) with hT
  have hsymm : ∀ u v, T u v → T v u := by
    rintro u v (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
    · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
  have htrans : ∀ u v w, T u v → T v w → T u w := by
    rintro u v w (h1 | ⟨h1, h1'⟩ | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩)
    · exact Or.inl (h1.trans h2)
    · exact Or.inr (Or.inl ⟨h1.trans h2, h2'⟩)
    · exact Or.inr (Or.inr ⟨h1.trans h2, h2'⟩)
    · exact Or.inr (Or.inl ⟨h1, h1'.trans h2⟩)
    · exact Or.inl (h1.trans ((h2.symm.trans h1'.symm).trans h2'))
    · exact Or.inl (h1.trans h2')
    · exact Or.inr (Or.inr ⟨h1, h1'.trans h2⟩)
    · exact Or.inl (h1.trans h2')
    · exact Or.inl (h1.trans (h2.symm.trans (h1'.symm.trans h2')))
  have hstep : ∀ u, T u (g u) := by
    intro u
    by_cases hux : u = x
    · subst hux
      exact Or.inr (Or.inl ⟨SameCycle.refl _ _, by
        rw [hg]; simp only [Perm.mul_apply, swap_apply_left]; exact ⟨1, by simp⟩⟩)
    by_cases huy : u = y
    · subst huy
      exact Or.inr (Or.inr ⟨SameCycle.refl _ _, by
        rw [hg]; simp only [Perm.mul_apply, swap_apply_right]; exact ⟨1, by simp⟩⟩)
    · refine Or.inl ⟨1, ?_⟩
      rw [hg]
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hux huy]
  have key : ∀ i : ℤ, T a ((g ^ i) a) := by
    intro i
    induction i using Int.induction_on with
    | zero => exact Or.inl (SameCycle.refl _ _)
    | succ n ih =>
        have hgg : (g ^ ((n : ℤ) + 1)) a = g ((g ^ (n : ℤ)) a) := by
          rw [add_comm, zpow_one_add, Perm.mul_apply]
        rw [hgg]
        exact htrans _ _ _ ih (hstep _)
    | pred n ih =>
        have hgg : (g ^ (-(n : ℤ) - 1)) a = g⁻¹ ((g ^ (-(n : ℤ))) a) := by
          rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Perm.mul_apply,
            zpow_neg_one]
        rw [hgg]
        refine htrans _ _ _ ih (hsymm _ _ ?_)
        have := hstep (g⁻¹ ((g ^ (-(n : ℤ))) a))
        simpa using this
  obtain ⟨i, hi⟩ := h
  have := key i
  rw [hi] at this
  exact this

omit [Fintype ι] in
/-- Walking along the orbit: as long as the darts `f ^ j y` avoid `x` and `y`, the
permutation `f * swap x y` moves `x` exactly as `f` moves `y`. -/
lemma pow_mul_swap_apply {f : Perm ι} {x y : ι} {k : ℕ}
    (hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y) :
    ∀ j, 0 < j → j ≤ k → ((f * swap x y) ^ j) x = (f ^ j) y := by
  intro j
  induction j with
  | zero => omega
  | succ n ih =>
    intro _ hle
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [pow_one, Perm.mul_apply, swap_apply_left]
    · have h1 : ((f * swap x y) ^ n) x = (f ^ n) y := ih hn (by omega)
      obtain ⟨h2, h3⟩ := hstep n hn (by omega)
      calc ((f * swap x y) ^ (n + 1)) x = (f * swap x y) (((f * swap x y) ^ n) x) := by
            rw [pow_succ']; rfl
        _ = (f * swap x y) ((f ^ n) y) := by rw [h1]
        _ = f ((f ^ n) y) := by simp [Perm.mul_apply, swap_apply_of_ne_of_ne h2 h3]
        _ = (f ^ (n + 1)) y := by rw [pow_succ']; rfl

/-- If `x` and `y` are in different orbits of `f`, then they are in the same orbit of
`f * swap x y`: the two orbits get merged. -/
lemma sameCycle_mul_swap_self {f : Perm ι} {x y : ι} (h : ¬ f.SameCycle x y) :
    (f * swap x y).SameCycle x y := by
  classical
  have hex : ∃ n, 0 < n ∧ (f ^ n) y = y :=
    ⟨orderOf f, orderOf_pos f, by rw [pow_orderOf_eq_one]; rfl⟩
  set k := Nat.find hex with hk
  obtain ⟨hkpos, hky⟩ := Nat.find_spec hex
  have hnx : ∀ j : ℕ, (f ^ j) y ≠ x := by
    intro j hj
    exact h (SameCycle.symm ⟨(j : ℤ), by simpa using hj⟩)
  have hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y := by
    intro j hj hjk
    exact ⟨hnx j, fun hjy => absurd ⟨hj, hjy⟩ (Nat.find_min hex hjk)⟩
  exact ⟨(k : ℤ), by rw [zpow_natCast, pow_mul_swap_apply hstep k hkpos le_rfl, hky]⟩

/-- If `x` and `y` are in the same orbit of `f` and are distinct, then they are in different
orbits of `f * swap x y`: the orbit gets split. -/
lemma not_sameCycle_mul_swap {f : Perm ι} {x y : ι} (hxy : x ≠ y) (h : f.SameCycle x y) :
    ¬ (f * swap x y).SameCycle x y := by
  classical
  set g := f * swap x y with hg
  have hex : ∃ n, 0 < n ∧ (f ^ n) y = x := by
    obtain ⟨i, _, hi⟩ := (h.symm).exists_pow_eq' (f := f)
    refine ⟨i, ?_, hi⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [pow_zero, Perm.one_apply] at hi
      exact absurd hi.symm hxy
    · exact hi0
  set k := Nat.find hex with hk
  obtain ⟨hkpos, hkx⟩ := Nat.find_spec hex
  have hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y := by
    intro j hj hjk
    refine ⟨fun hjx => absurd ⟨hj, hjx⟩ (Nat.find_min hex hjk), fun hjy => ?_⟩
    have hkj : (f ^ (k - j)) y = x := by
      have hsum : k - j + j = k := by omega
      have h2 : (f ^ (k - j)) ((f ^ j) y) = x := by
        rw [← Perm.mul_apply, ← pow_add, hsum, hkx]
      rwa [hjy] at h2
    exact absurd ⟨by omega, hkj⟩ (Nat.find_min hex (by omega))
  have hgk : (g ^ k) x = x := by
    rw [hg, pow_mul_swap_apply hstep k hkpos le_rfl, hkx]
  set Q : ι → Prop := fun u => ∃ j : ℕ, j < k ∧ (g ^ j) x = u with hQ
  have hQx : Q x := ⟨0, hkpos, by simp⟩
  have hQg : ∀ u, Q u → Q (g u) := by
    rintro u ⟨j, hj, rfl⟩
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hlt | heq
    · exact ⟨j + 1, hlt, by rw [pow_succ']; rfl⟩
    · refine ⟨0, hkpos, ?_⟩
      have heq' : j + 1 = k := heq
      have h1 : (g ^ (j + 1)) x = g ((g ^ j) x) := by rw [pow_succ']; rfl
      rw [heq', hgk] at h1
      simpa using h1
  have hQginv : ∀ u, Q u → Q (g⁻¹ u) := by
    rintro u ⟨j, hj, rfl⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · refine ⟨k - 1, by omega, ?_⟩
      have h1 : g ((g ^ (k - 1)) x) = x := by
        have hk1 : k - 1 + 1 = k := by omega
        calc g ((g ^ (k - 1)) x) = (g ^ (k - 1 + 1)) x := by rw [pow_succ']; rfl
          _ = x := by rw [hk1, hgk]
      simp only [pow_zero, Perm.one_apply]
      exact eq_inv_iff_eq.mpr h1
    · refine ⟨j - 1, by omega, ?_⟩
      have h1 : g ((g ^ (j - 1)) x) = (g ^ j) x := by
        have hj1 : j - 1 + 1 = j := by omega
        calc g ((g ^ (j - 1)) x) = (g ^ (j - 1 + 1)) x := by rw [pow_succ']; rfl
          _ = (g ^ j) x := by rw [hj1]
      exact eq_inv_iff_eq.mpr h1
  have hQall : ∀ i : ℤ, Q ((g ^ i) x) := by
    intro i
    induction i using Int.induction_on with
    | zero => simpa using hQx
    | succ n ih =>
        have hgg : (g ^ ((n : ℤ) + 1)) x = g ((g ^ (n : ℤ)) x) := by
          rw [add_comm, zpow_one_add, Perm.mul_apply]
        rw [hgg]; exact hQg _ ih
    | pred n ih =>
        have hgg : (g ^ (-(n : ℤ) - 1)) x = g⁻¹ ((g ^ (-(n : ℤ))) x) := by
          rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Perm.mul_apply,
            zpow_neg_one]
        rw [hgg]; exact hQginv _ ih
  rintro ⟨i, hi⟩
  obtain ⟨j, hj, hjx⟩ := hQall i
  rw [hi] at hjx
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [pow_zero, Perm.one_apply] at hjx
    exact hxy hjx
  · rw [hg, pow_mul_swap_apply hstep j hj0 (le_of_lt hj)] at hjx
    exact (hstep j hj0 hj).2 hjx

omit [Fintype ι] in
/-- Orbits of `f` are contained in orbits of `f * swap x y` when the latter merges
the orbits of `x` and `y`. -/
lemma sameCycle_mono_of_sameCycle_mul_swap {f : Perm ι} {x y a b : ι}
    (hg : (f * swap x y).SameCycle x y) (h : f.SameCycle a b) :
    (f * swap x y).SameCycle a b := by
  set g := f * swap x y with hgdef
  have hfg : g * swap x y = f := by
    rw [hgdef, mul_assoc, swap_mul_self, mul_one]
  rw [← hfg] at h
  rcases sameCycle_mul_swap_imp h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h1
  · exact h1.trans (hg.trans h2)
  · exact h1.trans (hg.symm.trans h2)

/-- **Merging**: multiplying by a transposition joining two different orbits decreases the
number of orbits by one. -/
lemma numOrbits_mul_swap_of_not_sameCycle {f : Perm ι} {x y : ι}
    (h : ¬ f.SameCycle x y) : numOrbits (f * swap x y) + 1 = numOrbits f := by
  classical
  set g := f * swap x y with hg
  have hgxy : g.SameCycle x y := sameCycle_mul_swap_self h
  have hmono : ∀ {a b : ι}, f.SameCycle a b → g.SameCycle a b := fun hab =>
    sameCycle_mono_of_sameCycle_mul_swap hgxy hab
  have hdesc : ∀ {a b : ι}, g.SameCycle a b →
      (f.SameCycle a b ∨ (f.SameCycle a x ∧ f.SameCycle y b) ∨
        (f.SameCycle a y ∧ f.SameCycle x b)) := fun hab => sameCycle_mul_swap_imp hab
  -- the value attached to a `g`-class, seen as an `f`-class different from that of `y`
  have hval : ∀ a : ι, (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
      else Quotient.mk (SameCycle.setoid f) a) ≠ Quotient.mk (SameCycle.setoid f) y := by
    intro a
    split_ifs with hay
    · exact fun hcon => h ((quotient_eq_iff_sameCycle f x y).mp hcon)
    · exact fun hcon => hay ((quotient_eq_iff_sameCycle f a y).mp hcon)
  have hwd : ∀ a b : ι, g.SameCycle a b →
      (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) =
      (if f.SameCycle b y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) b) := by
    intro a b hab
    rcases hdesc hab with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hay : f.SameCycle a y
      · rw [if_pos hay, if_pos (h1.symm.trans hay)]
      · rw [if_neg hay, if_neg (fun hby => hay (h1.trans hby))]
        exact Quotient.sound h1
    · have hay : ¬ f.SameCycle a y := fun hay => h (h1.symm.trans hay)
      have hby : f.SameCycle b y := h2.symm
      rw [if_neg hay, if_pos hby]
      exact Quotient.sound h1
    · have hay : f.SameCycle a y := h1
      have hby : ¬ f.SameCycle b y := fun hby => h (h2.trans hby)
      rw [if_pos hay, if_neg hby]
      exact Quotient.sound h2
  -- the equivalence
  let toFun : Quotient (SameCycle.setoid g) →
      {q : Quotient (SameCycle.setoid f) // q ≠ Quotient.mk (SameCycle.setoid f) y} :=
    Quotient.lift (fun a => ⟨_, hval a⟩) (by
      intro a b hab
      exact Subtype.ext (hwd a b hab))
  let F : Quotient (SameCycle.setoid f) → Quotient (SameCycle.setoid g) :=
    Quotient.lift (fun a => Quotient.mk (SameCycle.setoid g) a) (by
      intro a b hab
      exact Quotient.sound (hmono hab))
  have hleft : ∀ q, F (toFun q).1 = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      show F (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) = _
      by_cases hay : f.SameCycle a y
      · rw [if_pos hay]
        exact Quotient.sound (hgxy.trans (hmono hay).symm)
      · rw [if_neg hay]
        rfl
  have hright : ∀ q : {q : Quotient (SameCycle.setoid f) //
      q ≠ Quotient.mk (SameCycle.setoid f) y}, toFun (F q.1) = q := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h a =>
      have hay : ¬ f.SameCycle a y := fun hay => hq (Quotient.sound hay)
      apply Subtype.ext
      show (if f.SameCycle a y then Quotient.mk (SameCycle.setoid f) x
        else Quotient.mk (SameCycle.setoid f) a) = _
      rw [if_neg hay]
  have hcard : Nat.card (Quotient (SameCycle.setoid g)) =
      Nat.card {q : Quotient (SameCycle.setoid f) // q ≠ Quotient.mk (SameCycle.setoid f) y} :=
    Nat.card_congr ⟨toFun, fun q => F q.1, hleft, hright⟩
  rw [numOrbits, numOrbits, hcard, card_subtype_ne_add_one]

/-- **Splitting**: multiplying by a transposition of two points of the same orbit increases
the number of orbits by one. -/
lemma numOrbits_mul_swap_of_sameCycle {f : Perm ι} {x y : ι} (hxy : x ≠ y)
    (h : f.SameCycle x y) : numOrbits (f * swap x y) = numOrbits f + 1 := by
  have hnot : ¬ (f * swap x y).SameCycle x y := not_sameCycle_mul_swap hxy h
  have hmerge := numOrbits_mul_swap_of_not_sameCycle (f := f * swap x y) hnot
  rw [mul_assoc, swap_mul_self, mul_one] at hmerge
  exact hmerge.symm

/-- Inserting a fixed point `x` into the orbit of `d` (i.e. `d ↦ x ↦ f d`) merges the
singleton orbit `{x}` with the orbit of `d`. -/
lemma numOrbits_mul_swap_of_fixed {f : Perm ι} {d x : ι} (hx : f x = x) (hdx : d ≠ x) :
    numOrbits (f * swap d x) + 1 = numOrbits f :=
  numOrbits_mul_swap_of_not_sameCycle (fun h => hdx (h.eq_of_right hx))

omit [DecidableEq ι] in
/-- The identity permutation has one orbit per point. -/
lemma numOrbits_one : numOrbits (1 : Perm ι) = Fintype.card ι := by
  classical
  have : Nat.card (Quotient (SameCycle.setoid (1 : Perm ι))) = Nat.card ι := by
    refine Nat.card_congr (Equiv.ofBijective (fun q => q.out) ?_)
    constructor
    · intro q q' hqq'
      have := congrArg (Quotient.mk (SameCycle.setoid (1 : Perm ι))) hqq'
      simpa using this
    · intro a
      refine ⟨Quotient.mk (SameCycle.setoid (1 : Perm ι)) a, ?_⟩
      have : (Quotient.mk (SameCycle.setoid (1 : Perm ι))
          (Quotient.mk (SameCycle.setoid (1 : Perm ι)) a).out) =
          Quotient.mk (SameCycle.setoid (1 : Perm ι)) a := Quotient.out_eq _
      rw [quotient_eq_iff_sameCycle] at this
      obtain ⟨i, hi⟩ := this
      simpa using hi
  rw [numOrbits, this, Nat.card_eq_fintype_card]

end Polyhedron


/-!
# Combinatorial maps on the sphere and Euler's polyhedron formula

A *combinatorial map* (rotation system) on a finite set `D` of *darts* consists of two
permutations:

* `s` (the *vertex permutation*): its orbits on `D` are the vertices, `s` rotating the darts
  around a vertex in the cyclic order given by the embedding;
* `a` (the *edge permutation*): a fixed-point-free involution on `D`, whose orbits (pairs of
  darts) are the edges.

The *faces* are then the orbits of `a * s`.  This is the standard encoding of a graph embedded
in an oriented surface; the surface is a sphere exactly when the map can be built up, starting
from a single edge, by repeatedly

* attaching a new pendant edge at a corner of the map (`pendant`), or
* drawing a new edge between two distinct corners lying on a common face (`chord`),

which is the content of the inductive predicate `IsSphericalMap` below.  The boundary complex of
a convex polyhedron (for instance a fullerene cage) yields such a map, its darts being the
(edge, endpoint) incidences.

The main theorem `Chem.euler_polyhedron` states Euler's formula `V - E + F = 2` for these maps.
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `IsSphericalMap D s a` says that the pair of permutations `(s, a)`, supported on the finite
set of darts `D`, is a combinatorial map of the sphere: it can be obtained from a single edge by
repeatedly attaching a pendant edge at a corner, or joining two distinct corners of a common
face by a new edge.  Here `s` encodes the cyclic order of the darts around each vertex and `a`
is the fixed-point-free involution pairing the two darts of each edge. -/
inductive IsSphericalMap : Finset ι → Perm ι → Perm ι → Prop
  /-- The map consisting of a single edge: two vertices, one edge and one face. -/
  | base {d₀ d₁ : ι} (h : d₀ ≠ d₁) : IsSphericalMap {d₀, d₁} 1 (swap d₀ d₁)
  /-- Attach a new edge with a new endpoint (a new vertex `y`) at the corner `d`. -/
  | pendant {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) {d x y : ι}
      (hd : d ∈ D) (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
      IsSphericalMap (insert x (insert y D)) (s * swap d x) (a * swap x y)
  /-- Join the two distinct corners `d` and `e` of a common face by a new edge. -/
  | chord {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) {d e x y : ι}
      (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) (hface : (a * s).SameCycle d e)
      (hx : x ∉ D) (hy : y ∉ D) (hxy : x ≠ y) :
      IsSphericalMap (insert x (insert y D)) (s * swap d x * swap e y) (a * swap x y)

/-! ### Two permutation identities describing the effect of the moves on the faces -/

omit [Fintype ι] in
/-- Attaching a pendant edge inserts the two new darts into one face, leaving the number of
faces unchanged. -/
lemma face_pendant_eq (s a : Perm ι) {d x y : ι} (hdx : d ≠ x) (hdy : d ≠ y) (hxy : x ≠ y)
    (hsx : s x = x) (hsy : s y = y) (hay : a y = y) :
    (a * swap x y) * (s * swap d x) = (a * s) * swap d y * swap y x := by
  have hsne : ∀ z : ι, z ≠ x → s z ≠ x := fun z hz h => hz (s.injective (h.trans hsx.symm))
  have hsne' : ∀ z : ι, z ≠ y → s z ≠ y := fun z hz h => hz (s.injective (h.trans hsy.symm))
  have hsdx : s d ≠ x := hsne d hdx
  have hsdy : s d ≠ y := hsne' d hdy
  ext z
  by_cases hzd : z = d
  · rw [hzd]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hdy hdx, swap_apply_left, hsx, hsy, hay]
  by_cases hzx : z = x
  · rw [hzx]
    simp only [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hsdx hsdy]
  by_cases hzy : z = y
  · rw [hzy]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy),
      swap_apply_left, swap_apply_right, hsy, hsx,
      swap_apply_of_ne_of_ne (Ne.symm hdx) hxy]
  · simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hzd hzx, swap_apply_of_ne_of_ne hzy hzx,
      swap_apply_of_ne_of_ne hzd hzy, swap_apply_of_ne_of_ne (hsne z hzx) (hsne' z hzy)]

omit [Fintype ι] in
/-- Drawing a chord inserts the two new darts into one face and then splits it with the
transposition `swap x y`. -/
lemma face_chord_eq (s a : Perm ι) {d e x y : ι} (hde : d ≠ e) (hdx : d ≠ x) (hdy : d ≠ y)
    (hex : e ≠ x) (hey : e ≠ y) (hxy : x ≠ y)
    (hsx : s x = x) (hsy : s y = y) (hax : a x = x) (hay : a y = y) :
    (a * swap x y) * (s * swap d x * swap e y) = ((a * s) * swap d y * swap e x) * swap x y := by
  have hsne : ∀ z : ι, z ≠ x → s z ≠ x := fun z hz h => hz (s.injective (h.trans hsx.symm))
  have hsne' : ∀ z : ι, z ≠ y → s z ≠ y := fun z hz h => hz (s.injective (h.trans hsy.symm))
  ext z
  by_cases hzd : z = d
  · rw [hzd]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hde hdy, swap_apply_of_ne_of_ne hdx hdy,
      swap_apply_of_ne_of_ne hde hdx, swap_apply_left, hsx, hsy, hay]
  by_cases hze : z = e
  · rw [hze]
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy),
      swap_apply_of_ne_of_ne hex hey, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hsy, hsx, hax]
  by_cases hzx : z = x
  · rw [hzx]
    simp only [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hex) hxy,
      swap_apply_right, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hey) (Ne.symm hxy),
      swap_apply_of_ne_of_ne (hsne d hdx) (hsne' d hdy)]
  by_cases hzy : z = y
  · rw [hzy]
    simp only [Perm.mul_apply, swap_apply_right,
      swap_apply_of_ne_of_ne (Ne.symm hde) hex, swap_apply_of_ne_of_ne (Ne.symm hde) hey,
      swap_apply_of_ne_of_ne (hsne e hex) (hsne' e hey)]
  · simp only [Perm.mul_apply, swap_apply_of_ne_of_ne hze hzy, swap_apply_of_ne_of_ne hzd hzx,
      swap_apply_of_ne_of_ne hzx hzy, swap_apply_of_ne_of_ne hze hzx,
      swap_apply_of_ne_of_ne hzd hzy, swap_apply_of_ne_of_ne (hsne z hzx) (hsne' z hzy)]

/-! ### Basic structural facts about spherical maps -/

omit [Fintype ι] in
/-- The permutations of a map fix every non-dart. -/
lemma IsSphericalMap.fixes_of_notMem {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) :
    ∀ z ∉ D, s z = z ∧ a z = z := by
  induction H with
  | @base d₀ d₁ h =>
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      exact ⟨rfl, swap_apply_of_ne_of_ne hz.1 hz.2⟩
  | @pendant D s a H d x y hd hx hy hxy ih =>
      intro z hz
      simp only [Finset.mem_insert, not_or] at hz
      obtain ⟨hzx, hzy, hzD⟩ := hz
      have hzd : z ≠ d := fun h => hzD (h ▸ hd)
      exact ⟨by simp [Perm.mul_apply, swap_apply_of_ne_of_ne hzd hzx, (ih z hzD).1],
        by simp [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy, (ih z hzD).2]⟩
  | @chord D s a H d e x y hd he hde hface hx hy hxy ih =>
      intro z hz
      simp only [Finset.mem_insert, not_or] at hz
      obtain ⟨hzx, hzy, hzD⟩ := hz
      have hzd : z ≠ d := fun h => hzD (h ▸ hd)
      have hze : z ≠ e := fun h => hzD (h ▸ he)
      refine ⟨?_, by simp [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy, (ih z hzD).2]⟩
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne hze hzy, swap_apply_of_ne_of_ne hzd hzx,
        (ih z hzD).1]

omit [Fintype ι] in
lemma IsSphericalMap.vertex_fix {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a)
    {z : ι} (hz : z ∉ D) : s z = z := (H.fixes_of_notMem z hz).1

omit [Fintype ι] in
lemma IsSphericalMap.edge_fix {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a)
    {z : ι} (hz : z ∉ D) : a z = z := (H.fixes_of_notMem z hz).2

omit [Fintype ι] in
lemma IsSphericalMap.face_fix {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a)
    {z : ι} (hz : z ∉ D) : (a * s) z = z := by
  simp [Perm.mul_apply, H.vertex_fix hz, H.edge_fix hz]

omit [Fintype ι] in
/-- The edge permutation of a map is an involution which is fixed-point-free on the darts:
the darts come in pairs, one pair per edge. -/
lemma IsSphericalMap.edge_involutive {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) :
    a * a = 1 ∧ ∀ d ∈ D, a d ≠ d := by
  induction H with
  | @base d₀ d₁ h =>
      refine ⟨swap_mul_self d₀ d₁, ?_⟩
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · simpa [swap_apply_left] using h.symm
      · simpa [swap_apply_right] using h
  | @pendant D s a H d x y hd hx hy hxy ih =>
      obtain ⟨hinv, hfree⟩ := ih
      have hax : a x = x := H.edge_fix hx
      have hay : a y = y := H.edge_fix hy
      have hcomm : swap x y * a = a * swap x y := by
        have hc : a * swap x y * a⁻¹ = swap (a x) (a y) := (Equiv.swap_apply_apply a x y).symm
        rw [hax, hay] at hc
        calc swap x y * a = (a * swap x y * a⁻¹) * a := by rw [hc]
          _ = a * swap x y := by group
      refine ⟨?_, ?_⟩
      · calc (a * swap x y) * (a * swap x y) = a * (swap x y * a) * swap x y := by group
          _ = (a * a) * (swap x y * swap x y) := by rw [hcomm]; group
          _ = 1 := by rw [hinv, swap_mul_self, mul_one]
      · intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzD
        · simpa [Perm.mul_apply, swap_apply_left, hay] using Ne.symm hxy
        · simpa [Perm.mul_apply, swap_apply_right, hax] using hxy
        · have hzx : z ≠ x := fun h => hx (h ▸ hzD)
          have hzy : z ≠ y := fun h => hy (h ▸ hzD)
          simpa [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy] using hfree z hzD
  | @chord D s a H d e x y hd he hde hface hx hy hxy ih =>
      obtain ⟨hinv, hfree⟩ := ih
      have hax : a x = x := H.edge_fix hx
      have hay : a y = y := H.edge_fix hy
      have hcomm : swap x y * a = a * swap x y := by
        have hc : a * swap x y * a⁻¹ = swap (a x) (a y) := (Equiv.swap_apply_apply a x y).symm
        rw [hax, hay] at hc
        calc swap x y * a = (a * swap x y * a⁻¹) * a := by rw [hc]
          _ = a * swap x y := by group
      refine ⟨?_, ?_⟩
      · calc (a * swap x y) * (a * swap x y) = a * (swap x y * a) * swap x y := by group
          _ = (a * a) * (swap x y * swap x y) := by rw [hcomm]; group
          _ = 1 := by rw [hinv, swap_mul_self, mul_one]
      · intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | rfl | hzD
        · simpa [Perm.mul_apply, swap_apply_left, hay] using Ne.symm hxy
        · simpa [Perm.mul_apply, swap_apply_right, hax] using hxy
        · have hzx : z ≠ x := fun h => hx (h ▸ hzD)
          have hzy : z ≠ y := fun h => hy (h ▸ hzD)
          simpa [Perm.mul_apply, swap_apply_of_ne_of_ne hzx hzy] using hfree z hzD

/-- The number of darts is twice the number of edges (each edge consists of two darts). -/
lemma IsSphericalMap.card_darts {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) :
    2 * numOrbits a + D.card = 2 * Fintype.card ι := by
  induction H with
  | @base d₀ d₁ h =>
      have h1 : numOrbits ((1 : Perm ι) * swap d₀ d₁) + 1 = numOrbits (1 : Perm ι) :=
        numOrbits_mul_swap_of_fixed rfl h
      rw [one_mul, numOrbits_one] at h1
      rw [Finset.card_pair h]
      omega
  | @pendant D s a H d x y hd hx hy hxy ih =>
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed (H.edge_fix hy) hxy
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      omega
  | @chord D s a H d e x y hd he hde hface hx hy hxy ih =>
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed (H.edge_fix hy) hxy
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      omega

/-- Euler's formula in the general form, where the ambient type `ι` may contain non-darts
(each of which contributes a spurious singleton orbit to each of the three counts). -/
theorem IsSphericalMap.euler {D : Finset ι} {s a : Perm ι} (H : IsSphericalMap D s a) :
    numOrbits s + numOrbits (a * s) + D.card = numOrbits a + Fintype.card ι + 2 := by
  induction H with
  | @base d₀ d₁ h =>
      have h1 : numOrbits ((1 : Perm ι) * swap d₀ d₁) + 1 = numOrbits (1 : Perm ι) :=
        numOrbits_mul_swap_of_fixed rfl h
      rw [one_mul, numOrbits_one] at h1
      rw [mul_one, numOrbits_one, Finset.card_pair h]
      omega
  | @pendant D s a H d x y hd hx hy hxy ih =>
      have hsx : s x = x := H.vertex_fix hx
      have hsy : s y = y := H.vertex_fix hy
      have hay : a y = y := H.edge_fix hy
      have hdx : d ≠ x := fun h => hx (h ▸ hd)
      have hdy : d ≠ y := fun h => hy (h ▸ hd)
      have hfy : (a * s) y = y := H.face_fix hy
      have hfx : (a * s) x = x := H.face_fix hx
      have hV : numOrbits (s * swap d x) + 1 = numOrbits s :=
        numOrbits_mul_swap_of_fixed hsx hdx
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed hay hxy
      have hF1 : numOrbits ((a * s) * swap d y) + 1 = numOrbits (a * s) :=
        numOrbits_mul_swap_of_fixed hfy hdy
      have hg1x : ((a * s) * swap d y) x = x := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hfx]
      have hF2 : numOrbits (((a * s) * swap d y) * swap y x) + 1 =
          numOrbits ((a * s) * swap d y) :=
        numOrbits_mul_swap_of_fixed hg1x (Ne.symm hxy)
      have hid : (a * swap x y) * (s * swap d x) = ((a * s) * swap d y) * swap y x :=
        face_pendant_eq s a hdx hdy hxy hsx hsy hay
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      rw [hid, hcard]
      omega
  | @chord D s a H d e x y hd he hde hface hx hy hxy ih =>
      have hsx : s x = x := H.vertex_fix hx
      have hsy : s y = y := H.vertex_fix hy
      have hax : a x = x := H.edge_fix hx
      have hay : a y = y := H.edge_fix hy
      have hdx : d ≠ x := fun h => hx (h ▸ hd)
      have hdy : d ≠ y := fun h => hy (h ▸ hd)
      have hex : e ≠ x := fun h => hx (h ▸ he)
      have hey : e ≠ y := fun h => hy (h ▸ he)
      have hfy : (a * s) y = y := H.face_fix hy
      have hfx : (a * s) x = x := H.face_fix hx
      have hV1 : numOrbits (s * swap d x) + 1 = numOrbits s :=
        numOrbits_mul_swap_of_fixed hsx hdx
      have hsdxy : (s * swap d x) y = y := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdy) (Ne.symm hxy), hsy]
      have hV2 : numOrbits ((s * swap d x) * swap e y) + 1 = numOrbits (s * swap d x) :=
        numOrbits_mul_swap_of_fixed hsdxy hey
      have hE : numOrbits (a * swap x y) + 1 = numOrbits a :=
        numOrbits_mul_swap_of_fixed hay hxy
      have hF1 : numOrbits ((a * s) * swap d y) + 1 = numOrbits (a * s) :=
        numOrbits_mul_swap_of_fixed hfy hdy
      have hg1x : ((a * s) * swap d y) x = x := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hdx) hxy, hfx]
      have hF2 : numOrbits (((a * s) * swap d y) * swap e x) + 1 =
          numOrbits ((a * s) * swap d y) :=
        numOrbits_mul_swap_of_fixed hg1x hex
      -- the new edge splits the face containing both `d` and `e`
      have hnot1 : ¬ (a * s).SameCycle d y := fun hc => hdy (hc.eq_of_right hfy)
      have hm1 : ((a * s) * swap d y).SameCycle d y := sameCycle_mul_swap_self hnot1
      have hg1de : ((a * s) * swap d y).SameCycle d e :=
        sameCycle_mono_of_sameCycle_mul_swap hm1 hface
      have hnot2 : ¬ ((a * s) * swap d y).SameCycle e x := fun hc => hex (hc.eq_of_right hg1x)
      have hm2 : (((a * s) * swap d y) * swap e x).SameCycle e x :=
        sameCycle_mul_swap_self hnot2
      have hgde : (((a * s) * swap d y) * swap e x).SameCycle d e :=
        sameCycle_mono_of_sameCycle_mul_swap hm2 hg1de
      have hgd : (((a * s) * swap d y) * swap e x) d = y := by
        simp [Perm.mul_apply, swap_apply_of_ne_of_ne hde hdx, swap_apply_left, hsy, hay]
      have hgdy : (((a * s) * swap d y) * swap e x).SameCycle d y := ⟨1, by simpa using hgd⟩
      have hgxy : (((a * s) * swap d y) * swap e x).SameCycle x y :=
        hm2.symm.trans (hgde.symm.trans hgdy)
      have hF3 : numOrbits ((((a * s) * swap d y) * swap e x) * swap x y) =
          numOrbits (((a * s) * swap d y) * swap e x) + 1 :=
        numOrbits_mul_swap_of_sameCycle hxy hgxy
      have hid : (a * swap x y) * (s * swap d x * swap e y) =
          (((a * s) * swap d y) * swap e x) * swap x y :=
        face_chord_eq s a hde hdx hdy hex hey hxy hsx hsy hax hay
      have hcard : (insert x (insert y D)).card = D.card + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hxy, hx]),
          Finset.card_insert_of_notMem hy]
      rw [hid, hcard]
      omega

end Polyhedron

namespace Chem

open Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of vertices of a combinatorial map: the number of orbits of the vertex
permutation. -/
noncomputable def numVertices (s : Perm ι) : ℕ := numOrbits s

/-- The number of edges of a combinatorial map: the number of orbits of the edge involution. -/
noncomputable def numEdges (a : Perm ι) : ℕ := numOrbits a

/-- The number of faces of a combinatorial map: the number of orbits of `a * s`. -/
noncomputable def numFaces (s a : Perm ι) : ℕ := numOrbits (a * s)

/-- **Euler's polyhedron formula**.  For a convex polyhedron -- for instance a fullerene cage --
the boundary complex is a combinatorial map of the sphere, and for any such map
`V - E + F = 2`. -/
theorem euler_polyhedron {s a : Perm ι} (H : IsSphericalMap (Finset.univ : Finset ι) s a) :
    (numVertices s : ℤ) - numEdges a + numFaces s a = 2 := by
  have h := H.euler
  rw [Finset.card_univ] at h
  simp only [numVertices, numEdges, numFaces]
  omega

/-- For a spherical map on all of `ι`, the number of darts is twice the number of edges. -/
theorem card_darts_eq_two_mul_numEdges {s a : Perm ι}
    (H : IsSphericalMap (Finset.univ : Finset ι) s a) :
    Fintype.card ι = 2 * numEdges a := by
  have h := H.card_darts
  rw [Finset.card_univ] at h
  simp only [numEdges]
  omega

/-- Euler's formula in natural-number form: `V + F = E + 2`. -/
theorem euler_polyhedron_nat {s a : Perm ι} (H : IsSphericalMap (Finset.univ : Finset ι) s a) :
    numVertices s + numFaces s a = numEdges a + 2 := by
  have h := H.euler
  rw [Finset.card_univ] at h
  simp only [numVertices, numEdges, numFaces]
  omega

/-- **Twelve pentagons**: a fullerene cage is a spherical map in which every vertex has degree
three and every face is a pentagon or a hexagon; Euler's formula forces the number of pentagons
to be exactly `12`. -/
theorem fullerene_twelve_pentagons {V E F P H : ℕ} (hdeg : 3 * V = 2 * E)
    (hfaces : F = P + H) (hedges : 2 * E = 5 * P + 6 * H) (heuler : V + F = E + 2) :
    P = 12 := by
  omega

/-- **Twelve pentagons, for an actual spherical map**: if every vertex of a spherical map has
degree three (`3 V = 2 E`) and every face is a pentagon or a hexagon, then there are exactly
twelve pentagons -- the combinatorial reason why every fullerene cage has twelve five-membered
rings. -/
theorem fullerene_twelve_pentagons_of_map {s a : Perm ι} {P Hex : ℕ}
    (H : IsSphericalMap (Finset.univ : Finset ι) s a)
    (hdeg : 3 * numVertices s = 2 * numEdges a)
    (hfaces : numFaces s a = P + Hex)
    (hedges : 2 * numEdges a = 5 * P + 6 * Hex) : P = 12 :=
  fullerene_twelve_pentagons hdeg hfaces hedges (euler_polyhedron_nat H)

end Chem


/-!
# A concrete spherical map

To show that the notion `Polyhedron.IsSphericalMap` is not vacuous we build an explicit
example: a triangle drawn on the sphere, with `3` vertices, `3` edges and `2` faces
(the inside and the outside of the triangle), realised on the six darts `Fin 6`.
-/

open Equiv Equiv.Perm Polyhedron

namespace Chem

/-- A triangle drawn on the sphere, on the six darts `Fin 6`: three vertices, three edges and
two faces.  In particular `Chem.euler_polyhedron` applies to a genuine map. -/
theorem exists_sphericalMap_triangle :
    ∃ s a : Perm (Fin 6), IsSphericalMap Finset.univ s a := by
  refine ⟨(1 * swap 1 2) * swap 0 4 * swap 3 5, (swap 0 1 * swap 2 3) * swap 4 5, ?_⟩
  have hbase : IsSphericalMap ({0, 1} : Finset (Fin 6)) 1 (swap 0 1) :=
    IsSphericalMap.base (by decide)
  have hpath : IsSphericalMap (insert 2 (insert 3 ({0, 1} : Finset (Fin 6))))
      (1 * swap 1 2) (swap 0 1 * swap 2 3) :=
    hbase.pendant (d := 1) (x := 2) (y := 3) (by decide) (by decide) (by decide) (by decide)
  have htri := hpath.chord (d := 0) (e := 3) (x := 4) (y := 5) (by decide) (by decide)
    (by decide) ⟨2, by decide⟩ (by decide) (by decide) (by decide)
  have hset : insert (4 : Fin 6) (insert 5 (insert 2 (insert 3 ({0, 1} : Finset (Fin 6)))))
      = Finset.univ := by decide
  rwa [hset] at htri

/-- Euler's formula for the triangle map. -/
theorem euler_triangle :
    ∃ s a : Perm (Fin 6), IsSphericalMap Finset.univ s a ∧
      (numVertices s : ℤ) - numEdges a + numFaces s a = 2 := by
  obtain ⟨s, a, H⟩ := exists_sphericalMap_triangle
  exact ⟨s, a, H, euler_polyhedron H⟩

end Chem


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


/-
Absorbing the countable set of poles: the unit sphere is `SO(3)`-paradoxical.
-/
import RequestProject.Sphere

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### Countability of the solution sets of rotation equations -/

/-- For a point `d` off the `z`-axis, only countably many angles `t` satisfy
`rZ (c * t) • d = d'`. -/
theorem countable_rZ_sol {c : ℝ} (hc : c ≠ 0) {d d' : E} (hd : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    {t : ℝ | rZ (c * t) • d = d'}.Countable := by
  rcases Set.eq_empty_or_nonempty {t : ℝ | rZ (c * t) • d = d'} with h | ⟨t₀, ht₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_
      (Set.countable_range (fun k : ℤ => t₀ + (k : ℝ) * (2 * Real.pi) / c))
    intro t ht
    have heq : rZ (c * t) • d = rZ (c * t₀) • d := by
      rw [show rZ (c * t) • d = d' from ht, show rZ (c * t₀) • d = d' from ht₀]
    have hfix : rZ (c * (t - t₀)) • d = d := by
      have hsplit : rZ (c * (t - t₀)) = (rZ (c * t₀))⁻¹ * rZ (c * t) := by
        rw [rZ_inv, ← rZ_add]; congr 1; ring
      rw [hsplit, SemigroupAction.mul_smul, heq, inv_smul_smul]
    obtain ⟨hcos, -⟩ := rZ_fix _ d hd hfix
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    refine ⟨k, ?_⟩
    show t₀ + (k : ℝ) * (2 * Real.pi) / c = t
    field_simp
    linear_combination hk

/-- For a point `v` off the `y`-axis, only countably many angles `s` satisfy
`rY s • v = d`. -/
theorem countable_rY_sol {d v : E} (hv : v 0 ≠ 0 ∨ v 2 ≠ 0) :
    {s : ℝ | rY s • v = d}.Countable := by
  rcases Set.eq_empty_or_nonempty {s : ℝ | rY s • v = d} with h | ⟨s₀, hs₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono ?_
      (Set.countable_range (fun k : ℤ => s₀ + (k : ℝ) * (2 * Real.pi)))
    intro s hs
    have heq : rY s • v = rY s₀ • v := by
      rw [show rY s • v = d from hs, show rY s₀ • v = d from hs₀]
    have hfix : rY (s - s₀) • v = v := by
      have hsplit : rY (s - s₀) = (rY s₀)⁻¹ * rY s := by
        rw [rY_inv, ← rY_add]; congr 1; ring
      rw [hsplit, SemigroupAction.mul_smul, heq, inv_smul_smul]
    obtain ⟨hcos, -⟩ := rY_fix _ v hv hfix
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    exact ⟨k, by show s₀ + (k : ℝ) * (2 * Real.pi) = s; linarith⟩

/-- The reals are uncountable, so a countable set of reals has a complement point. -/
theorem exists_not_mem_of_countable {S : Set ℝ} (hS : S.Countable) : ∃ t : ℝ, t ∉ S := by
  by_contra hcon
  push_neg at hcon
  exact Cardinal.not_countable_real (Set.Countable.mono (fun x _ => hcon x) hS)

/-! ### Finding an absorbing rotation -/

/-- There is an angle whose rotation about the `z`-axis moves a countable set off itself,
provided the set avoids the poles. -/
theorem exists_angle {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable)
    (hp : EuclideanSpace.single 2 (1 : ℝ) ∉ D) (hp' : -EuclideanSpace.single 2 (1 : ℝ) ∉ D) :
    ∃ t : ℝ, ∀ n : ℕ, 1 ≤ n → Disjoint ((rZ t ^ n) • D) D := by
  have hoff : ∀ d ∈ D, d 0 ≠ 0 ∨ d 1 ≠ 0 := fun d hd =>
    off_axis_of_mem_sph (hD hd) (fun h => hp (h ▸ hd)) (fun h => hp' (h ▸ hd))
  obtain ⟨t, ht⟩ := exists_not_mem_of_countable
    (S := ⋃ (n : ℕ), ⋃ (d ∈ D), ⋃ (d' ∈ D), {t : ℝ | rZ (((n : ℝ) + 1) * t) • d = d'})
    (Set.countable_iUnion fun n =>
      hcount.biUnion fun d hd => hcount.biUnion fun d' _ =>
        countable_rZ_sol (by positivity) (hoff d hd))
  refine ⟨t, fun n hn => ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨d, hd, rfl⟩ hmem
  apply ht
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine Set.mem_iUnion.2 ⟨m, Set.mem_iUnion₂.2 ⟨d, hd, Set.mem_iUnion₂.2
    ⟨(rZ t ^ (m + 1)) • d, hmem, ?_⟩⟩⟩
  show rZ (((m : ℝ) + 1) * t) • d = (rZ t ^ (m + 1)) • d
  rw [rZ_pow]
  norm_num

/-- There is a rotation taking the poles off a given countable subset of the sphere. -/
theorem exists_axis {D : Set E} (hcount : D.Countable) :
    ∃ Q : SO3, EuclideanSpace.single 2 (1 : ℝ) ∉ Q⁻¹ • D ∧
      -EuclideanSpace.single 2 (1 : ℝ) ∉ Q⁻¹ • D := by
  set p : E := EuclideanSpace.single 2 (1 : ℝ) with hpdef
  have hoffp : p 0 ≠ 0 ∨ p 2 ≠ 0 := Or.inr (by simp [hpdef, EuclideanSpace.single_apply])
  have hoffnp : (-p) 0 ≠ 0 ∨ (-p) 2 ≠ 0 := Or.inr (by simp [hpdef, EuclideanSpace.single_apply])
  obtain ⟨psi, hpsi⟩ := exists_not_mem_of_countable
    (S := ⋃ (d ∈ D), ({s : ℝ | rY s • p = d} ∪ {s : ℝ | rY s • (-p) = d}))
    (hcount.biUnion fun _ _ => (countable_rY_sol hoffp).union (countable_rY_sol hoffnp))
  refine ⟨rY psi, ?_, ?_⟩
  · rintro ⟨d, hd, hdq⟩
    replace hdq : (rY psi)⁻¹ • d = p := hdq
    exact hpsi (Set.mem_iUnion₂.2 ⟨d, hd, Or.inl (by
      show rY psi • p = d
      rw [← hdq, smul_inv_smul])⟩)
  · rintro ⟨d, hd, hdq⟩
    replace hdq : (rY psi)⁻¹ • d = -p := hdq
    exact hpsi (Set.mem_iUnion₂.2 ⟨d, hd, Or.inr (by
      show rY psi • (-p) = d
      rw [← hdq, smul_inv_smul])⟩)

theorem exists_absorbing_rotation {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable) :
    ∃ rho : SO3, ∀ n : ℕ, 1 ≤ n → Disjoint ((rho ^ n) • D) D := by
  obtain ⟨Q, hQ1, hQ2⟩ := exists_axis hcount
  have hD'sub : (Q⁻¹ • D : Set E) ⊆ sph := by
    rintro _ ⟨d, hd, rfl⟩; exact smul_mem_sph _ (hD hd)
  have hD'c : (Q⁻¹ • D : Set E).Countable := hcount.image _
  obtain ⟨t, ht⟩ := exists_angle hD'sub hD'c hQ1 hQ2
  have hpow : ∀ n : ℕ, (Q * rZ t * Q⁻¹) ^ n = Q * (rZ t ^ n) * Q⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih, pow_succ]; group
  refine ⟨Q * rZ t * Q⁻¹, fun n hn => ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨d, hd, rfl⟩ hmem
  have h1 : Q⁻¹ • ((Q * rZ t * Q⁻¹) ^ n • d) = (rZ t ^ n) • (Q⁻¹ • d) := by
    rw [hpow, ← SemigroupAction.mul_smul, ← SemigroupAction.mul_smul]
    congr 1
    group
  have hin1 : Q⁻¹ • ((Q * rZ t * Q⁻¹) ^ n • d) ∈ (Q⁻¹ • D : Set E) := ⟨_, hmem, rfl⟩
  have hin2 : (rZ t ^ n) • (Q⁻¹ • d) ∈ (rZ t ^ n) • (Q⁻¹ • D : Set E) :=
    ⟨Q⁻¹ • d, ⟨d, hd, rfl⟩, rfl⟩
  rw [h1] at hin1
  exact ((ht n hn).le_bot ⟨hin2, hin1⟩ : _ ∈ (⊥ : Set E))

theorem equidec_sph_diff {D : Set E} (hD : D ⊆ sph) (hcount : D.Countable) :
    Equidec SO3 sph (sph \ D) := by
  obtain ⟨rho, hrho⟩ := exists_absorbing_rotation hD hcount
  refine Equidec.absorb rho (fun n => ?_) hrho
  rintro _ ⟨d, hd, rfl⟩
  exact smul_mem_sph _ (hD hd)

/-- **The Hausdorff paradox**: the unit sphere is `SO(3)`-paradoxical. -/
theorem isParadoxical_sph : IsParadoxical SO3 sph :=
  IsParadoxical.of_equidec (Equidec.symm (equidec_sph_diff badSet_subset badSet_countable))
    isParadoxical_sph_diff_bad

end

end BT

/-
Paradoxical decompositions coming from free actions of the free group of rank two.
-/
import RequestProject.Equidec

open Set Function Pointwise

namespace BT

/-- The free group of rank two. -/
abbrev F2 := FreeGroup (Fin 2)

namespace FreeWord

variable {α : Type*} [DecidableEq α]

theorem toWord_cons {x : α × Bool} {w : FreeGroup α} (h : w.toWord.head? ≠ some (x.1, !x.2)) :
    (FreeGroup.mk [x] * w).toWord = x :: w.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons hd tl =>
      rw [hw] at h
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have hne : ¬ (x.1 = hd.1 ∧ x.2 = !hd.2) := by
        rintro ⟨h1, h2⟩
        exact h (by rw [h1, h2]; simp)
      simp [hne]

theorem toWord_cancel {x : α × Bool} {w : FreeGroup α} {L : List (α × Bool)}
    (h : w.toWord = (x.1, !x.2) :: L) :
    (FreeGroup.mk [x] * w).toWord = L := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord, h]
  simp

end FreeWord

/-- The set of elements of `F2` whose reduced word starts with the letter `x`. -/
def startsWith (x : Fin 2 × Bool) : Set F2 := {w : F2 | w.toWord.head? = some x}

theorem startsWith_disjoint {x y : Fin 2 × Bool} (h : x ≠ y) :
    Disjoint (startsWith x) (startsWith y) := by
  rw [Set.disjoint_left]
  intro w hx hy
  exact h (by rw [← Option.some_inj, ← hx, ← hy])

theorem of_eq_mk (i : Fin 2) : (FreeGroup.of i : F2) = FreeGroup.mk [(i, true)] := rfl

theorem inv_of_eq_mk (i : Fin 2) : (FreeGroup.of i : F2)⁻¹ = FreeGroup.mk [(i, false)] := by
  rw [of_eq_mk, FreeGroup.inv_mk]
  rfl

/-- Every element of `F2` either starts with the letter `i`, or is `i` times an element
starting with `i⁻¹`. -/
theorem startsWith_cover (i : Fin 2) :
    startsWith (i, true) ∪ (FreeGroup.of i : F2) • startsWith (i, false) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : w.toWord.head? = some (i, true)
  · exact Or.inl h
  · refine Or.inr ⟨(FreeGroup.of i : F2)⁻¹ * w, ?_, by simp⟩
    show ((FreeGroup.of i : F2)⁻¹ * w).toWord.head? = some (i, false)
    rw [inv_of_eq_mk]
    rw [FreeWord.toWord_cons (x := (i, false)) (by simpa using h)]
    simp

theorem startsWith_cover_disjoint (i : Fin 2) :
    Disjoint (startsWith (i, true)) ((FreeGroup.of i : F2) • startsWith (i, false)) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨u, hu, rfl⟩
  -- `u` starts with `i⁻¹`, so `i * u` is `u` with its first letter removed
  have hu' : u.toWord.head? = some (i, false) := hu
  obtain ⟨L, hL⟩ : ∃ L, u.toWord = (i, false) :: L := by
    cases hc : u.toWord with
    | nil => rw [hc] at hu'; simp at hu'
    | cons hd tl =>
        rw [hc] at hu'
        simp only [List.head?_cons, Option.some.injEq] at hu'
        exact ⟨tl, by rw [hu']⟩
  have hred : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  rw [hL] at hred
  have hcancel : ((FreeGroup.of i : F2) * u).toWord = L := by
    rw [of_eq_mk]
    exact FreeWord.toWord_cancel (x := (i, true)) (by simpa using hL)
  have hhead : L.head? = some (i, true) := by
    have h2 : ((FreeGroup.of i : F2) * u).toWord.head? = some (i, true) := hw
    rwa [hcancel] at h2
  cases hLc : L with
  | nil => rw [hLc] at hhead; simp at hhead
  | cons hd tl =>
      rw [hLc] at hhead hred
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [FreeGroup.isReduced_cons_cons] at hred
      have hcon := hred.1 (by rw [hhead])
      rw [hhead] at hcon
      simp at hcon

section FreeParadox

variable {X G : Type*} [Group G] [MulAction G X]

/-- **Paradoxicality from a free action.** If the free group of rank two acts on `Y` through
`phi : F2 →* G` in such a way that `Y` is invariant and no nontrivial element of `F2` fixes a
point of `Y`, then `Y` is `G`-paradoxical. -/
theorem isParadoxical_of_free (phi : F2 →* G) (Y : Set X)
    (hinv : ∀ (w : F2) (y : X), y ∈ Y → phi w • y ∈ Y)
    (hfree : ∀ (w : F2) (y : X), y ∈ Y → phi w • y = y → w = 1) :
    IsParadoxical G Y := by
  classical
  -- the orbit equivalence relation on `Y`
  let r : Setoid Y :=
    { r := fun y z => ∃ w : F2, phi w • (y : X) = (z : X)
      iseqv :=
        { refl := fun y => ⟨1, by simp⟩
          symm := by
            rintro y z ⟨w, hw⟩
            exact ⟨w⁻¹, by rw [← hw, ← mul_smul, ← map_mul]; simp⟩
          trans := by
            rintro y z u ⟨w, hw⟩ ⟨v, hv⟩
            exact ⟨v * w, by rw [map_mul, mul_smul, hw, hv]⟩ } }
  let base : Y → Y := fun y => (Quotient.mk r y).out
  have hbase_rel : ∀ y : Y, ∃ w : F2, phi w • ((base y : Y) : X) = (y : X) := by
    intro y
    have : r.r (base y) y := Quotient.mk_out (s := r) y
    exact this
  have hbase_eq : ∀ y z : Y, (∃ w : F2, phi w • (y : X) = (z : X)) → base y = base z := by
    intro y z h
    show (Quotient.mk r y).out = (Quotient.mk r z).out
    congr 1
    exact Quotient.sound (s := r) h
  let ind : Y → F2 := fun y => (hbase_rel y).choose
  have hind : ∀ y : Y, phi (ind y) • ((base y : Y) : X) = (y : X) := fun y => (hbase_rel y).choose_spec
  have hind_unique : ∀ (y : Y) (w : F2), phi w • ((base y : Y) : X) = (y : X) → w = ind y := by
    intro y w hw
    have hb : phi ((ind y)⁻¹ * w) • ((base y : Y) : X) = ((base y : Y) : X) := by
      rw [map_mul, mul_smul, hw, ← hind y, ← mul_smul, ← map_mul]
      simp
    have := hfree ((ind y)⁻¹ * w) _ (base y).2 hb
    have h2 : w = ind y := by
      have := congrArg (fun t => ind y * t) this
      simpa [mul_assoc] using this
    exact h2
  -- the pieces indexed by subsets of `F2`
  set YS : Set F2 → Set X := fun S => {x : X | ∃ h : x ∈ Y, ind ⟨x, h⟩ ∈ S} with hYS
  have hYS_subset : ∀ S, YS S ⊆ Y := by
    rintro S x ⟨h, -⟩; exact h
  have hYS_univ : YS Set.univ = Y := by
    ext x
    constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, Set.mem_univ _⟩
  have hYS_union : ∀ S T, YS (S ∪ T) = YS S ∪ YS T := by
    intro S T
    ext x
    constructor
    · rintro ⟨h, hmem⟩
      rcases hmem with hs | ht
      · exact Or.inl ⟨h, hs⟩
      · exact Or.inr ⟨h, ht⟩
    · rintro (⟨h, hs⟩ | ⟨h, ht⟩)
      · exact ⟨h, Or.inl hs⟩
      · exact ⟨h, Or.inr ht⟩
  have hYS_disj : ∀ S T, Disjoint S T → Disjoint (YS S) (YS T) := by
    intro S T hST
    rw [Set.disjoint_left]
    rintro x ⟨h, hs⟩ ⟨h', ht⟩
    exact (hST.le_bot ⟨hs, ht⟩ : _ ∈ (⊥ : Set F2))
  have hind_smul : ∀ (v : F2) (x : X) (h : x ∈ Y),
      ind ⟨phi v • x, hinv v _ h⟩ = v * ind ⟨x, h⟩ := by
    intro v x h
    have hb : base ⟨phi v • x, hinv v _ h⟩ = base ⟨x, h⟩ := by
      refine (hbase_eq _ _ ⟨v⁻¹, ?_⟩)
      show phi v⁻¹ • (phi v • x) = x
      rw [← mul_smul, ← map_mul]; simp
    refine (hind_unique ⟨phi v • x, hinv v _ h⟩ (v * ind ⟨x, h⟩) ?_).symm
    rw [hb, map_mul, mul_smul, hind ⟨x, h⟩]
  have hYS_smul : ∀ (v : F2) (S : Set F2), phi v • YS S = YS (v • S) := by
    intro v S
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hyS⟩, rfl⟩
      exact ⟨hinv v _ hy, ⟨ind ⟨y, hy⟩, hyS, (hind_smul v y hy).symm⟩⟩
    · rintro ⟨h, ⟨s, hs, hsv⟩⟩
      have hxy : phi v • (phi v⁻¹ • x) = x := by rw [smul_smul, ← map_mul]; simp
      refine ⟨phi v⁻¹ • x, ⟨hinv v⁻¹ _ h, ?_⟩, hxy⟩
      have key : ind ⟨phi v • (phi v⁻¹ • x), hinv v _ (hinv v⁻¹ _ h)⟩
          = v * ind ⟨phi v⁻¹ • x, hinv v⁻¹ _ h⟩ := hind_smul v _ (hinv v⁻¹ _ h)
      have key2 : ind ⟨x, h⟩ = v * ind ⟨phi v⁻¹ • x, hinv v⁻¹ _ h⟩ := by
        rw [← key]
        congr 1
        exact Subtype.ext hxy.symm
      have hsv' : v * s = ind ⟨x, h⟩ := hsv
      have hs2 : s = ind ⟨phi v⁻¹ • x, hinv v⁻¹ _ h⟩ := mul_left_cancel (by rw [hsv', key2])
      rwa [← hs2]
  -- the four pieces
  set S1 := startsWith (0, true) with hS1
  set S2 := startsWith (0, false) with hS2
  set T1 := startsWith (1, true) with hT1
  set T2 := startsWith (1, false) with hT2
  have key : ∀ i : Fin 2,
      Equidec G Y (YS (startsWith (i, true)) ∪ YS (startsWith (i, false))) := by
    intro i
    have hdisj1 : Disjoint (YS (startsWith (i, true))) (YS (startsWith (i, false))) :=
      hYS_disj _ _ (startsWith_disjoint (by simp))
    have hdisj2 : Disjoint (YS (startsWith (i, true)))
        (phi (FreeGroup.of i) • YS (startsWith (i, false))) := by
      rw [hYS_smul]
      exact hYS_disj _ _ (startsWith_cover_disjoint i)
    have hunion : YS (startsWith (i, true)) ∪ phi (FreeGroup.of i) • YS (startsWith (i, false))
        = Y := by
      rw [hYS_smul, ← hYS_union, startsWith_cover i, hYS_univ]
    have := Equidec.union (G := G) (Equidec.refl (YS (startsWith (i, true))))
      (Equidec.smul_set (phi (FreeGroup.of i)) (YS (startsWith (i, false)))) hdisj1 hdisj2
    rw [hunion] at this
    exact this.symm
  refine ⟨YS S1 ∪ YS S2, YS T1 ∪ YS T2, ?_, ?_, ?_, key 0, key 1⟩
  · exact Set.union_subset (hYS_subset _) (hYS_subset _)
  · exact Set.union_subset (hYS_subset _) (hYS_subset _)
  · rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    refine ⟨⟨hYS_disj _ _ (startsWith_disjoint (by simp)),
      hYS_disj _ _ (startsWith_disjoint (by simp))⟩,
      ⟨hYS_disj _ _ (startsWith_disjoint (by simp)),
      hYS_disj _ _ (startsWith_disjoint (by simp))⟩⟩

end FreeParadox

end BT

/-
A free subgroup of rank two inside `SO(3)`, generated by two rotations by `arccos (1/3)`
about the `z`- and `x`-axes.
-/
import RequestProject.FreeAction

open Matrix Real

namespace BT

noncomputable section

/-- Rotation by `arccos (1/3)` about the `z`-axis. -/
noncomputable def rotA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1/3, -(2 * Real.sqrt 2)/3, 0;
     (2 * Real.sqrt 2)/3, 1/3, 0;
     0, 0, 1]

/-- Rotation by `arccos (1/3)` about the `x`-axis. -/
noncomputable def rotB : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, 1/3, -(2 * Real.sqrt 2)/3;
     0, (2 * Real.sqrt 2)/3, 1/3]

theorem sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem rotA_transpose_mul : rotAᵀ * rotA = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotA, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [sqrt_two_sq]

theorem rotA_mul_transpose : rotA * rotAᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotA, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [sqrt_two_sq]

theorem rotB_transpose_mul : rotBᵀ * rotB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [sqrt_two_sq]

theorem rotB_mul_transpose : rotB * rotBᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotB, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [sqrt_two_sq]

theorem rotA_det : rotA.det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotA]
  nlinarith [sqrt_two_sq]

theorem rotB_det : rotB.det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotB]
  nlinarith [sqrt_two_sq]

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

theorem rotA_mem : rotA ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr rotA_mul_transpose, rotA_det⟩

theorem rotB_mem : rotB ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr rotB_mul_transpose, rotB_det⟩

/-- The two generating rotations, as elements of `SO(3)`. -/
noncomputable def gen : Fin 2 → SO3 := fun i => if i = 0 then ⟨rotA, rotA_mem⟩ else ⟨rotB, rotB_mem⟩

/-- The homomorphism from the free group of rank two to `SO(3)`. -/
noncomputable def phi : F2 →* SO3 := FreeGroup.lift gen

/-- The rotation matrix attached to a letter of the free group. -/
noncomputable def letterMat (x : Fin 2 × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  if x.2 then (if x.1 = 0 then rotA else rotB) else (if x.1 = 0 then rotA else rotB)ᵀ

theorem fin2_cases (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> simp

theorem coe_phi_mk (L : List (Fin 2 × Bool)) :
    ((phi (FreeGroup.mk L) : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = (L.map letterMat).prod := by
  rw [phi, FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      rw [show ((((cond x.2 (gen x.1) (gen x.1)⁻¹) * (t.map fun y =>
          cond y.2 (gen y.1) (gen y.1)⁻¹).prod : SO3) : Matrix (Fin 3) (Fin 3) ℝ))
        = ((cond x.2 (gen x.1) (gen x.1)⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ) *
          (((t.map fun y => cond y.2 (gen y.1) (gen y.1)⁻¹).prod : SO3) :
            Matrix (Fin 3) (Fin 3) ℝ) from rfl]
      rw [ih]
      congr 1
      rcases fin2_cases x.1 with h | h <;> cases hx : x.2 <;>
        simp [letterMat, gen, h, hx] <;> rfl

/-! ### The integer state machine -/

/-- The sign attached to a boolean: `true` is the letter, `false` its inverse. -/
def sgn (e : Bool) : ℤ := if e then 1 else -1

/-- One step of the integer state machine: the state `(a, b, c)` represents the vector
`(a, b * √2, c) / 3 ^ k`. -/
def step (x : Fin 2 × Bool) (u : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if x.1 = 0 then (u.1 - 4 * sgn x.2 * u.2.1, 2 * sgn x.2 * u.1 + u.2.1, 3 * u.2.2)
  else (3 * u.1, u.2.1 - 2 * sgn x.2 * u.2.2, 4 * sgn x.2 * u.2.1 + u.2.2)

/-- The state reached by applying the word `L` (from right to left) to `(0, 1, 0)`. -/
def stateOf (L : List (Fin 2 × Bool)) : ℤ × ℤ × ℤ := L.foldr step (0, 1, 0)

@[simp] theorem stateOf_nil : stateOf [] = (0, 1, 0) := rfl

@[simp] theorem stateOf_cons (x : Fin 2 × Bool) (L : List (Fin 2 × Bool)) :
    stateOf (x :: L) = step x (stateOf L) := rfl

/-- The real vector attached to an integer state. -/
noncomputable def vecR (u : ℤ × ℤ × ℤ) : Fin 3 → ℝ :=
  ![(u.1 : ℝ), (u.2.1 : ℝ) * Real.sqrt 2, (u.2.2 : ℝ)]

theorem letterMat_mulVec (x : Fin 2 × Bool) (u : ℤ × ℤ × ℤ) :
    letterMat x *ᵥ vecR u = ((3 : ℝ)⁻¹) • vecR (step x u) := by
  funext i
  rcases fin2_cases x.1 with hx | hx <;> cases hb : x.2 <;>
    fin_cases i <;>
      simp [letterMat, step, sgn, hx, hb, rotA, rotB, vecR, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three, Matrix.transpose_apply]
  all_goals ring_nf
  all_goals (try rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)])
  all_goals (try ring)

/-- The mod-3 invariant satisfied by the state of a reduced word. -/
def Inv (L : List (Fin 2 × Bool)) : Prop :=
  ¬ ((3 : ℤ) ∣ (stateOf L).2.1) ∧
  (∀ e : Bool, L.head? = some (0, e) →
      ((stateOf L).1 + sgn e * (stateOf L).2.1) % 3 = 0 ∧ (stateOf L).2.2 % 3 = 0) ∧
  (∀ e : Bool, L.head? = some (1, e) →
      (stateOf L).1 % 3 = 0 ∧ ((stateOf L).2.2 - sgn e * (stateOf L).2.1) % 3 = 0) ∧
  (L = [] → (stateOf L).1 % 3 = 0 ∧ (stateOf L).2.2 % 3 = 0)

theorem sgn_cases (e : Bool) : sgn e = 1 ∨ sgn e = -1 := by cases e <;> simp [sgn]

theorem arith1 (a b s : ℤ) (hs : s = 1 ∨ s = -1) (hb : ¬ ((3:ℤ) ∣ b))
    (h : (a + s * b) % 3 = 0 ∨ a % 3 = 0) : ¬ ((3:ℤ) ∣ (2 * s * a + b)) := by
  rcases hs with rfl | rfl <;> omega

theorem arith2 (a b c s : ℤ) (hs : s = 1 ∨ s = -1) :
    ((a - 4 * s * b) + s * (2 * s * a + b)) % 3 = 0 ∧ (3 * c) % 3 = 0 := by
  rcases hs with rfl | rfl <;> omega

theorem arith3 (b c s : ℤ) (hs : s = 1 ∨ s = -1) (hb : ¬ ((3:ℤ) ∣ b))
    (h : (c - s * b) % 3 = 0 ∨ c % 3 = 0) : ¬ ((3:ℤ) ∣ (b - 2 * s * c)) := by
  rcases hs with rfl | rfl <;> omega

theorem arith4 (a b c s : ℤ) (hs : s = 1 ∨ s = -1) :
    (3 * a) % 3 = 0 ∧ ((4 * s * b + c) - s * (b - 2 * s * c)) % 3 = 0 := by
  rcases hs with rfl | rfl <;> omega

theorem inv_of_isReduced : ∀ L : List (Fin 2 × Bool), FreeGroup.IsReduced L → Inv L := by
  intro L
  induction L with
  | nil =>
      intro _
      refine ⟨by decide, ?_, ?_, ?_⟩ <;> simp
  | cons x L ih =>
      intro hred
      have hredL : FreeGroup.IsReduced L := hred.infix (List.suffix_cons x L).isInfix
      obtain ⟨hb, h0, h1, hnil⟩ := ih hredL
      have hfact0 : x.1 = 0 →
          ((stateOf L).1 + sgn x.2 * (stateOf L).2.1) % 3 = 0 ∨ (stateOf L).1 % 3 = 0 := by
        intro hx0
        cases L with
        | nil => exact Or.inr (hnil rfl).1
        | cons hd tl =>
            rcases fin2_cases hd.1 with hh | hh
            · have hhd : hd = ((0 : Fin 2), hd.2) := Prod.ext hh rfl
              have hx2 : x.2 = hd.2 := (FreeGroup.isReduced_cons_cons.mp hred).1 (by rw [hx0, hh])
              have hfin := h0 hd.2 (by rw [List.head?_cons, hhd])
              exact Or.inl (by rw [hx2]; exact hfin.1)
            · have hhd : hd = ((1 : Fin 2), hd.2) := Prod.ext hh rfl
              exact Or.inr (h1 hd.2 (by rw [List.head?_cons, hhd])).1
      have hfact1 : x.1 = 1 →
          ((stateOf L).2.2 - sgn x.2 * (stateOf L).2.1) % 3 = 0 ∨ (stateOf L).2.2 % 3 = 0 := by
        intro hx1
        cases L with
        | nil => exact Or.inr (hnil rfl).2
        | cons hd tl =>
            rcases fin2_cases hd.1 with hh | hh
            · have hhd : hd = ((0 : Fin 2), hd.2) := Prod.ext hh rfl
              exact Or.inr (h0 hd.2 (by rw [List.head?_cons, hhd])).2
            · have hhd : hd = ((1 : Fin 2), hd.2) := Prod.ext hh rfl
              have hx2 : x.2 = hd.2 := (FreeGroup.isReduced_cons_cons.mp hred).1 (by rw [hx1, hh])
              have hfin := h1 hd.2 (by rw [List.head?_cons, hhd])
              exact Or.inl (by rw [hx2]; exact hfin.2)
      rcases fin2_cases x.1 with hx | hx
      · have hs : stateOf (x :: L) = ((stateOf L).1 - 4 * sgn x.2 * (stateOf L).2.1,
            2 * sgn x.2 * (stateOf L).1 + (stateOf L).2.1, 3 * (stateOf L).2.2) := by
          rw [stateOf_cons, step, if_pos hx]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hs]
          exact arith1 _ _ _ (sgn_cases x.2) hb (hfact0 hx)
        · intro e he
          have hxe : x = ((0 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          have hx2 : x.2 = e := by rw [hxe]
          rw [hs, ← hx2]
          exact arith2 _ _ _ _ (sgn_cases x.2)
        · intro e he
          have hxe : x = ((1 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          rw [hxe] at hx
          simp at hx
        · intro hcon
          exact absurd hcon (List.cons_ne_nil _ _)
      · have hs : stateOf (x :: L) = (3 * (stateOf L).1,
            (stateOf L).2.1 - 2 * sgn x.2 * (stateOf L).2.2,
            4 * sgn x.2 * (stateOf L).2.1 + (stateOf L).2.2) := by
          rw [stateOf_cons, step, if_neg (by rw [hx]; decide)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hs]
          exact arith3 _ _ _ (sgn_cases x.2) hb (hfact1 hx)
        · intro e he
          have hxe : x = ((0 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          rw [hxe] at hx
          simp at hx
        · intro e he
          have hxe : x = ((1 : Fin 2), e) := Option.some_inj.mp (by rw [← List.head?_cons]; exact he)
          have hx2 : x.2 = e := by rw [hxe]
          rw [hs, ← hx2]
          exact arith4 _ _ _ _ (sgn_cases x.2)
        · intro hcon
          exact absurd hcon (List.cons_ne_nil _ _)

/-! ### Freeness -/

theorem prod_mulVec (L : List (Fin 2 × Bool)) :
    (L.map letterMat).prod *ᵥ vecR (0, 1, 0) = (((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L) := by
  induction L with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        letterMat_mulVec, stateOf_cons, List.length_cons, smul_smul, pow_succ]

theorem prod_ne_one {L : List (Fin 2 × Bool)} (hred : FreeGroup.IsReduced L) (hne : L ≠ []) :
    (L.map letterMat).prod ≠ 1 := by
  intro hone
  have h := prod_mulVec L
  rw [hone, Matrix.one_mulVec] at h
  have hsq : Real.sqrt 2 ≠ 0 := by positivity
  have hLv : vecR (0, 1, 0) 1 = Real.sqrt 2 := by norm_num [vecR]
  have hRv : ((((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L)) 1
      = ((3 : ℝ)⁻¹) ^ L.length * (((stateOf L).2.1 : ℝ) * Real.sqrt 2) := by
    simp [vecR]
  have h1 : Real.sqrt 2 = ((3 : ℝ)⁻¹) ^ L.length * (((stateOf L).2.1 : ℝ) * Real.sqrt 2) :=
    calc Real.sqrt 2 = vecR (0, 1, 0) 1 := hLv.symm
      _ = ((((3 : ℝ)⁻¹) ^ L.length) • vecR (stateOf L)) 1 := by rw [h]
      _ = _ := hRv
  have h1' : (1 : ℝ) * Real.sqrt 2
      = (((3 : ℝ)⁻¹) ^ L.length * ((stateOf L).2.1 : ℝ)) * Real.sqrt 2 := by
    linear_combination h1
  have h2 : (1 : ℝ) = ((3 : ℝ)⁻¹) ^ L.length * ((stateOf L).2.1 : ℝ) :=
    mul_right_cancel₀ hsq h1'
  have h3 : ((stateOf L).2.1 : ℝ) = (3 : ℝ) ^ L.length := by
    rw [inv_pow] at h2
    field_simp at h2
    linarith [h2]
  have h4 : (stateOf L).2.1 = 3 ^ L.length := by
    have : ((stateOf L).2.1 : ℝ) = ((3 ^ L.length : ℤ) : ℝ) := by push_cast; exact h3
    exact_mod_cast this
  have hlen : L.length ≠ 0 := by simpa using hne
  have hdvd : (3 : ℤ) ∣ (stateOf L).2.1 := by
    rw [h4]
    exact dvd_pow_self 3 hlen
  exact (inv_of_isReduced L hred).1 hdvd

theorem phi_injective : Function.Injective phi := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  have hne' : w.toWord ≠ [] := by
    intro h
    exact hne (FreeGroup.toWord_eq_nil_iff.mp h)
  have hcoe : (w.toWord.map letterMat).prod = 1 := by
    rw [← coe_phi_mk, FreeGroup.mk_toWord, hw]
    rfl
  exact prod_ne_one FreeGroup.isReduced_toWord hne' hcoe

end

end BT

/-
Basic theory of equidecomposability and paradoxical sets, built on Mathlib's `Equidecomp`.
-/
import Mathlib

open Set Function Pointwise

namespace BT

variable {X Y G G' : Type*}

section Defs

variable [Group G] [MulAction G X]

/-- Two sets `A B : Set X` are `G`-equidecomposable if there is an equidecomposition
of `X` (in the sense of Mathlib's `Equidecomp`) whose source is `A` and whose target is `B`. -/
def Equidec (G : Type*) [Group G] [MulAction G X] (A B : Set X) : Prop :=
  ∃ f : Equidecomp X G, f.source = A ∧ f.target = B

/-- A set `A` is `G`-paradoxical if it contains two disjoint subsets, each of which is
`G`-equidecomposable with `A` itself. -/
def IsParadoxical (G : Type*) [Group G] [MulAction G X] (A : Set X) : Prop :=
  ∃ B C : Set X, B ⊆ A ∧ C ⊆ A ∧ Disjoint B C ∧ Equidec G A B ∧ Equidec G A C

end Defs

section Basic

variable [Group G] [MulAction G X] {A B C : Set X}

/-- Basic constructor for equidecomposability. -/
theorem Equidec.mk' (phi psi : X → X) (S : Finset G)
    (hmap : ∀ x ∈ A, phi x ∈ B) (hmap' : ∀ y ∈ B, psi y ∈ A)
    (hleft : ∀ x ∈ A, psi (phi x) = x) (hright : ∀ y ∈ B, phi (psi y) = y)
    (hdec : ∀ x ∈ A, ∃ g ∈ S, phi x = g • x) : Equidec G A B :=
  ⟨{ toFun := phi
     invFun := psi
     source := A
     target := B
     map_source' := hmap
     map_target' := hmap'
     left_inv' := hleft
     right_inv' := hright
     isDecompOn' := ⟨S, hdec⟩ }, rfl, rfl⟩

@[refl]
theorem Equidec.refl (A : Set X) : Equidec G A A :=
  Equidec.mk' id id {1} (fun x hx => hx) (fun x hx => hx) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x _ => ⟨1, Finset.mem_singleton_self 1, by simp⟩)

@[symm]
theorem Equidec.symm (h : Equidec G A B) : Equidec G B A := by
  obtain ⟨f, hs, ht⟩ := h
  exact ⟨f.symm, by simpa using ht, by simpa using hs⟩

theorem Equidec.trans (h₁ : Equidec G A B) (h₂ : Equidec G B C) : Equidec G A C := by
  classical
  obtain ⟨f, hfs, hft⟩ := h₁
  obtain ⟨g, hgs, hgt⟩ := h₂
  refine Equidec.mk' (g ∘ f) (f.toPartialEquiv.symm ∘ g.toPartialEquiv.symm)
    (g.witness * f.witness) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [← hgt]
    apply Equidecomp.apply_mem_target
    rw [hgs, ← hft]
    exact Equidecomp.apply_mem_target (hfs ▸ hx)
  · intro y hy
    rw [← hfs]
    apply Equidecomp.map_target
    rw [hft, ← hgs]
    exact Equidecomp.map_target (hgt ▸ hy)
  · intro x hx
    have hxs : x ∈ f.source := hfs ▸ hx
    have : f x ∈ g.source := by rw [hgs, ← hft]; exact Equidecomp.apply_mem_target hxs
    simp only [comp_apply]
    rw [Equidecomp.left_inv this, Equidecomp.left_inv hxs]
  · intro y hy
    have hyt : y ∈ g.target := hgt ▸ hy
    have : g.toPartialEquiv.symm y ∈ f.target := by
      rw [hft, ← hgs]; exact Equidecomp.map_target hyt
    simp only [comp_apply]
    rw [Equidecomp.right_inv this, Equidecomp.right_inv hyt]
  · intro x hx
    have hxs : x ∈ f.source := hfs ▸ hx
    have hfx : f x ∈ g.source := by rw [hgs, ← hft]; exact Equidecomp.apply_mem_target hxs
    obtain ⟨a, ha, hax⟩ := f.isDecompOn x hxs
    obtain ⟨b, hb, hbx⟩ := g.isDecompOn (f x) hfx
    exact ⟨b * a, Finset.mul_mem_mul hb ha, by
      rw [comp_apply, hbx, hax, mul_smul]⟩

/-- Translating a set by a group element gives an equidecomposable set. -/
theorem Equidec.smul_set (g : G) (A : Set X) : Equidec G A (g • A) :=
  Equidec.mk' (fun x => g • x) (fun x => g⁻¹ • x) {g}
    (fun x hx => ⟨x, hx, rfl⟩)
    (by rintro y ⟨x, hx, rfl⟩; simpa using hx)
    (fun x _ => by simp)
    (by rintro y ⟨x, hx, rfl⟩; simp)
    (fun x _ => ⟨g, Finset.mem_singleton_self g, rfl⟩)

/-- Gluing two equidecompositions along a disjoint union. -/
theorem Equidec.union {A₁ A₂ B₁ B₂ : Set X} (h₁ : Equidec G A₁ B₁) (h₂ : Equidec G A₂ B₂)
    (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    Equidec G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f, hfs, hft⟩ := h₁
  obtain ⟨g, hgs, hgt⟩ := h₂
  refine Equidec.mk' (fun x => if x ∈ A₁ then f x else g x)
    (fun y => if y ∈ B₁ then f.toPartialEquiv.symm y else g.toPartialEquiv.symm y)
    (f.witness ∪ g.witness) ?_ ?_ ?_ ?_ ?_
  · rintro x (hx | hx)
    · simp only [hx, if_pos]
      exact Or.inl (hft ▸ Equidecomp.apply_mem_target (hfs ▸ hx))
    · have hx1 : x ∉ A₁ := fun h => (hA.le_bot ⟨h, hx⟩ : x ∈ (⊥ : Set X))
      simp only [hx1, if_neg, not_false_iff]
      exact Or.inr (hgt ▸ Equidecomp.apply_mem_target (hgs ▸ hx))
  · rintro y (hy | hy)
    · simp only [hy, if_pos]
      exact Or.inl (hfs ▸ Equidecomp.map_target (hft ▸ hy))
    · have hy1 : y ∉ B₁ := fun h => (hB.le_bot ⟨h, hy⟩ : y ∈ (⊥ : Set X))
      simp only [hy1, if_neg, not_false_iff]
      exact Or.inr (hgs ▸ Equidecomp.map_target (hgt ▸ hy))
  · rintro x (hx | hx)
    · have h1 : f x ∈ B₁ := hft ▸ Equidecomp.apply_mem_target (hfs ▸ hx)
      simp only [hx, if_pos, h1]
      exact Equidecomp.left_inv (hfs ▸ hx)
    · have hx1 : x ∉ A₁ := fun h => (hA.le_bot ⟨h, hx⟩ : x ∈ (⊥ : Set X))
      have h2 : g x ∈ B₂ := hgt ▸ Equidecomp.apply_mem_target (hgs ▸ hx)
      have h2' : g x ∉ B₁ := fun h => (hB.le_bot ⟨h, h2⟩ : g x ∈ (⊥ : Set X))
      simp only [hx1, if_neg, not_false_iff, h2']
      exact Equidecomp.left_inv (hgs ▸ hx)
  · rintro y (hy | hy)
    · have h1 : f.toPartialEquiv.symm y ∈ A₁ := hfs ▸ Equidecomp.map_target (hft ▸ hy)
      simp only [hy, if_pos, h1]
      exact Equidecomp.right_inv (hft ▸ hy)
    · have hy1 : y ∉ B₁ := fun h => (hB.le_bot ⟨h, hy⟩ : y ∈ (⊥ : Set X))
      have h2 : g.toPartialEquiv.symm y ∈ A₂ := hgs ▸ Equidecomp.map_target (hgt ▸ hy)
      have h2' : g.toPartialEquiv.symm y ∉ A₁ := fun h => (hA.le_bot ⟨h, h2⟩ : _ ∈ (⊥ : Set X))
      simp only [hy1, if_neg, not_false_iff, h2']
      exact Equidecomp.right_inv (hgt ▸ hy)
  · rintro x (hx | hx)
    · obtain ⟨a, ha, hax⟩ := f.isDecompOn x (hfs ▸ hx)
      exact ⟨a, Finset.mem_union_left _ ha, by simp only [hx, if_pos]; exact hax⟩
    · have hx1 : x ∉ A₁ := fun h => (hA.le_bot ⟨h, hx⟩ : x ∈ (⊥ : Set X))
      obtain ⟨a, ha, hax⟩ := g.isDecompOn x (hgs ▸ hx)
      exact ⟨a, Finset.mem_union_right _ ha, by
        simp only [hx1, if_neg, not_false_iff]; exact hax⟩

/-- The restriction of an equidecomposition to a subset of its source. -/
theorem Equidec.image {A A' : Set X} {f : Equidecomp X G} (hfs : f.source = A) (hA' : A' ⊆ A) :
    Equidec G A' (f '' A') := by
  refine Equidec.mk' f f.toPartialEquiv.symm f.witness (fun x hx => ⟨x, hx, rfl⟩) ?_ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [Equidecomp.left_inv (hfs ▸ hA' hx)]
    exact hx
  · intro x hx
    exact Equidecomp.left_inv (hfs ▸ hA' hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Equidecomp.left_inv (hfs ▸ hA' hx)]
  · intro x hx
    exact f.isDecompOn x (hfs ▸ hA' hx)

/-- Paradoxicality transfers along equidecompositions. -/
theorem IsParadoxical.of_equidec {A B : Set X} (hAB : Equidec G A B) (hA : IsParadoxical G A) :
    IsParadoxical G B := by
  obtain ⟨P, Q, hP, hQ, hPQ, hAP, hAQ⟩ := hA
  obtain ⟨f, hfs, hft⟩ := hAB
  have hinj : Set.InjOn f A := by
    intro x hx y hy hxy
    have h1 := Equidecomp.left_inv (f := f) (hfs ▸ hx)
    rw [hxy, Equidecomp.left_inv (f := f) (hfs ▸ hy)] at h1
    exact h1.symm
  have hsub : ∀ {S : Set X}, S ⊆ A → f '' S ⊆ B := by
    rintro S hS _ ⟨x, hx, rfl⟩
    exact hft ▸ Equidecomp.apply_mem_target (hfs ▸ hS hx)
  refine ⟨f '' P, f '' Q, hsub hP, hsub hQ, ?_, ?_, ?_⟩
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
    have hxx : x' = x := hinj (hQ hx') (hP hx) hxx'
    subst hxx
    exact (hPQ.le_bot ⟨hx, hx'⟩ : x' ∈ (⊥ : Set X))
  · exact (Equidec.symm ⟨f, hfs, hft⟩).trans (hAP.trans (Equidec.image hfs hP))
  · exact (Equidec.symm ⟨f, hfs, hft⟩).trans (hAQ.trans (Equidec.image hfs hQ))

/-- Transporting an equidecomposition along a map of acting groups compatible with the actions. -/
theorem Equidec.map {G' : Type*} [Group G'] [MulAction G' X] (F : G → G')
    (hF : ∀ (g : G) (x : X), F g • x = g • x) {A B : Set X} (h : Equidec G A B) :
    Equidec G' A B := by
  classical
  obtain ⟨f, hfs, hft⟩ := h
  refine Equidec.mk' f f.toPartialEquiv.symm (f.witness.image F) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hft ▸ Equidecomp.apply_mem_target (hfs ▸ hx)
  · intro y hy; exact hfs ▸ Equidecomp.map_target (hft ▸ hy)
  · intro x hx; exact Equidecomp.left_inv (hfs ▸ hx)
  · intro y hy; exact Equidecomp.right_inv (hft ▸ hy)
  · intro x hx
    obtain ⟨g, hg, hgx⟩ := f.isDecompOn x (hfs ▸ hx)
    exact ⟨F g, Finset.mem_image_of_mem F hg, by rw [hF, hgx]⟩

/-- Transporting paradoxicality along a map of acting groups compatible with the actions. -/
theorem IsParadoxical.map {G' : Type*} [Group G'] [MulAction G' X] (F : G → G')
    (hF : ∀ (g : G) (x : X), F g • x = g • x) {A : Set X} (h : IsParadoxical G A) :
    IsParadoxical G' A := by
  obtain ⟨P, Q, hP, hQ, hPQ, hAP, hAQ⟩ := h
  exact ⟨P, Q, hP, hQ, hPQ, hAP.map F hF, hAQ.map F hF⟩

/-- **Absorption lemma**: if `rho` moves `D` off itself under all positive powers, and all the
powers `rho ^ n • D` stay inside `A`, then `A` is equidecomposable with `A \ D`. -/
theorem Equidec.absorb {A D : Set X} (rho : G)
    (hsub : ∀ n : ℕ, (rho ^ n) • D ⊆ A)
    (hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((rho ^ n) • D) D) :
    Equidec G A (A \ D) := by
  set U : Set X := ⋃ n : ℕ, (rho ^ n) • D with hU
  have hUA : U ⊆ A := Set.iUnion_subset hsub
  have hDU : D ⊆ U := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
  have hrhoU : rho • U = U \ D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      have hmem : rho • y ∈ (rho ^ (n + 1)) • D := by
        obtain ⟨d, hd, rfl⟩ := hn
        exact ⟨d, hd, by rw [← mul_smul, ← pow_succ']⟩
      refine ⟨Set.mem_iUnion.2 ⟨n + 1, hmem⟩, ?_⟩
      intro hxD
      exact ((hdisj (n + 1) (Nat.le_add_left 1 n)).le_bot ⟨hmem, hxD⟩ : _ ∈ (⊥ : Set X))
    · rintro ⟨hxU, hxD⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hxU
      match n, hn with
      | 0, hn => exact absurd (by simpa using hn) hxD
      | (m + 1), hn =>
        obtain ⟨d, hd, rfl⟩ := hn
        refine ⟨(rho ^ m) • d, Set.mem_iUnion.2 ⟨m, ⟨d, hd, rfl⟩⟩, ?_⟩
        show rho • (rho ^ m • d) = rho ^ (m + 1) • d
        rw [← mul_smul, ← pow_succ']
  have hsplit : A = U ∪ (A \ U) := by
    rw [Set.union_diff_cancel hUA]
  have hsplit' : A \ D = (U \ D) ∪ (A \ U) := by
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨hxA, hxD⟩
      by_cases hxU : x ∈ U
      · exact Or.inl ⟨hxU, hxD⟩
      · exact Or.inr ⟨hxA, hxU⟩
    · rintro (⟨hxU, hxD⟩ | ⟨hxA, hxU⟩)
      · exact ⟨hUA hxU, hxD⟩
      · exact ⟨hxA, fun hxD => hxU (hDU hxD)⟩
  have key : Equidec G (U ∪ (A \ U)) ((U \ D) ∪ (A \ U)) := by
    refine Equidec.union ?_ (Equidec.refl _) ?_ ?_
    · have h := Equidec.smul_set rho U
      rwa [hrhoU] at h
    · exact Set.disjoint_sdiff_right.mono_left le_rfl
    · exact Set.disjoint_of_subset_left Set.diff_subset Set.disjoint_sdiff_right
  rw [← hsplit'] at key
  rw [← hsplit] at key
  exact key

end Basic

end BT

/-
From the sphere to the ball: the Banach–Tarski paradox.
-/
import RequestProject.Absorb

open Matrix Set Pointwise

namespace BT

noncomputable section

/-! ### The isometry group of `ℝ³` acting on `ℝ³` -/

/-- The group of isometries of `ℝ³`. -/
abbrev Iso3 := E ≃ᵢ E

instance : MulAction Iso3 E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem iso3_smul_def (g : Iso3) (x : E) : g • x = g x := rfl

/-! ### Rotations as isometries -/

theorem so3_smul_sub (M : SO3) (x y : E) : M • (x - y) = M • x - M • y := by
  ext i
  show ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (x - y) j
      = ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j - ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * y j
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (x j - y j) = _
  ring

theorem so3_smul_smul (M : SO3) (c : ℝ) (x : E) : M • (c • x) = c • (M • x) := by
  ext i
  show ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (c • x) j
      = c * ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (c * x j) = c * ((M : Matrix (Fin 3) (Fin 3) ℝ) i j * x j)
  ring

/-- A rotation, viewed as an isometry of `ℝ³`. -/
def rotIso (M : SO3) : Iso3 where
  toFun := fun x => M • x
  invFun := fun x => M⁻¹ • x
  left_inv := fun x => by
    show M⁻¹ • (M • x) = x
    rw [smul_smul, inv_mul_cancel, one_smul]
  right_inv := fun x => by
    show M • (M⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel, one_smul]
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    show dist (M • x) (M • y) = dist x y
    rw [dist_eq_norm, dist_eq_norm, ← so3_smul_sub, norm_smul_so3]

theorem rotIso_smul (M : SO3) (x : E) : rotIso M • x = M • x := rfl

theorem isParadoxical_iso3_of_so3 {A : Set E} (h : IsParadoxical SO3 A) : IsParadoxical Iso3 A :=
  IsParadoxical.map rotIso (fun g x => rotIso_smul g x) h

/-! ### Radial extension: from the sphere to the punctured ball -/

/-- The (punctured) cone over a subset of the sphere. -/
def cone (A : Set E) : Set E := {x : E | x ≠ 0 ∧ ‖x‖ ≤ 1 ∧ ‖x‖⁻¹ • x ∈ A}

theorem cone_subset (A : Set E) : cone A ⊆ Metric.closedBall (0 : E) 1 \ {0} := by
  rintro x ⟨hx0, hx1, -⟩
  exact ⟨by simpa [Metric.mem_closedBall] using hx1, hx0⟩

theorem cone_sph : cone sph = Metric.closedBall (0 : E) 1 \ {0} := by
  ext x
  constructor
  · exact fun hx => cone_subset sph hx
  · rintro ⟨hx1, hx0⟩
    have hx0' : x ≠ 0 := hx0
    have hn : ‖x‖ ≠ 0 := fun h => hx0' (norm_eq_zero.mp h)
    refine ⟨hx0', by simpa [Metric.mem_closedBall] using hx1, ?_⟩
    show ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

theorem cone_mono {A B : Set E} (h : A ⊆ B) : cone A ⊆ cone B :=
  fun _ hx => ⟨hx.1, hx.2.1, h hx.2.2⟩

theorem cone_disjoint {A B : Set E} (h : Disjoint A B) : Disjoint (cone A) (cone B) := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  exact (h.le_bot ⟨hxA.2.2, hxB.2.2⟩ : _ ∈ (⊥ : Set E))

/-- Rescaling a unit vector to length `r ≤ 1` lands in the cone. -/
theorem cone_radial {T : Set E} (hT : T ⊆ sph) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {v : E} (hv : v ∈ T) :
    ‖r • v‖ = r ∧ r • v ∈ cone T ∧ ‖r • v‖⁻¹ • (r • v) = v := by
  have hv1 : ‖v‖ = 1 := hT hv
  have hnorm : ‖r • v‖ = r := by
    rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  have hlast : ‖r • v‖⁻¹ • (r • v) = v := by
    rw [hnorm, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul]
  refine ⟨hnorm, ⟨?_, by rw [hnorm]; exact hr1, by rw [hlast]; exact hv⟩, hlast⟩
  intro hc
  rw [hc, norm_zero] at hnorm
  exact (ne_of_gt hr) hnorm.symm

theorem equidec_cone {A B : Set E} (hA : A ⊆ sph) (hB : B ⊆ sph) (h : Equidec SO3 A B) :
    Equidec SO3 (cone A) (cone B) := by
  classical
  obtain ⟨f, hfs, hft⟩ := h
  refine Equidec.mk' (fun x => ‖x‖ • f (‖x‖⁻¹ • x))
    (fun y => ‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)) f.witness ?_ ?_ ?_ ?_ ?_
  · rintro x ⟨hx0, hx1, hxA⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfu : f (‖x‖⁻¹ • x) ∈ B := hft ▸ Equidecomp.apply_mem_target (hfs ▸ hxA)
    exact (cone_radial hB hr hx1 hfu).2.1
  · rintro y ⟨hy0, hy1, hyB⟩
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hfu : f.toPartialEquiv.symm (‖y‖⁻¹ • y) ∈ A := hfs ▸ Equidecomp.map_target (hft ▸ hyB)
    exact (cone_radial hA hr hy1 hfu).2.1
  · rintro x ⟨hx0, hx1, hxA⟩
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfu : f (‖x‖⁻¹ • x) ∈ B := hft ▸ Equidecomp.apply_mem_target (hfs ▸ hxA)
    obtain ⟨hn, -, -⟩ := cone_radial hB hr hx1 hfu
    show ‖‖x‖ • f (‖x‖⁻¹ • x)‖ • f.toPartialEquiv.symm
      (‖‖x‖ • f (‖x‖⁻¹ • x)‖⁻¹ • (‖x‖ • f (‖x‖⁻¹ • x))) = x
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
      Equidecomp.left_inv (hfs ▸ hxA), smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro y ⟨hy0, hy1, hyB⟩
    have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hfu : f.toPartialEquiv.symm (‖y‖⁻¹ • y) ∈ A := hfs ▸ Equidecomp.map_target (hft ▸ hyB)
    obtain ⟨hn, -, -⟩ := cone_radial hA hr hy1 hfu
    show ‖‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)‖ • f
      (‖‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y)‖⁻¹ • (‖y‖ • f.toPartialEquiv.symm (‖y‖⁻¹ • y))) = y
    rw [hn, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul,
      Equidecomp.right_inv (hft ▸ hyB), smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
  · rintro x ⟨hx0, hx1, hxA⟩
    obtain ⟨g, hg, hgx⟩ := f.isDecompOn (‖x‖⁻¹ • x) (hfs ▸ hxA)
    refine ⟨g, hg, ?_⟩
    have hr : ‖x‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hx0)
    show ‖x‖ • f (‖x‖⁻¹ • x) = g • x
    rw [hgx, so3_smul_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem isParadoxical_punctured_ball : IsParadoxical SO3 (Metric.closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨P, Q, hP, hQ, hPQ, hsP, hsQ⟩ := isParadoxical_sph
  refine ⟨cone P, cone Q, ?_, ?_, cone_disjoint hPQ, ?_, ?_⟩
  · rw [← cone_sph]; exact cone_mono hP
  · rw [← cone_sph]; exact cone_mono hQ
  · rw [← cone_sph]; exact equidec_cone (fun _ hx => hx) hP hsP
  · rw [← cone_sph]; exact equidec_cone (fun _ hx => hx) hQ hsQ

/-! ### Absorbing the centre -/

/-- The centre of the auxiliary rotation axis, the point `(1/2, 0, 0)`. -/
def cVec : E := EuclideanSpace.single 0 (1 / 2 : ℝ)

/-- Rotation by one radian about the axis through `cVec` parallel to the `z`-axis. -/
def centerRot : Iso3 :=
  ((IsometryEquiv.constVAdd (-cVec) : E ≃ᵢ E).trans (rotIso (rZ 1))).trans
    (IsometryEquiv.constVAdd cVec : E ≃ᵢ E)

theorem centerRot_apply (x : E) : centerRot • x = cVec + rZ 1 • (x - cVec) := by
  show cVec + rZ 1 • (-cVec + x) = cVec + rZ 1 • (x - cVec)
  rw [show (-cVec + x : E) = x - cVec by abel]

theorem so3_smul_zero (M : SO3) : M • (0 : E) = 0 := by
  ext i
  show ∑ j, (M : Matrix (Fin 3) (Fin 3) ℝ) i j * (0 : E) j = (0 : E) i
  simp

theorem centerRot_pow_apply (n : ℕ) : ∀ x : E,
    (centerRot ^ n) • x = cVec + (rZ (n : ℝ)) • (x - cVec) := by
  induction n with
  | zero =>
      intro x
      simp only [pow_zero, Nat.cast_zero, rZ_zero, one_smul]
      abel
  | succ m ih =>
      intro x
      rw [pow_succ, SemigroupAction.mul_smul, ih, centerRot_apply,
        show (cVec + rZ 1 • (x - cVec) - cVec : E) = rZ 1 • (x - cVec) by abel,
        Nat.cast_add, Nat.cast_one, rZ_add, ← smul_smul]

theorem centerRot_pow_apply_zero (n : ℕ) :
    (centerRot ^ n) • (0 : E) = cVec - (rZ (n : ℝ)) • cVec := by
  have hneg : (rZ (n : ℝ)) • (-cVec : E) = -((rZ (n : ℝ)) • cVec) := by
    have h := so3_smul_sub (rZ (n : ℝ)) 0 cVec
    rw [zero_sub, so3_smul_zero, zero_sub] at h
    exact h
  rw [centerRot_pow_apply, zero_sub, hneg]
  abel

theorem norm_cVec : ‖cVec‖ = 1 / 2 := by
  rw [cVec, EuclideanSpace.norm_single]; norm_num

theorem cVec_zero : cVec 0 = 1 / 2 := by
  simp [cVec, EuclideanSpace.single_apply]

/-- A rotation by a positive whole number of radians about the `z`-axis does not fix `cVec`
(this is where the irrationality of `π` enters). -/
theorem rZ_nat_smul_cVec_ne (n : ℕ) (hn : 1 ≤ n) : (rZ (n : ℝ)) • cVec ≠ cVec := by
  intro hc
  have hoff : cVec 0 ≠ 0 ∨ cVec 1 ≠ 0 := Or.inl (by rw [cVec_zero]; norm_num)
  obtain ⟨hcos, -⟩ := rZ_fix (n : ℝ) cVec hoff hc
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (n : ℝ)).mp hcos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    linarith [hk ▸ hnpos]
  have hpi : Real.pi = (n : ℝ) / (2 * k) := by
    have h2k : (2 * (k : ℝ)) ≠ 0 := by
      simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
      exact_mod_cast hk0
    field_simp
    linarith [hk]
  have hirr : Irrational ((((n : ℚ) / (2 * (k : ℚ))) : ℚ) : ℝ) := by
    rw [show ((((n : ℚ) / (2 * (k : ℚ))) : ℚ) : ℝ) = (n : ℝ) / (2 * (k : ℝ)) by push_cast; ring,
      ← hpi]
    exact irrational_pi
  exact (Rat.not_irrational _) hirr

theorem equidec_ball_punctured :
    Equidec Iso3 (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : E) 1 \ {0}) := by
  refine Equidec.absorb centerRot ?_ ?_
  · intro n
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show (centerRot ^ n) • (0 : E) ∈ Metric.closedBall (0 : E) 1
    rw [mem_closedBall_zero_iff, centerRot_pow_apply_zero n]
    calc ‖cVec - (rZ (n : ℝ)) • cVec‖ ≤ ‖cVec‖ + ‖(rZ (n : ℝ)) • cVec‖ := norm_sub_le _ _
      _ = 1 := by rw [norm_smul_so3, norm_cVec]; norm_num
  · intro n hn
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hmem
    rw [Set.mem_singleton_iff] at hy
    subst hy
    replace hmem : (centerRot ^ n) • (0 : E) = 0 := hmem
    rw [centerRot_pow_apply_zero n, sub_eq_zero] at hmem
    exact rZ_nat_smul_cVec_ne n hn hmem.symm

/-- **The Banach–Tarski paradox** for the closed unit ball of `ℝ³`. -/
theorem isParadoxical_ball : IsParadoxical Iso3 (Metric.closedBall (0 : E) 1) :=
  IsParadoxical.of_equidec (Equidec.symm equidec_ball_punctured)
    (isParadoxical_iso3_of_so3 isParadoxical_punctured_ball)

end

end BT

/-
The Hausdorff paradox: the unit sphere in `ℝ³` is `SO(3)`-paradoxical.
-/
import RequestProject.FreeRotations

open Matrix Set Pointwise

namespace BT

noncomputable section

/-- Euclidean 3-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-! ### `SO(3)` acts by isometries -/

theorem inner_eq_dotProduct (x y : E) : (inner ℝ x y : ℝ) = x.ofLp ⬝ᵥ y.ofLp := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem smul_ofLp (M : SO3) (x : E) :
    (M • x).ofLp = (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x.ofLp := rfl

theorem so3_transpose_mul (M : SO3) :
    (M : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (M : Matrix (Fin 3) (Fin 3) ℝ) = 1 := M.2.1.1

theorem so3_det (M : SO3) : (M : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := M.2.2

theorem inner_smul_smul (M : SO3) (x y : E) :
    (inner ℝ (M • x) (M • y) : ℝ) = inner ℝ x y := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct, smul_ofLp, smul_ofLp, dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, so3_transpose_mul, Matrix.one_mulVec]

theorem norm_smul_so3 (M : SO3) (x : E) : ‖M • x‖ = ‖x‖ := by
  have h := inner_smul_smul M x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (M • x), norm_nonneg x]

/-! ### Nonidentity rotations have few fixed points -/

theorem cross_mulVec (N : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    (N *ᵥ u) ⨯₃ (N *ᵥ v) = (N.adjugate)ᵀ *ᵥ (u ⨯₃ v) := by
  funext i
  fin_cases i <;>
    simp [Matrix.adjugate_fin_three, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> ring

theorem adjugate_eq_transpose {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ * N = 1) (hdet : N.det = 1) :
    N.adjugate = Nᵀ := by
  calc N.adjugate = (Nᵀ * N) * N.adjugate := by rw [hN, Matrix.one_mul]
    _ = Nᵀ * (N * N.adjugate) := by rw [Matrix.mul_assoc]
    _ = Nᵀ := by rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]

theorem det_triple (u v : Fin 3 → ℝ) :
    (Matrix.of ![u, v, u ⨯₃ v]).det = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  simp [Matrix.det_fin_three, cross_apply, dotProduct, Fin.sum_univ_three]
  ring

/-- A rotation fixing two vectors with nondegenerate Gram determinant is the identity. -/
theorem so3_eq_one_of_fixed_pair {N : Matrix (Fin 3) (Fin 3) ℝ} (hN : Nᵀ * N = 1)
    (hdet : N.det = 1) {u v : Fin 3 → ℝ}
    (hgram : (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 ≠ 0)
    (hu : N *ᵥ u = u) (hv : N *ᵥ v = v) : N = 1 := by
  set w := u ⨯₃ v with hw
  have hNw : N *ᵥ w = w := by
    have h := cross_mulVec N u v
    rw [hu, hv, adjugate_eq_transpose hN hdet, Matrix.transpose_transpose] at h
    exact h.symm
  set P : Matrix (Fin 3) (Fin 3) ℝ := (Matrix.of ![u, v, w])ᵀ with hP
  have hdetP : P.det ≠ 0 := by
    rw [hP, Matrix.det_transpose, hw, det_triple]
    exact hgram
  have hmul : ∀ (z : Fin 3 → ℝ), N *ᵥ z = z → ∀ i, ∑ k, N i k * z k = z i := by
    intro z hz i
    have := congrFun hz i
    simpa [Matrix.mulVec, dotProduct] using this
  have hNP : N * P = P := by
    ext i j
    fin_cases j <;>
      simp only [Matrix.mul_apply, hP, Matrix.transpose_apply, Matrix.of_apply]
    · simpa using hmul u hu i
    · simpa using hmul v hv i
    · simpa using hmul w hNw i
  have hPunit : IsUnit P.det := isUnit_iff_ne_zero.mpr hdetP
  calc N = N * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one]
    _ = (N * P) * P⁻¹ := by rw [Matrix.mul_assoc]
    _ = P * P⁻¹ := by rw [hNP]
    _ = 1 := Matrix.mul_nonsing_inv P hPunit

/-- Two distinct, non-antipodal unit vectors have nondegenerate Gram determinant. -/
theorem gram_ne_zero {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h1 : u ≠ v) (h2 : u ≠ -v) :
    (u.ofLp ⬝ᵥ u.ofLp) * (v.ofLp ⬝ᵥ v.ofLp) - (u.ofLp ⬝ᵥ v.ofLp) ^ 2 ≠ 0 := by
  have huu : (u.ofLp ⬝ᵥ u.ofLp) = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : (v.ofLp ⬝ᵥ v.ofLp) = 1 := by
    rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq, hv]; norm_num
  rw [huu, hvv, one_mul]
  intro hcon
  set c : ℝ := (inner ℝ u v : ℝ) with hc
  have hcd : c = u.ofLp ⬝ᵥ v.ofLp := inner_eq_dotProduct u v
  have hc2 : c ^ 2 = 1 := by rw [hcd]; linarith
  have hzero : ‖u - c • v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, hu, hv, mul_one, one_pow]
    rw [← hc]
    nlinarith [hc2, sq_abs c]
  have hueq : u = c • v := by
    have hn : ‖u - c • v‖ = 0 := by nlinarith [norm_nonneg (u - c • v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hc2]
  rcases mul_eq_zero.mp hfac with h | h
  · exact h1 (by rw [hueq, show c = 1 by linarith, one_smul])
  · exact h2 (by rw [hueq, show c = -1 by linarith]; module)

/-! ### The unit sphere -/

/-- The unit sphere of `ℝ³`. -/
def sph : Set E := {x : E | ‖x‖ = 1}

theorem smul_mem_sph (M : SO3) {x : E} (hx : x ∈ sph) : M • x ∈ sph := by
  show ‖M • x‖ = 1
  rw [norm_smul_so3]
  exact hx

theorem smul_sph (M : SO3) : M • sph = sph := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact smul_mem_sph M hy
  · intro hx
    refine ⟨M⁻¹ • x, smul_mem_sph M⁻¹ hx, ?_⟩
    show M • (M⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel, one_smul]

/-- A nonidentity rotation fixes at most two points of the sphere. -/
theorem fixed_countable (M : SO3) (hM : M ≠ 1) : {x ∈ sph | M • x = x}.Countable := by
  rcases Set.eq_empty_or_nonempty {x ∈ sph | M • x = x} with h | ⟨u, hu⟩
  · rw [h]; exact Set.countable_empty
  · have hsub : {x ∈ sph | M • x = x} ⊆ {u, -u} := by
      intro v hv
      by_contra hne
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
      apply hM
      have hgram := gram_ne_zero (u := u) (v := v) hu.1 hv.1
        (fun h => hne.1 h.symm) (fun h => hne.2 (by rw [h]; module))
      have hNu : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ u.ofLp = u.ofLp := by
        rw [← smul_ofLp, hu.2]
      have hNv : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.ofLp = v.ofLp := by
        rw [← smul_ofLp, hv.2]
      exact Subtype.ext (so3_eq_one_of_fixed_pair (so3_transpose_mul M) (so3_det M) hgram hNu hNv)
    exact Set.Countable.mono hsub (Set.toFinite _).countable

instance : Countable F2 := FreeGroup.toWord_injective.countable

/-- The countable set of points of the sphere fixed by some nontrivial rotation of our free
group. -/
def badSet : Set E := {x ∈ sph | ∃ w : F2, w ≠ 1 ∧ phi w • x = x}

theorem badSet_subset : badSet ⊆ sph := fun _ hx => hx.1

theorem badSet_countable : badSet.Countable := by
  have hsub : badSet ⊆ ⋃ w : F2, {x ∈ sph | w ≠ 1 ∧ phi w • x = x} := by
    rintro x ⟨hx, w, hw, hwx⟩
    exact Set.mem_iUnion.2 ⟨w, hx, hw, hwx⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun w => ?_)
  by_cases hw : w = 1
  · have : {x ∈ sph | w ≠ 1 ∧ phi w • x = x} = ∅ := by
      ext x; simp [hw]
    rw [this]; exact Set.countable_empty
  · have hne : phi w ≠ 1 := fun h => hw (phi_injective (by rw [h, map_one]))
    refine Set.Countable.mono ?_ (fixed_countable (phi w) hne)
    rintro x ⟨hx, -, hwx⟩
    exact ⟨hx, hwx⟩

theorem sph_diff_bad_invariant (w : F2) {x : E} (hx : x ∈ sph \ badSet) :
    phi w • x ∈ sph \ badSet := by
  refine ⟨smul_mem_sph _ hx.1, ?_⟩
  rintro ⟨-, v, hv, hvx⟩
  refine hx.2 ⟨hx.1, w⁻¹ * v * w, ?_, ?_⟩
  · intro hcon
    apply hv
    have : v = w * w⁻¹ := by
      have := congrArg (fun z => w * z * w⁻¹) hcon
      simpa [mul_assoc] using this
    simpa using this
  · rw [map_mul, map_mul, SemigroupAction.mul_smul, SemigroupAction.mul_smul, hvx, map_inv,
      inv_smul_smul]

theorem sph_diff_bad_free (w : F2) {x : E} (hx : x ∈ sph \ badSet) (h : phi w • x = x) : w = 1 := by
  by_contra hw
  exact hx.2 ⟨hx.1, w, hw, h⟩

theorem isParadoxical_sph_diff_bad : IsParadoxical SO3 (sph \ badSet) :=
  isParadoxical_of_free phi (sph \ badSet) (fun w _ hx => sph_diff_bad_invariant w hx)
    (fun w _ hx h => sph_diff_bad_free w hx h)

/-! ### Rotations about the coordinate axes -/

/-- Rotation by `t` about the `z`-axis. -/
def rotZ (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

/-- Rotation by `t` about the `y`-axis. -/
def rotY (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, 0, Real.sin t; 0, 1, 0; -Real.sin t, 0, Real.cos t]

theorem rotZ_mul_transpose (t : ℝ) : rotZ t * (rotZ t)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotZ_det (t : ℝ) : (rotZ t).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotZ]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotY_mul_transpose (t : ℝ) : rotY t * (rotY t)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotY_det (t : ℝ) : (rotY t).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [rotY]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotZ_mem (t : ℝ) : rotZ t ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr (rotZ_mul_transpose t), rotZ_det t⟩

theorem rotY_mem (t : ℝ) : rotY t ∈ SO3 :=
  ⟨(Matrix.mem_unitaryGroup_iff).mpr (rotY_mul_transpose t), rotY_det t⟩

/-- Rotation about the `z`-axis, as an element of `SO(3)`. -/
def rZ (t : ℝ) : SO3 := ⟨rotZ t, rotZ_mem t⟩

/-- Rotation about the `y`-axis, as an element of `SO(3)`. -/
def rY (t : ℝ) : SO3 := ⟨rotY t, rotY_mem t⟩

theorem rZ_add (s t : ℝ) : rZ (s + t) = rZ s * rZ t := by
  apply Subtype.ext
  show rotZ (s + t) = rotZ s * rotZ t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rZ_zero : rZ 0 = 1 := by
  apply Subtype.ext
  show rotZ 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ]

theorem rZ_pow (t : ℝ) (n : ℕ) : rZ t ^ n = rZ (n * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, rZ_zero]
  | succ m ih =>
      rw [pow_succ, ih, ← rZ_add]
      congr 1
      push_cast
      ring

theorem rZ_smul (t : ℝ) (x : E) (i : Fin 3) :
    (rZ t • x) i = (rotZ t) i 0 * x 0 + (rotZ t) i 1 * x 1 + (rotZ t) i 2 * x 2 := by
  show ∑ j, (rotZ t) i j * x j = _
  rw [Fin.sum_univ_three]

/-- A rotation about the `z`-axis fixing a point off the axis must be trivial. -/
theorem rZ_fix (t : ℝ) (x : E) (hx : x 0 ≠ 0 ∨ x 1 ≠ 0) (h : rZ t • x = x) :
    Real.cos t = 1 ∧ Real.sin t = 0 := by
  have h0 : (rZ t • x) 0 = x 0 := by rw [h]
  have h1 : (rZ t • x) 1 = x 1 := by rw [h]
  rw [rZ_smul] at h0 h1
  simp only [rotZ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.tail_cons] at h0 h1
  have hpos : 0 < x 0 ^ 2 + x 1 ^ 2 := by
    rcases hx with hne | hne
    · have := sq_nonneg (x 1); positivity
    · have := sq_nonneg (x 0); positivity
  constructor
  · have hkey : (Real.cos t - 1) * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
      linear_combination (x 0) * h0 + (x 1) * h1
    have := (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)
    linarith
  · have hkey : Real.sin t * (x 0 ^ 2 + x 1 ^ 2) = 0 := by
      linear_combination (-(x 1)) * h0 + (x 0) * h1
    exact (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)

theorem rZ_inv (t : ℝ) : (rZ t)⁻¹ = rZ (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← rZ_add, add_neg_cancel, rZ_zero]

theorem rY_add (s t : ℝ) : rY (s + t) = rY s * rY t := by
  apply Subtype.ext
  show rotY (s + t) = rotY s * rotY t
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

theorem rY_zero : rY 0 = 1 := by
  apply Subtype.ext
  show rotY 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY]

theorem rY_inv (t : ℝ) : (rY t)⁻¹ = rY (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← rY_add, add_neg_cancel, rY_zero]

theorem rY_smul (t : ℝ) (x : E) (i : Fin 3) :
    (rY t • x) i = (rotY t) i 0 * x 0 + (rotY t) i 1 * x 1 + (rotY t) i 2 * x 2 := by
  show ∑ j, (rotY t) i j * x j = _
  rw [Fin.sum_univ_three]

/-- A rotation about the `y`-axis fixing a point off the axis must be trivial. -/
theorem rY_fix (t : ℝ) (x : E) (hx : x 0 ≠ 0 ∨ x 2 ≠ 0) (h : rY t • x = x) :
    Real.cos t = 1 ∧ Real.sin t = 0 := by
  have h0 : (rY t • x) 0 = x 0 := by rw [h]
  have h2 : (rY t • x) 2 = x 2 := by rw [h]
  rw [rY_smul] at h0 h2
  simp only [rotY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.vecHead] at h0 h2
  have hpos : 0 < x 0 ^ 2 + x 2 ^ 2 := by
    rcases hx with hne | hne
    · have := sq_nonneg (x 2); positivity
    · have := sq_nonneg (x 0); positivity
  constructor
  · have hkey : (Real.cos t - 1) * (x 0 ^ 2 + x 2 ^ 2) = 0 := by
      linear_combination (x 0) * h0 + (x 2) * h2
    have := (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)
    linarith
  · have hkey : Real.sin t * (x 0 ^ 2 + x 2 ^ 2) = 0 := by
      linear_combination (x 2) * h0 - (x 0) * h2
    exact (mul_eq_zero.mp hkey).resolve_right (ne_of_gt hpos)

/-- Points of the sphere off the `z`-axis. -/
theorem off_axis_of_mem_sph {x : E} (hx : x ∈ sph) (h1 : x ≠ EuclideanSpace.single 2 (1 : ℝ))
    (h2 : x ≠ -EuclideanSpace.single 2 (1 : ℝ)) : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx0, hx1⟩ := hcon
  have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_dotProduct]
    simp [dotProduct, Fin.sum_univ_three]
    ring
  have h1' : ‖x‖ = 1 := hx
  have hsq : x 2 ^ 2 = 1 := by rw [h1', hx0, hx1] at hnorm; nlinarith
  have : x 2 = 1 ∨ x 2 = -1 := by
    rcases mul_eq_zero.mp (show (x 2 - 1) * (x 2 + 1) = 0 by nlinarith) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases this with h | h
  · exact h1 (by ext i; fin_cases i <;>
      simp [EuclideanSpace.single_apply, hx0, hx1, h])
  · exact h2 (by ext i; fin_cases i <;>
      simp [EuclideanSpace.single_apply, hx0, hx1, h])

end

end BT

/-
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Pointwise

namespace Frontier

/-- **The Banach–Tarski paradox.**

The closed unit ball `B` of `ℝ³` admits a paradoxical decomposition: there are two disjoint
subsets `P, Q ⊆ B`, each of which is equidecomposable with the whole ball `B` using finitely
many pieces moved by isometries of `ℝ³`.

Here `BT.Equidec G A B` says that there is a finite decomposition of `A` into pieces which,
after applying to each piece a single element of the group `G`, reassemble exactly into `B`
(this is Mathlib's `Equidecomp`), and `G` is the full isometry group
`EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3)`. -/
theorem Banach_Tarski :
    ∃ P Q : Set (EuclideanSpace ℝ (Fin 3)),
      P ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∧
      Q ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∧
      Disjoint P Q ∧
      BT.Equidec (EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) P ∧
      BT.Equidec (EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) Q :=
  BT.isParadoxical_ball

end Frontier


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

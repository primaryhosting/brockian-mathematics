/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## Arrow's impossibility theorem

For a finite electorate `ι` and a set of alternatives `A` containing at least three elements,
there is no social welfare function `F : (ι → Pref A) → Pref A` that is simultaneously
unanimous (Pareto efficient), independent of irrelevant alternatives (IIA), and
non-dictatorial.

Individual and social preferences are modelled as strict linear orders (`Pref`), i.e.
transitive, irreflexive and total relations, `P.gt x y` meaning "`x` is strictly preferred
to `y`".

The proof is the classical "decisive coalition" argument:

* a coalition `S` is *weakly decisive* for the ordered pair `(x, y)` if whenever the members of
  `S` prefer `x` to `y` and everybody else prefers `y` to `x`, society prefers `x` to `y`;
* a coalition `S` is *decisive* if whenever all of its members prefer `x` to `y`, so does
  society;
* (field expansion) weak decisiveness for a single pair implies full decisiveness;
* (group contraction) if a decisive coalition splits into two disjoint pieces, one of the pieces
  is decisive;
* the whole electorate is decisive and the empty coalition is not, so by induction along a list
  enumerating the electorate some singleton coalition `{i}` is decisive — and `i` is then a
  dictator.

This file is deliberately self-contained: it depends on nothing but the Lean 4 core library.
-/

universe u v

namespace Frontier

/-- A strict preference relation on `A`: a transitive, irreflexive and total relation.
`P.gt x y` means "`x` is strictly preferred to `y`". -/
structure Pref (A : Type v) where
  /-- `gt x y` means that `x` is strictly preferred to `y`. -/
  gt : A → A → Prop
  /-- Preference is transitive. -/
  gt_trans : ∀ {x y z}, gt x y → gt y z → gt x z
  /-- Preference is irreflexive. -/
  gt_irrefl : ∀ x, ¬ gt x x
  /-- Preference is total: distinct alternatives are always comparable. -/
  gt_total : ∀ {x y}, x ≠ y → gt x y ∨ gt y x

namespace Pref

variable {A : Type v}

theorem asymm (P : Pref A) {x y : A} (h : P.gt x y) : ¬ P.gt y x :=
  fun h' => P.gt_irrefl x (P.gt_trans h h')

theorem ne_of_gt (P : Pref A) {x y : A} (h : P.gt x y) : x ≠ y := by
  intro hxy
  exact P.gt_irrefl x (hxy ▸ h)

/-- The preference `P` modified by moving the alternative `w` to the top. -/
def top (P : Pref A) (w : A) : Pref A where
  gt x y := (x = w ∧ y ≠ w) ∨ (y ≠ w ∧ P.gt x y)
  gt_trans := by
    rintro x y z (⟨rfl, hy⟩ | ⟨hy, hxy⟩) (⟨rfl, hz⟩ | ⟨hz, hyz⟩)
    · exact absurd rfl hy
    · exact Or.inl ⟨rfl, hz⟩
    · exact absurd rfl hy
    · exact Or.inr ⟨hz, P.gt_trans hxy hyz⟩
  gt_irrefl := by
    rintro x (⟨rfl, h⟩ | ⟨-, h⟩)
    · exact h rfl
    · exact P.gt_irrefl x h
  gt_total := by
    intro x y hxy
    by_cases hx : x = w
    · exact Or.inl (Or.inl ⟨hx, fun h => hxy (hx.trans h.symm)⟩)
    · by_cases hy : y = w
      · exact Or.inr (Or.inl ⟨hy, hx⟩)
      · rcases P.gt_total hxy with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)

theorem top_gt_top (P : Pref A) {w y : A} (h : y ≠ w) : (P.top w).gt w y := Or.inl ⟨rfl, h⟩

theorem top_gt_iff (P : Pref A) {w x y : A} (hx : x ≠ w) (hy : y ≠ w) :
    (P.top w).gt x y ↔ P.gt x y := by
  constructor
  · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
    · exact absurd rfl hx
    · exact h
  · intro h
    exact Or.inr ⟨hy, h⟩

/-- `P` if the proposition `c` holds, and `Q` otherwise. (A decidability-free `ite`.) -/
def byProp (c : Prop) (P Q : Pref A) : Pref A where
  gt x y := (c ∧ P.gt x y) ∨ (¬ c ∧ Q.gt x y)
  gt_trans := by
    rintro x y z (⟨hc, h1⟩ | ⟨hc, h1⟩) (⟨hc', h2⟩ | ⟨hc', h2⟩)
    · exact Or.inl ⟨hc, P.gt_trans h1 h2⟩
    · exact absurd hc hc'
    · exact absurd hc' hc
    · exact Or.inr ⟨hc, Q.gt_trans h1 h2⟩
  gt_irrefl := by
    rintro x (⟨-, h⟩ | ⟨-, h⟩)
    · exact P.gt_irrefl x h
    · exact Q.gt_irrefl x h
  gt_total := by
    intro x y hxy
    by_cases hc : c
    · rcases P.gt_total hxy with h | h
      · exact Or.inl (Or.inl ⟨hc, h⟩)
      · exact Or.inr (Or.inl ⟨hc, h⟩)
    · rcases Q.gt_total hxy with h | h
      · exact Or.inl (Or.inr ⟨hc, h⟩)
      · exact Or.inr (Or.inr ⟨hc, h⟩)

theorem byProp_pos {c : Prop} {P Q : Pref A} (hc : c) {x y : A} :
    (byProp c P Q).gt x y ↔ P.gt x y := by
  constructor
  · rintro (⟨-, h⟩ | ⟨hc', -⟩)
    · exact h
    · exact absurd hc hc'
  · intro h
    exact Or.inl ⟨hc, h⟩

theorem byProp_neg {c : Prop} {P Q : Pref A} (hc : ¬ c) {x y : A} :
    (byProp c P Q).gt x y ↔ Q.gt x y := by
  constructor
  · rintro (⟨hc', -⟩ | ⟨-, h⟩)
    · exact absurd hc' hc
    · exact h
  · intro h
    exact Or.inr ⟨hc, h⟩

end Pref

variable {A : Type v}

/-- The preference ranking `x` first, `y` second, `z` third, and everything else as in
`base`. -/
def three (x y z : A) (base : Pref A) : Pref A := ((base.top z).top y).top x

theorem three_gt_fst_snd (base : Pref A) {x y z : A} (hyx : y ≠ x) :
    (three x y z base).gt x y :=
  Pref.top_gt_top _ hyx

theorem three_gt_fst_thd (base : Pref A) {x y z : A} (hzx : z ≠ x) :
    (three x y z base).gt x z :=
  Pref.top_gt_top _ hzx

theorem three_gt_snd_thd (base : Pref A) {x y z : A} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) :
    (three x y z base).gt y z :=
  (Pref.top_gt_iff _ hyx hzx).mpr (Pref.top_gt_top _ hzy)

variable {ι : Type u}

/-- Unanimity (Pareto efficiency): if everybody strictly prefers `x` to `y`, so does society. -/
def Unanimous (F : (ι → Pref A) → Pref A) : Prop :=
  ∀ (p : ι → Pref A) (x y : A), (∀ i, (p i).gt x y) → (F p).gt x y

/-- Independence of irrelevant alternatives: the social ranking of `x` against `y` depends only
on the individual rankings of `x` against `y`. -/
def IIA (F : (ι → Pref A) → Pref A) : Prop :=
  ∀ (p q : ι → Pref A) (x y : A), (∀ i, ((p i).gt x y ↔ (q i).gt x y)) →
    ((F p).gt x y ↔ (F q).gt x y)

/-- `i` is a dictator: society always follows `i`'s strict preferences. -/
def IsDictator (F : (ι → Pref A) → Pref A) (i : ι) : Prop :=
  ∀ (p : ι → Pref A) (x y : A), (p i).gt x y → (F p).gt x y

/-- The coalition `S` is decisive: whenever all of its members prefer `x` to `y`, so does
society. -/
def Decisive (F : (ι → Pref A) → Pref A) (S : ι → Prop) : Prop :=
  ∀ (p : ι → Pref A) (x y : A), x ≠ y → (∀ i, S i → (p i).gt x y) → (F p).gt x y

/-- The coalition `S` is weakly decisive for the ordered pair `(x, y)`: whenever its members
prefer `x` to `y` and everybody else prefers `y` to `x`, society prefers `x` to `y`. -/
def WeaklyDecisive (F : (ι → Pref A) → Pref A) (S : ι → Prop) (x y : A) : Prop :=
  ∀ (p : ι → Pref A), (∀ i, S i → (p i).gt x y) → (∀ i, ¬ S i → (p i).gt y x) → (F p).gt x y

section Arrow

variable {F : (ι → Pref A) → Pref A}

/-- A single witnessing profile suffices to establish weak decisiveness (by IIA). -/
theorem weaklyDecisive_of_witness (hI : IIA F) {S : ι → Prop} {x y : A} (q : ι → Pref A)
    (hS : ∀ i, S i → (q i).gt x y) (hSc : ∀ i, ¬ S i → (q i).gt y x) (hq : (F q).gt x y) :
    WeaklyDecisive F S x y := by
  intro p hpS hpSc
  refine (hI p q x y ?_).mpr hq
  intro i
  by_cases hi : S i
  · exact ⟨fun _ => hS i hi, fun _ => hpS i hi⟩
  · exact ⟨fun h => absurd h ((p i).asymm (hpSc i hi)),
      fun h => absurd h ((q i).asymm (hSc i hi))⟩

/-- Field expansion, step 1: shifting the second coordinate of a weakly decisive pair. -/
theorem weaklyDecisive_shift_right (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    {S : ι → Prop} {x y z : A} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y)
    (h : WeaklyDecisive F S x y) : WeaklyDecisive F S x z := by
  -- members of `S` rank `x ≻ y ≻ z`, everybody else ranks `y ≻ z ≻ x`
  let P1 : Pref A := three x y z base
  let P2 : Pref A := three y z x base
  let q : ι → Pref A := fun i => Pref.byProp (S i) P1 P2
  have hxy : (F q).gt x y := by
    refine h q (fun i hi => ?_) (fun i hi => ?_)
    · exact (Pref.byProp_pos hi).mpr (three_gt_fst_snd base hyx)
    · exact (Pref.byProp_neg hi).mpr (three_gt_fst_thd base hyx.symm)
  have hyz : (F q).gt y z := by
    refine hU q y z (fun i => ?_)
    by_cases hi : S i
    · exact (Pref.byProp_pos hi).mpr (three_gt_snd_thd base hyx hzx hzy)
    · exact (Pref.byProp_neg hi).mpr (three_gt_fst_snd base hzy)
  refine weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) ((F q).gt_trans hxy hyz)
  · exact (Pref.byProp_pos hi).mpr (three_gt_fst_thd base hzx)
  · exact (Pref.byProp_neg hi).mpr (three_gt_snd_thd base hzy hyx.symm hzx.symm)

/-- Field expansion, step 2: shifting the first coordinate of a weakly decisive pair. -/
theorem weaklyDecisive_shift_left (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    {S : ι → Prop} {x y z : A} (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y)
    (h : WeaklyDecisive F S x y) : WeaklyDecisive F S z y := by
  -- members of `S` rank `z ≻ x ≻ y`, everybody else ranks `y ≻ z ≻ x`
  let P1 : Pref A := three z x y base
  let P2 : Pref A := three y z x base
  let q : ι → Pref A := fun i => Pref.byProp (S i) P1 P2
  have hxy : (F q).gt x y := by
    refine h q (fun i hi => ?_) (fun i hi => ?_)
    · exact (Pref.byProp_pos hi).mpr (three_gt_snd_thd base hzx.symm hzy.symm hyx)
    · exact (Pref.byProp_neg hi).mpr (three_gt_fst_thd base hyx.symm)
  have hzx' : (F q).gt z x := by
    refine hU q z x (fun i => ?_)
    by_cases hi : S i
    · exact (Pref.byProp_pos hi).mpr (three_gt_fst_snd base hzx.symm)
    · exact (Pref.byProp_neg hi).mpr (three_gt_snd_thd base hzy hyx.symm hzx.symm)
  refine weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_)
    ((F q).gt_trans hzx' hxy)
  · exact (Pref.byProp_pos hi).mpr (three_gt_fst_thd base hzy.symm)
  · exact (Pref.byProp_neg hi).mpr (three_gt_fst_snd base hzy)

/-- Field expansion: weak decisiveness for a single pair yields weak decisiveness for every
pair. -/
theorem weaklyDecisive_all (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {S : ι → Prop} {x y : A} (hxy : x ≠ y)
    (h : WeaklyDecisive F S x y) : ∀ u v : A, u ≠ v → WeaklyDecisive F S u v := by
  intro u v huv
  -- Step A: obtain weak decisiveness for `(u, w)` for some `w ≠ u`.
  obtain ⟨w, hwu, hw⟩ : ∃ w : A, w ≠ u ∧ WeaklyDecisive F S u w := by
    by_cases hux : u = x
    · subst hux
      exact ⟨y, hxy.symm, h⟩
    · by_cases huy : u = y
      · subst huy
        obtain ⟨t, htx, htu⟩ := hthird x u
        have h1 : WeaklyDecisive F S x t :=
          weaklyDecisive_shift_right base hU hI hxy.symm htx htu h
        exact ⟨t, htu, weaklyDecisive_shift_left base hU hI htx hux htu.symm h1⟩
      · exact ⟨y, fun hc => huy hc.symm,
          weaklyDecisive_shift_left base hU hI hxy.symm hux huy h⟩
  -- Step B: shift the second coordinate to `v`.
  by_cases hvw : v = w
  · subst hvw
    exact hw
  · exact weaklyDecisive_shift_right base hU hI hwu (Ne.symm huv) hvw hw

/-- Weak decisiveness for a single pair implies full decisiveness. -/
theorem decisive_of_weaklyDecisive (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {S : ι → Prop} {x y : A} (hxy : x ≠ y)
    (h : WeaklyDecisive F S x y) : Decisive F S := by
  have hall := weaklyDecisive_all base hU hI hthird hxy h
  intro p u v huv hp
  obtain ⟨w, hwu, hwv⟩ := hthird u v
  -- members of `S` rank `u ≻ w ≻ v`; everybody else keeps their preference but moves `w` on top
  let q : ι → Pref A := fun i => Pref.byProp (S i) (three u w v (p i)) ((p i).top w)
  have huw : (F q).gt u w := by
    refine hall u w (Ne.symm hwu) q (fun i hi => ?_) (fun i hi => ?_)
    · exact (Pref.byProp_pos hi).mpr (three_gt_fst_snd (p i) hwu)
    · exact (Pref.byProp_neg hi).mpr ((p i).top_gt_top (Ne.symm hwu))
  have hwv' : (F q).gt w v := by
    refine hU q w v (fun i => ?_)
    by_cases hi : S i
    · exact (Pref.byProp_pos hi).mpr
        (three_gt_snd_thd (p i) hwu (Ne.symm huv) (Ne.symm hwv))
    · exact (Pref.byProp_neg hi).mpr ((p i).top_gt_top (Ne.symm hwv))
  refine (hI p q u v ?_).mpr ((F q).gt_trans huw hwv')
  intro i
  by_cases hi : S i
  · exact ⟨fun _ => (Pref.byProp_pos hi).mpr (three_gt_fst_thd (p i) (Ne.symm huv)),
      fun _ => hp i hi⟩
  · exact ((Pref.byProp_neg hi).trans ((p i).top_gt_iff (Ne.symm hwu) (Ne.symm hwv))).symm

/-- The whole electorate is decisive. -/
theorem decisive_univ (hU : Unanimous F) : Decisive F (fun _ => True) :=
  fun p x y _ hp => hU p x y (fun i => hp i trivial)

/-- Decisiveness is inherited by larger coalitions. -/
theorem decisive_mono {S T : ι → Prop} (hST : ∀ i, S i → T i) (h : Decisive F S) :
    Decisive F T :=
  fun p x y hxy hp => h p x y hxy (fun i hi => hp i (hST i hi))

/-- A coalition with no members is not decisive. -/
theorem not_decisive_of_isEmpty (base : Pref A) {x y : A} (hxy : x ≠ y) {S : ι → Prop}
    (hS : ∀ i, ¬ S i) : ¬ Decisive F S := by
  intro h
  have h1 : (F (fun _ => base)).gt x y :=
    h (fun _ => base) x y hxy (fun i hi => absurd hi (hS i))
  have h2 : (F (fun _ => base)).gt y x :=
    h (fun _ => base) y x hxy.symm (fun i hi => absurd hi (hS i))
  exact (F (fun _ => base)).asymm h1 h2

/-- Group contraction: if a decisive coalition splits into two disjoint pieces, then one of the
pieces is decisive. -/
theorem decisive_split (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S S₁ S₂ : ι → Prop} (hS : ∀ i, S i ↔ (S₁ i ∨ S₂ i)) (hdisj : ∀ i, ¬ (S₁ i ∧ S₂ i))
    (hdec : Decisive F S) : Decisive F S₁ ∨ Decisive F S₂ := by
  -- `S₁` ranks `a ≻ b ≻ c`, `S₂` ranks `b ≻ c ≻ a`, everybody else ranks `c ≻ a ≻ b`
  let P1 : Pref A := three a b c base
  let P2 : Pref A := three b c a base
  let P3 : Pref A := three c a b base
  let q : ι → Pref A := fun i => Pref.byProp (S₁ i) P1 (Pref.byProp (S₂ i) P2 P3)
  have hq1 : ∀ i, S₁ i → ∀ {x y : A}, ((q i).gt x y ↔ P1.gt x y) :=
    fun i hi => Pref.byProp_pos hi
  have hq2 : ∀ i, S₂ i → ∀ {x y : A}, ((q i).gt x y ↔ P2.gt x y) := by
    intro i hi x y
    have hi1 : ¬ S₁ i := fun h => hdisj i ⟨h, hi⟩
    exact (Pref.byProp_neg hi1).trans (Pref.byProp_pos hi)
  have hq3 : ∀ i, ¬ S i → ∀ {x y : A}, ((q i).gt x y ↔ P3.gt x y) := by
    intro i hi x y
    have hi1 : ¬ S₁ i := fun h => hi ((hS i).mpr (Or.inl h))
    have hi2 : ¬ S₂ i := fun h => hi ((hS i).mpr (Or.inr h))
    exact (Pref.byProp_neg hi1).trans (Pref.byProp_neg hi2)
  -- society prefers `b` to `c`, since the decisive coalition `S` does
  have hbc' : (F q).gt b c := by
    refine hdec q b c hbc (fun i hi => ?_)
    rcases (hS i).mp hi with h1 | h2
    · exact (hq1 i h1).mpr (three_gt_snd_thd base hab.symm hac.symm hbc.symm)
    · exact (hq2 i h2).mpr (three_gt_fst_snd base hbc.symm)
  rcases (F q).gt_total hac with hf | hf
  · -- society prefers `a` to `c`, and only `S₁` does
    left
    refine decisive_of_weaklyDecisive base hU hI hthird hac
      (weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) hf)
    · exact (hq1 i hi).mpr (three_gt_fst_thd base hac.symm)
    · by_cases hiS : S i
      · have h2 : S₂ i := by
          rcases (hS i).mp hiS with h | h
          · exact absurd h hi
          · exact h
        exact (hq2 i h2).mpr (three_gt_snd_thd base hbc.symm hab hac)
      · exact (hq3 i hiS).mpr (three_gt_fst_snd base hac)
  · -- society prefers `c` to `a`, hence `b` to `a`, and only `S₂` prefers `b` to `a`
    right
    have hba : (F q).gt b a := (F q).gt_trans hbc' hf
    refine decisive_of_weaklyDecisive base hU hI hthird hab.symm
      (weaklyDecisive_of_witness hI q (fun i hi => ?_) (fun i hi => ?_) hba)
    · exact (hq2 i hi).mpr (three_gt_fst_thd base hab)
    · by_cases hiS : S i
      · have h1 : S₁ i := by
          rcases (hS i).mp hiS with h | h
          · exact h
          · exact absurd h hi
        exact (hq1 i h1).mpr (three_gt_fst_snd base hab.symm)
      · exact (hq3 i hiS).mpr (three_gt_snd_thd base hac hbc hab.symm)

/-- Induction along a list enumerating the electorate: every decisive coalition contained in the
list contains a decisive singleton. -/
theorem exists_decisive_singleton (base : Pref A) (hU : Unanimous F) (hI : IIA F)
    (hthird : ∀ x y : A, ∃ t : A, t ≠ x ∧ t ≠ y) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (l : List ι) (S : ι → Prop), (∀ i, S i → i ∈ l) → Decisive F S →
      ∃ i : ι, Decisive F (fun j => j = i) := by
  intro l
  induction l with
  | nil =>
    intro S hsub hdec
    exact absurd hdec (not_decisive_of_isEmpty base hab (fun i hi => by
      cases hsub i hi))
  | cons a' t ih =>
    intro S hsub hdec
    have hsplit := decisive_split base hU hI hthird hab hac hbc
      (S := S) (S₁ := fun i => S i ∧ i = a') (S₂ := fun i => S i ∧ i ≠ a')
      (fun i => by
        constructor
        · intro hi
          by_cases h : i = a'
          · exact Or.inl ⟨hi, h⟩
          · exact Or.inr ⟨hi, h⟩
        · rintro (⟨hi, -⟩ | ⟨hi, -⟩) <;> exact hi)
      (fun i hi => hi.2.2 hi.1.2) hdec
    rcases hsplit with h1 | h2
    · exact ⟨a', decisive_mono (fun i hi => hi.2) h1⟩
    · refine ih (fun i => S i ∧ i ≠ a') (fun i hi => ?_) h2
      rcases List.mem_cons.mp (hsub i hi.1) with h | h
      · exact absurd h hi.2
      · exact h

/-- With at least three alternatives, for every pair of alternatives there is a third one
distinct from both. -/
theorem exists_third {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x y : A) :
    ∃ t : A, t ≠ x ∧ t ≠ y := by
  by_cases hax : a = x
  · by_cases hby : b = y
    · exact ⟨c, fun h => hac (hax.trans h.symm), fun h => hbc (hby.trans h.symm)⟩
    · by_cases hbx : b = x
      · exact absurd (hax.trans hbx.symm) hab
      · exact ⟨b, hbx, hby⟩
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · exact ⟨c, fun h => hbc (hbx.trans h.symm), fun h => hac (hay.trans h.symm)⟩
      · exact ⟨b, hbx, fun h => hab (h.trans hay.symm).symm⟩
    · exact ⟨a, hax, hay⟩

/-- **Arrow's theorem** (positive form): with at least three alternatives and a finite
electorate, unanimity together with independence of irrelevant alternatives forces the existence
of a dictator. -/
theorem exists_dictator (hfin : ∃ l : List ι, ∀ i : ι, i ∈ l) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hU : Unanimous F) (hI : IIA F) :
    ∃ i : ι, IsDictator F i := by
  by_cases hP : Nonempty (Pref A)
  · obtain ⟨base⟩ := hP
    obtain ⟨l, hl⟩ := hfin
    obtain ⟨i, hi⟩ := exists_decisive_singleton base hU hI (exists_third hab hac hbc)
      hab hac hbc l (fun _ => True) (fun i _ => hl i) (decisive_univ hU)
    refine ⟨i, fun p x y hxy => hi p x y ((p i).ne_of_gt hxy) (fun j hj => ?_)⟩
    subst hj
    exact hxy
  · -- there is no preference at all on `A`, hence no profile
    by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι
      exact ⟨i, fun p _ _ _ => absurd ⟨p i⟩ hP⟩
    · exfalso
      have hemp : ∀ i : ι, False := fun i => hι ⟨i⟩
      let p : ι → Pref A := fun i => (hemp i).elim
      exact (F p).asymm (hU p a b (fun i => (hemp i).elim))
        (hU p b a (fun i => (hemp i).elim))

/-- **Arrow's impossibility theorem**: for a finite electorate and at least three alternatives,
no social welfare function is simultaneously unanimous, independent of irrelevant alternatives
and non-dictatorial. -/
theorem arrow_impossibility (hfin : ∃ l : List ι, ∀ i : ι, i ∈ l) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ ∃ F : (ι → Pref A) → Pref A, Unanimous F ∧ IIA F ∧ ∀ i : ι, ¬ IsDictator F i := by
  rintro ⟨F, hU, hI, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator hfin hab hac hbc hU hI
  exact hnd i hi

/-- Sanity check (non-vacuity of the axioms): a dictatorship *does* satisfy unanimity and
independence of irrelevant alternatives.  So the content of Arrow's theorem is exactly that
non-dictatorship is the property that has to fail. -/
theorem dictatorship_unanimous_iia (i₀ : ι) :
    Unanimous (A := A) (fun p => p i₀) ∧ IIA (A := A) (fun p => p i₀) ∧
      IsDictator (A := A) (fun p => p i₀) i₀ :=
  ⟨fun _ _ _ hp => hp i₀, fun _ _ _ _ h => h i₀, fun _ _ _ h => h⟩

end Arrow

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


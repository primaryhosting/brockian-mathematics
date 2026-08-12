import Mathlib
-- (Lean 4 requires `import` lines to precede any module docstring, so the requested
-- header comment appears immediately below the import.)

/-!
# Four Color Statement
Category: Frontier — Moonshot
Target: Frontier.four_color_statement
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

set_option grind.warning false

namespace Frontier

open SimpleGraph

/-! ## Planarity

We use the *straight-line* notion of planarity: a graph is planar when its vertices can be
placed at distinct points of the plane `ℝ × ℝ` in such a way that the closed segments
representing the edges meet only in common endpoints, and no vertex lies on a segment
representing an edge that is not incident to it.

By Fáry's theorem this is equivalent, for finite simple graphs, to the usual topological
notion of planarity (embeddability of the graph into the plane with arbitrary arcs as edges).
-/

/-- A straight-line planar drawing of `G`: an injective placement `p` of the vertices in the
plane such that (i) a vertex lying on the segment of an edge is an endpoint of that edge, and
(ii) the segments of two distinct edges meet only in common endpoints. -/
def IsPlanarDrawing {V : Type*} (G : SimpleGraph V) (p : V → ℝ × ℝ) : Prop :=
  Function.Injective p ∧
  (∀ ⦃a b : V⦄, G.Adj a b → ∀ v : V, p v ∈ segment ℝ (p a) (p b) → v = a ∨ v = b) ∧
  (∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj c d → s(a, b) ≠ s(c, d) →
    ∀ x ∈ segment ℝ (p a) (p b) ∩ segment ℝ (p c) (p d), x ∈ p '' ({a, b} ∩ {c, d} : Set V))

/-- A graph is planar if it admits a straight-line planar drawing. -/
def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → ℝ × ℝ, IsPlanarDrawing G p

/-- Planarity is inherited by subgraphs on the same vertex set. -/
theorem IsPlanar.mono {V : Type*} {G G' : SimpleGraph V} (hle : G' ≤ G) (h : IsPlanar G) :
    IsPlanar G' := by
  obtain ⟨p, hinj, hvert, hedge⟩ := h
  exact ⟨p, hinj, fun a b hab v hv => hvert (hle hab) v hv,
    fun a b c d hab hcd hne x hx => hedge (hle hab) (hle hcd) hne x hx⟩

/-- Planarity is inherited by induced subgraphs. -/
theorem IsPlanar.induce {V : Type*} {G : SimpleGraph V} (s : Set V) (h : IsPlanar G) :
    IsPlanar (G.induce s) := by
  obtain ⟨p, hinj, hvert, hedge⟩ := h
  refine ⟨fun v => p v.1, hinj.comp Subtype.val_injective, ?_, ?_⟩
  · intro a b hab v hv
    rcases hvert hab v.1 hv with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro a b c d hab hcd hne x hx
    have hne' : s(a.1, b.1) ≠ s(c.1, d.1) := by
      intro hcontra
      exact hne (by
        rw [Sym2.eq_iff] at hcontra ⊢
        rcases hcontra with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
    obtain ⟨y, hy, rfl⟩ := hedge hab hcd hne' x hx
    obtain ⟨hy1, hy2⟩ := hy
    have hys : y ∈ s := by
      rcases hy1 with rfl | rfl
      · exact a.2
      · exact b.2
    refine ⟨⟨y, hys⟩, ⟨?_, ?_⟩, rfl⟩
    · rcases hy1 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rcases hy2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)

/-! ## The statement of the Four Colour Theorem -/

/-- The Four Colour Theorem: every planar graph is 4-colourable. -/
def FourColourTheorem.{u} : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-- The Four Colour Theorem for finite graphs. -/
def FiniteFourColourTheorem.{u} : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), IsPlanar G → G.Colorable 4

/-! ## Unconditional partial results -/

/-- Greedy colouring: if every nonempty finite set of vertices contains a vertex with fewer
than `n` neighbours inside that set (`n`-degeneracy), then the graph is `n`-colourable. -/
theorem colorable_of_degenerate {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ)
    (h : ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (fun w => G.Adj v w)).card < n) :
    G.Colorable n := by
  have key : ∀ s : Finset V, ∃ f : V → ℕ, (∀ v ∈ s, f v < n) ∧
      ∀ a ∈ s, ∀ b ∈ s, G.Adj a b → f a ≠ f b := by
    intro s
    induction s using Finset.strongInduction with
    | _ s ih =>
      rcases s.eq_empty_or_nonempty with rfl | hs
      · exact ⟨fun _ => 0, by simp, by simp⟩
      obtain ⟨v, hv, hvcard⟩ := h s hs
      obtain ⟨f, hfb, hfp⟩ := ih (s.erase v) (Finset.erase_ssubset hv)
      set N : Finset V := s.filter (fun w => G.Adj v w) with hN
      have hlt : (N.image f).card < n := lt_of_le_of_lt (Finset.card_image_le) hvcard
      have hex : ∃ c ∈ Finset.range n, c ∉ N.image f := by
        by_contra hcon
        push_neg at hcon
        have : (Finset.range n).card ≤ (N.image f).card :=
          Finset.card_le_card (fun x hx => hcon x hx)
        simp only [Finset.card_range] at this
        omega
      obtain ⟨c, hcn, hcnot⟩ := hex
      rw [Finset.mem_range] at hcn
      refine ⟨Function.update f v c, ?_, ?_⟩
      · intro x hx
        by_cases hxv : x = v
        · subst hxv
          rw [Function.update_self]
          exact hcn
        · rw [Function.update_of_ne hxv]
          exact hfb x (Finset.mem_erase.2 ⟨hxv, hx⟩)
      · intro a ha b hb hab
        have hne : a ≠ b := hab.ne
        by_cases hav : a = v
        · subst hav
          have hbv : b ≠ a := hne.symm
          rw [Function.update_of_ne hbv, Function.update_self]
          intro hcontra
          exact hcnot (Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨hb, hab⟩, hcontra.symm⟩)
        · by_cases hbv : b = v
          · subst hbv
            rw [Function.update_of_ne hav, Function.update_self]
            intro hcontra
            exact hcnot (Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hab.symm⟩, hcontra⟩)
          · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
            exact hfp a (Finset.mem_erase.2 ⟨hav, ha⟩) b (Finset.mem_erase.2 ⟨hbv, hb⟩) hab
  obtain ⟨f, hfb, hfp⟩ := key Finset.univ
  rw [SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab =>
    hfp a (Finset.mem_univ a) b (Finset.mem_univ b) hab, fun v => hfb v (Finset.mem_univ v)⟩

/-- Base case: any graph on at most four vertices is 4-colourable, in particular any such
planar graph. -/
theorem colorable_four_of_card_le_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 4) : G.Colorable 4 :=
  (G.colorable_of_fintype).mono hcard

/-- Any graph of maximum degree at most three is 4-colourable; in particular the Four Colour
Theorem holds unconditionally for planar graphs of maximum degree at most three. -/
theorem colorable_four_of_maxDegree_le_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v : V, G.degree v ≤ 3) :
    G.Colorable 4 := by
  refine colorable_of_degenerate G 4 ?_
  rintro s ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  have hsub : s.filter (fun w => G.Adj v w) ⊆ G.neighborFinset v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact (SimpleGraph.mem_neighborFinset G v w).2 hw.2
  have := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree] at this
  have := hdeg v
  omega

/-- Removing a vertex of degree at most three: this is the standard first reduction in the
proof of the Four Colour Theorem (a minimal counterexample has minimum degree at least
four).  If `G` minus the vertex `v` is 4-colourable and `v` has at most three neighbours,
then `G` itself is 4-colourable. -/
theorem colorable_four_of_removeVertex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (hdeg : G.degree v ≤ 3)
    (h : (G.induce {w : V | w ≠ v}).Colorable 4) : G.Colorable 4 := by
  classical
  obtain ⟨C⟩ := h
  set T : Finset (Fin 4) :=
    (G.neighborFinset v).image (fun w => if hw : w ≠ v then C ⟨w, hw⟩ else 0) with hT
  have hTcard : T.card < 4 := by
    have h1 : T.card ≤ (G.neighborFinset v).card := Finset.card_image_le
    rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hex : ∃ c : Fin 4, c ∉ T := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin 4)).card ≤ T.card :=
      Finset.card_le_card (fun x _ => hcon x)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨SimpleGraph.Coloring.mk (fun w => if hw : w ≠ v then C ⟨w, hw⟩ else c) ?_⟩
  intro a b hab
  have hmemT : ∀ w : V, G.Adj v w → (if hw : w ≠ v then C ⟨w, hw⟩ else (0 : Fin 4)) ∈ T := by
    intro w hw
    exact Finset.mem_image.2 ⟨w, (SimpleGraph.mem_neighborFinset G v w).2 hw, rfl⟩
  by_cases hav : a = v
  · subst hav
    have hb : b ≠ a := hab.ne'
    have hmem := hmemT b hab
    simp only [dif_neg (by simp : ¬(a ≠ a)), dif_pos hb]
    intro hcontra
    rw [dif_pos hb] at hmem
    exact hc (hcontra ▸ hmem)
  · by_cases hbv : b = v
    · subst hbv
      have ha : a ≠ b := hab.ne
      have hmem := hmemT a hab.symm
      simp only [dif_neg (by simp : ¬(b ≠ b)), dif_pos ha]
      intro hcontra
      rw [dif_pos ha] at hmem
      exact hc (hcontra ▸ hmem)
    · simp only [dif_pos hav, dif_pos hbv]
      exact C.valid (show (G.induce {w : V | w ≠ v}).Adj ⟨a, hav⟩ ⟨b, hbv⟩ from hab)

/-! ## Nonvacuity of the planarity predicate -/

/-- Any edgeless graph whose vertices can be placed at distinct points of the plane is
planar. -/
theorem isPlanar_bot_of_injective {V : Type*} (p : V → ℝ × ℝ) (hp : Function.Injective p) :
    IsPlanar (⊥ : SimpleGraph V) :=
  ⟨p, hp, by rintro a b ⟨⟩, by rintro a b c d ⟨⟩⟩

/-- The edgeless graph on `Fin n` is planar. -/
theorem isPlanar_bot_fin (n : ℕ) : IsPlanar (⊥ : SimpleGraph (Fin n)) := by
  refine isPlanar_bot_of_injective (fun i => ((i : ℝ), 0)) ?_
  intro a b hab
  have : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := congrArg Prod.fst hab
  exact Fin.val_injective (Nat.cast_injective this)

/-- A graph with an edge can be planar: the complete graph on two vertices is planar. -/
theorem isPlanar_top_fin_two : IsPlanar (⊤ : SimpleGraph (Fin 2)) := by
  refine ⟨![((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))], ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro a b hab v _
    have key : ∀ a b v : Fin 2, a ≠ b → v = a ∨ v = b := by decide
    exact key a b v hab.ne
  · intro a b c d hab hcd hne x _
    have key : ∀ a b c d : Fin 2, a ≠ b → c ≠ d → s(a, b) = s(c, d) := by decide
    exact absurd (key a b c d hab.ne hcd.ne) hne

/-! ## Reduction of the general statement to the finite case -/

/-- **Four Colour Statement.**  The Four Colour Theorem for arbitrary planar graphs is
equivalent to the Four Colour Theorem for finite planar graphs.

The nontrivial direction is a compactness (De Bruijn–Erdős) argument: the space of
`4`-colourings is a compact space, planarity is inherited by induced subgraphs, and every
finite set of adjacency constraints is satisfiable by the finite case. -/
theorem four_color_statement.{u} : FourColourTheorem.{u} ↔ FiniteFourColourTheorem.{u} := by
  classical
  constructor
  · intro h V _ G hG
    exact h G hG
  · intro hfin V G hG
    set ι : Type u := {q : V × V // G.Adj q.1 q.2} with hι
    set Z : ι → Set (V → Fin 4) := fun q => {f | f q.1.1 ≠ f q.1.2} with hZ
    have hZclosed : ∀ q, IsClosed (Z q) := by
      intro q
      have hcont : Continuous fun f : V → Fin 4 => (f q.1.1, f q.1.2) :=
        (continuous_apply _).prodMk (continuous_apply _)
      exact (isClosed_discrete {y : Fin 4 × Fin 4 | y.1 ≠ y.2}).preimage hcont
    have hfip : ∀ t : Finset ι, ∃ f : V → Fin 4, ∀ q ∈ t, f q.1.1 ≠ f q.1.2 := by
      intro t
      set s : Finset V := t.biUnion (fun q => {q.1.1, q.1.2}) with hs
      have hmem : ∀ q ∈ t, q.1.1 ∈ (↑s : Set V) ∧ q.1.2 ∈ (↑s : Set V) := by
        intro q hq
        constructor <;>
        · simp only [hs, Finset.coe_biUnion, Set.mem_iUnion]
          exact ⟨q, by simpa using hq, by simp⟩
      obtain ⟨C⟩ := hfin (G.induce (↑s : Set V)) (hG.induce _)
      refine ⟨fun v => if hv : v ∈ (↑s : Set V) then C ⟨v, hv⟩ else 0, ?_⟩
      intro q hq
      obtain ⟨h1, h2⟩ := hmem q hq
      simp only [dif_pos h1, dif_pos h2]
      exact C.valid (show (G.induce (↑s : Set V)).Adj ⟨q.1.1, h1⟩ ⟨q.1.2, h2⟩ from q.2)
    have hne : (Set.univ ∩ ⋂ q, Z q).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      obtain ⟨t, ht⟩ := (isCompact_univ (X := V → Fin 4)).elim_finite_subfamily_closed Z
        hZclosed hempty
      obtain ⟨f, hf⟩ := hfip t
      have : f ∈ Set.univ ∩ ⋂ q ∈ t, Z q := by
        refine ⟨Set.mem_univ _, ?_⟩
        simp only [Set.mem_iInter]
        intro q hq
        exact hf q hq
      rw [ht] at this
      exact this
    obtain ⟨f, -, hf⟩ := hne
    simp only [Set.mem_iInter, hZ, Set.mem_setOf_eq] at hf
    exact ⟨SimpleGraph.Coloring.mk f fun {a b} hab => hf ⟨(a, b), hab⟩⟩

/-- A further reduction: the Four Colour Theorem for finite planar graphs is equivalent to
the Four Colour Theorem for finite *connected* planar graphs. -/
theorem finiteFourColourTheorem_iff_connected.{u} : FiniteFourColourTheorem.{u} ↔
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), IsPlanar G → G.Connected → G.Colorable 4 := by
  classical
  constructor
  · intro h V _ G hG _
    exact h G hG
  · intro h V _ G hG
    rw [SimpleGraph.colorable_iff_forall_connectedComponents]
    intro c
    have : Finite (↑c.supp : Set V) := Subtype.finite
    letI : Fintype (↑c.supp : Set V) := Fintype.ofFinite _
    exact h c.toSimpleGraph (hG.induce c.supp) c.connected_toSimpleGraph

end Frontier


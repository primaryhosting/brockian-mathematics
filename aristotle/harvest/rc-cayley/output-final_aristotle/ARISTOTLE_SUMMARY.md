# Summary of changes for run 508ea4d6-648c-48de-bcd8-cd6a9f7c8d96
The formalization is complete in Lean and verified with the tools; the file `Cayley.lean` (single file, bare `import Mathlib`) builds with zero errors and zero `sorry`.

**Statement formalized (mathematical content unchanged):**
```lean
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2)
```

**Structure of the Lean development** (everything proved inline; no Archive/Theorems100/GeometryOfNumbers/Erdos699 namespaces, no `native_decide`, no added axioms):
1. `IsForest A S f` — rooted forests encoded as parent functions: `f` fixes everything outside `A \ S`, maps `A \ S` into `A`, and iterating `f` from any vertex of `A` reaches the root set `S`.
2. A root-deletion bijection (`cut`/`uncut`, with `children A S r f`) between forests on `A` with roots `S` and given children-set `C` of a root `r`, and forests on `A.erase r` with roots `S.erase r ∪ C`; summing over `C` yields a recursion.
3. Binomial identities `∑ C(m,i) q^(m-i) = (q+1)^m` and `∑ i·C(m,i) q^(m-i) = m(q+1)^(m-1)`, plus strong induction on `|A|`, give `card_forestFinset`: `|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)`.
4. Trees ↔ rooted forests with a single root: `parent` (second vertex of the unique path to `0`) and `graphOf`, with both directions shown injective, so the counts agree.
5. Specialising to `A = univ`, `S = {0}` in `Fin n` and cancelling one factor of `n` gives `n ^ (n - 2)`.

**Fixes made this session** (the two issues that blocked the independent Lean 4.32.0 check, reproduced here against a Mathlib v4.32.0 build):
- `length_treePath_parent`: the counting-induction step failed because the hypothesis and goal print identically but differ in the implicit source-vertex argument of `Walk.length` (`(treePath hG v).snd` vs `parent hG v`), so the arithmetic automation saw two unrelated atoms. Rewrote into the hypothesis and closed the goal with `exact lt_of_lt_of_le (Nat.lt_succ_self _) hl.le`, which matches up to definitional equality.
- Added `noncomputable instance instFintypeTreeSubtype (n : ℕ) : Fintype {G : SimpleGraph (Fin n) // G.IsTree} := Fintype.ofFinite _`, since at 4.32.0 this instance is no longer synthesized automatically; it is derived from Mathlib's finiteness of `SimpleGraph V` for finite `V`, leaving the theorem statement unchanged.

**Verification:** the whole file compiles with zero errors at Lean 4.32.0 with Mathlib v4.32.0 (only a `push_neg` deprecation warning remains) and also under the toolchain pinned in the project; `#print axioms Brockian.Cayley.cayley_formula` reports only `propext`, `Classical.choice`, `Quot.sound`; a search confirms no `sorry`/`admit`/`native_decide`. All work is committed and pushed.

# Summary of changes for run 5c70ffc9-5d13-4020-a76d-03af3f2e1658
**Cayley's formula is fully proved in `Cayley.lean`, with no `sorry`, no `admit`, no `native_decide`, and no added axioms.**

The original statement is unchanged:

```lean
theorem cayley_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} = n ^ (n - 2)
```

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

**Proof architecture** (all developed from scratch — the pinned Mathlib has no matrix–tree theorem, Prüfer codes, or Cayley formula; only core `SimpleGraph`/`Finset` API is used, under a bare `import Mathlib`):

1. *Rooted forests as parent functions.* `IsForest A S f` says `f : V → V` fixes everything outside `A \ S`, maps `A \ S` into `A`, and iterating `f` from any vertex of `A` eventually reaches the root set `S`.
2. *Root deletion bijection.* For a root `r ∈ S`, cutting the edges into `r` (`cut`/`uncut`, with `children A S r f` the set of children of `r`) is a bijection between forests on `A` with roots `S` whose children-set of `r` is `C`, and forests on `A.erase r` with roots `S.erase r ∪ C`. Summing over `C ⊆ A \ S` gives a recursion.
3. *Counting.* Combined with the binomial identities `∑ C(m,i) q^(m-i) = (q+1)^m` and `∑ i·C(m,i) q^(m-i) = m(q+1)^(m-1)`, strong induction on `|A|` yields the general formula
   `|A| * #(forests on A with roots S) = |S| * |A| ^ (|A| - |S|)` (`card_forestFinset`), valid for all `S ⊆ A`.
4. *Trees ↔ rooted forests with a single root.* A tree gives a parent function via the second vertex of the unique path to `0`; conversely a parent function gives a graph, shown to be a tree via connectedness plus the edge count `|E| + 1 = |V|`. Both maps are injective (the reverse direction uses that an acyclic parent function has no 2-cycle), so the two counts agree.
5. Specialising to `A = univ`, `S = {0}` in `Fin n` and cancelling one factor of `n` gives `n ^ (n - 2)`.

The file builds cleanly with the project's pinned toolchain and Mathlib (`lean-toolchain` and `lakefile.toml` were left as provided, i.e. v4.28.0; the development only uses standard Mathlib API). The build is also free of linter warnings (unused hypotheses were removed from the auxiliary lemmas rather than suppressed).

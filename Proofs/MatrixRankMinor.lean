module

/-
First-party proof composition for the classical rank/minor characterization.
No upstream source body is copied or adapted.

Mathematical background: the field rank/minor criterion is stated explicitly
in the proof of part (3) of Stacks Project Lemma 36.31.1, tag 0BDI:
https://stacks.math.columbia.edu/tag/0BDI . This elementary matrix consequence
does not import that lemma's derived-category framework. The later intended
specialization application is related to Fitting semicontinuity in Section
15.8, tag 07Z6; no specialization result is proved in this module.

Import-only code provenance:
https://github.com/leanprover-community/mathlib4
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Mathlib/LinearAlgebra/Matrix/Rank.lean :: rank_eq_finrank_span_cols:397,
rank_eq_finrank_span_row:567; copyright (c) 2021 Johan Commelin;
header authors Johan Commelin, Eric Wieser.
Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean ::
exists_linearIndependent':800; copyright (c) 2020 Anne Baanen;
header authors Johannes Hoelzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen.
Mathlib/LinearAlgebra/Dimension/Constructions.lean :: finrank_span_eq_card:458;
copyright (c) 2018 Mario Carneiro; header authors Mario Carneiro, Johannes
Hoelzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen.
Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean ::
linearIndependent_rows_iff_isUnit:365, isUnit_iff_isUnit_det:127;
copyright (c) 2019 Anne Baanen; header authors Anne Baanen, Lu-Ming Zhang.
Root and file headers specify Apache-2.0. No upstream modifications.
Thank you to these authors, the Stacks Project authors, and mathlib contributors.
"If I have seen further it is by standing on the sholders of Giants."
-- Isaac Newton, letter to Robert Hooke, 1676.
-/

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# A nonzero square minor of size equal to field rank

Select a basis from the actual columns, and then from the rows of the
column-restricted matrix. The finite equivalences only order these selected
indices; the entries remain entries of the original matrix. The proof covers
empty shapes and rank zero without an extra nonemptiness hypothesis: the
selected square matrix is then empty, with determinant one.
-/

namespace Matrix

noncomputable section

variable {k m n : Type*} [Field k] [Fintype m] [Fintype n]

/-- Classical rank/minor characterization, existence direction: a finite
matrix over a field has a nonzero square minor of size equal to its rank.
The elementary criterion is explicitly stated in the proof of Stacks Lemma
36.31.1(3), tag 0BDI. The injections record the row and column orders; they
impose no preferred sorting. Empty shapes and rank zero are included. -/
theorem exists_nonzero_minor_of_rank (M : Matrix m n k) :
    ∃ (rows : Fin M.rank → m) (cols : Fin M.rank → n),
      Function.Injective rows ∧ Function.Injective cols ∧
        (M.submatrix rows cols).det ≠ 0 := by
  classical
  -- An injected column subfamily has exactly the original column span.
  obtain ⟨ColumnBasisIndex, a, ha, hspan, hLI⟩ := exists_linearIndependent' k M.col
  letI : Finite ColumnBasisIndex := Finite.of_injective a ha
  letI : Fintype ColumnBasisIndex := Fintype.ofFinite ColumnBasisIndex
  have hColumnCard : Fintype.card ColumnBasisIndex = M.rank := by
    rw [M.rank_eq_finrank_span_cols, ← hspan, finrank_span_eq_card hLI]
  -- Order the selected columns before selecting rows, so that all subsequent
  -- row vectors already have the final coordinate type Fin M.rank → k.
  let eCols : Fin M.rank ≃ ColumnBasisIndex := (Fintype.equivFinOfCardEq hColumnCard).symm
  let cols : Fin M.rank → n := a ∘ eCols
  have hcols : Function.Injective cols := ha.comp eCols.injective
  let B : Matrix m (Fin M.rank) k := M.submatrix id cols
  have hBLI : LinearIndependent k B.col := by
    change LinearIndependent k ((M.col ∘ a) ∘ eCols)
    exact hLI.comp eCols eCols.injective
  have hBrank : B.rank = M.rank := by
    rw [B.rank_eq_finrank_span_cols, finrank_span_eq_card hBLI, Fintype.card_fin]
  -- Row rank equals column rank over a field. A basis selected from these
  -- actual rows consequently also has precisely M.rank members.
  obtain ⟨RowBasisIndex, b, hb, hrowspan, hrowLI⟩ := exists_linearIndependent' k B.row
  letI : Finite RowBasisIndex := Finite.of_injective b hb
  letI : Fintype RowBasisIndex := Fintype.ofFinite RowBasisIndex
  have hRowCard : Fintype.card RowBasisIndex = M.rank := by
    calc
      Fintype.card RowBasisIndex =
          Module.finrank k (Submodule.span k (Set.range (B.row ∘ b))) :=
        (finrank_span_eq_card hrowLI).symm
      _ = B.rank := by rw [hrowspan, ← B.rank_eq_finrank_span_row]
      _ = M.rank := hBrank
  let eRows : Fin M.rank ≃ RowBasisIndex := (Fintype.equivFinOfCardEq hRowCard).symm
  let rows : Fin M.rank → m := b ∘ eRows
  have hrows : Function.Injective rows := hb.comp eRows.injective
  let S : Matrix (Fin M.rank) (Fin M.rank) k := M.submatrix rows cols
  have hSLI : LinearIndependent k S.row := by
    change LinearIndependent k ((B.row ∘ b) ∘ eRows)
    exact hrowLI.comp eRows eRows.injective
  -- The cached inverse-matrix API applies also to a zero-by-zero matrix.
  have hSunit : IsUnit S := linearIndependent_rows_iff_isUnit.mp hSLI
  have hdet : IsUnit S.det := (isUnit_iff_isUnit_det S).mp hSunit
  exact ⟨rows, cols, hrows, hcols, hdet.ne_zero⟩

end
end Matrix

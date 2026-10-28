module

/-
First-party composition of classical determinant specialization and field
rank-nullity. No upstream source body is copied or adapted.

Mathematical background: the rank/minor criterion is explicit in the proof
of Stacks Project Lemma 36.31.1(3), tag 0BDI; finite-presentation Fitting
semicontinuity is treated in Section 15.8, tag 07Z6. This module gives the
elementary matrix argument directly. No flatness, locality, analytic germ,
all-order bound or geometric dimension conclusion is asserted.
https://stacks.math.columbia.edu/tag/0BDI
https://stacks.math.columbia.edu/tag/07Z6

Import-only code provenance:
https://github.com/leanprover-community/mathlib4
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean :: RingHom.map_det:318;
copyright (c) 2018 Kenny Lau; header authors Kenny Lau, Chris Hughes, Anne Baanen.
Mathlib/LinearAlgebra/Matrix/Rank.lean :: rank_of_det_ne_zero:222,
rank_submatrix_le:287; copyright (c) 2021 Johan Commelin;
header authors Johan Commelin, Eric Wieser.
Mathlib/LinearAlgebra/Dimension/RankNullity.lean ::
Submodule.finrank_quotient_add_finrank:247; copyright (c) 2024 Andrew Yang;
header author Andrew Yang.
Mathlib/LinearAlgebra/Dimension/DivisionRing.lean ::
DivisionRing.hasRankNullity:62; copyright (c) 2018 Mario Carneiro;
header authors Mario Carneiro, Johannes Hoelzl, Sander Dahmen,
Kim Morrison, Chris Hughes, Anne Baanen, Junyan Xu.
The provenance of the column/row selection and coordinate-space dimension
tools is retained in MatrixRankMinor.lean. Root and file headers specify
Apache-2.0. No upstream modifications. Thank you to these authors, the Stacks
Project authors, and all mathlib contributors.
"If I have seen further it is by standing on the sholders of Giants."
-- Isaac Newton, letter to Robert Hooke, 1676.
-/

public import «MatrixRankMinor»
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

@[expose] public section

/-!
# Rank and cokernel dimensions under entrywise coefficient specialization

For a commutative ring A, a residue map A → k, and an injection A → K into
fields, every nonzero residue minor is nonzero over K. The finite matrix
rank therefore cannot drop from k to K. Ordinary field rank-nullity reverses
this inequality for the dimensions of the actual cokernels.

Rectangular matrices use the actual entrywise `Matrix.map`. The bundled
`RingHom.mapMatrix` is used only on square submatrices, where its ring
structure and the determinant-map theorem naturally apply.
-/

namespace Matrix

noncomputable section

section FieldCokernel

variable {k m n : Type*} [Field k] [Fintype m] [Fintype n]

/-- Classical field rank-nullity for the actual matrix cokernel, expressed
as a module quotient. It includes empty row and column types. -/
theorem finrank_quotient_range_mulVecLin (M : Matrix m n k) :
    Module.finrank k ((m → k) ⧸ LinearMap.range M.mulVecLin) =
      Fintype.card m - M.rank := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range M.mulVecLin)
  rw [Module.finrank_pi] at h
  exact Nat.eq_sub_of_add_eq h

end FieldCokernel

section CoefficientSpecialization

variable {A k K m n : Type*} [CommRing A] [Field k] [Field K]
variable [Fintype m] [Fintype n]

/-- Classical determinantal rank comparison. The map to the first field is
arbitrary; injectivity is required only for the map to the second field.
The conclusion compares actual entrywise images of the original matrix. -/
theorem rank_map_le_rank_map_of_injective (M : Matrix m n A)
    (ρ : A →+* k) (ι : A →+* K) (hι : Function.Injective ι) :
    (M.map ρ).rank ≤ (M.map ι).rank := by
  classical
  obtain ⟨rows, cols, _, _, hminor⟩ := exists_nonzero_minor_of_rank (M.map ρ)
  let S : Matrix (Fin (M.map ρ).rank) (Fin (M.map ρ).rank) A :=
    M.submatrix rows cols
  -- The same selected entries define a square matrix over the source ring.
  have hρdet : ρ S.det ≠ 0 := by
    rw [ρ.map_det]
    exact hminor
  have hSdet : S.det ≠ 0 := by
    intro hzero
    exact hρdet (by rw [hzero, map_zero])
  have hKminor : ((M.map ι).submatrix rows cols).det ≠ 0 := by
    change (ι.mapMatrix S).det ≠ 0
    rw [← ι.map_det]
    intro hzero
    apply hSdet
    apply hι
    simpa only [map_zero] using hzero
  calc
    (M.map ρ).rank = ((M.map ι).submatrix rows cols).rank := by
      rw [rank_of_det_ne_zero hKminor, Fintype.card_fin]
    _ ≤ (M.map ι).rank := rank_submatrix_le (M.map ι) rows cols

/-- The cokernel dimension over the injected field is bounded by the
cokernel dimension over the residue field. This uses rank-nullity over
the two fields, not a rank-nullity assumption on the source ring. -/
theorem finrank_quotient_range_map_le (M : Matrix m n A)
    (ρ : A →+* k) (ι : A →+* K) (hι : Function.Injective ι) :
    Module.finrank K ((m → K) ⧸ LinearMap.range (M.map ι).mulVecLin) ≤
      Module.finrank k ((m → k) ⧸ LinearMap.range (M.map ρ).mulVecLin) := by
  rw [finrank_quotient_range_mulVecLin, finrank_quotient_range_mulVecLin]
  exact Nat.sub_le_sub_left (rank_map_le_rank_map_of_injective M ρ ι hι) (Fintype.card m)

end CoefficientSpecialization
end
end Matrix

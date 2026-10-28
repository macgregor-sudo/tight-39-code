module

public import PipelineNaturality
public import SliceGlue
public import A6Field
public import A6DataLin

@[expose] public section

/-!
# A6 compact route — statements D1–D4 (lane LIN), fixed by INTEG

`g = QuarticCertificate.PipelineNaturality.translatedRowModP` (Q's B1 mod-p rows, = CHAINTOP's `g_p`), `E = id`,
field `A6Compact.F = ZMod 1048573` with Mathlib's `ZMod.instField` (instance `A6Compact.fact_prime_p`).
Lane LIN proves `lin_annihilates : StmtD1`, `lin_pivot : StmtD2`, `lin_vanish : StmtD3`, `lin_dim : StmtD4`
(namespace `A6Compact`), importing this file (never `A6Interface`, which holds same-named `sorry` placeholders).
-/

open MvPolynomial Module PolynomialJets SliceLemmas QuarticCertificate.PipelineNaturality

namespace A6Compact

/-- (D1) `w · L_p = 0`: the annihilator weights kill the linear parts (first conjunct of `HFpCumulative`). -/
abbrev StmtD1 : Prop :=
  ∀ s j, ∑ r, wLin s r * equationLinearMatrix translatedRowModP r j = 0

/-- (D2) `Bsl` is in pivot form at `pivSl` (A3 `SliceLemmas.IsPivot`). -/
abbrev StmtD2 : Prop := IsPivot Bsl pivSl

/-- (D3) the linear parts of the rows vanish on the slice (`L_p · Bsl = 0`; use CHAINMID RankBridge
`ChainMid.cutLinearSpace_nil_le_linearAnnihilator`). -/
abbrev StmtD3 : Prop :=
  cutLinearSpace translatedRowModP (id : Fin 2184 → Fin 2184) [] ≤ linearAnnihilator Bsl

/-- (D4) `rank L_p ≥ 973` (use CHAINMID RankBridge `ChainMid.le_finrank_cutLinearSpace_nil_of_det`). -/
abbrev StmtD4 : Prop :=
  1053 - 80 ≤ finrank F (cutLinearSpace translatedRowModP (id : Fin 2184 → Fin 2184) [])

/-- Q's field structure on `ZMod 1048573` IS Mathlib's (definitionally): facts proved by Q under
`letI := Matrix.zmodField 1048573 Matrix.prime_1048573` transfer to the library instance. -/
theorem zmodField_eq : Matrix.zmodField 1048573 Matrix.prime_1048573 = ZMod.instField 1048573 := rfl

end A6Compact

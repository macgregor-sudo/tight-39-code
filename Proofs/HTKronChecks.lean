module

public import HTKronExactness

@[expose] public section

/-!
# Kernel checks of the side conditions (ENGINE, first-party)

Strict sortedness of the 24 original eigencolumns, the Sidon property of the Golomb marks, and the
coefficient bound `2 (BE + BB) < 2^width` for all 24 components, each by `decide +kernel` on the
original definitions.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false

namespace Option2.NativeStress.HTRouteKron

open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary

theorem columns_strict : ∀ j : Fin 24, strictB (d6Entries (eigenIndex j)) = true := by
  decide +kernel

theorem columns_sorted (j : Fin 24) :
    (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val) :=
  strictB_pairwise _ (columns_strict j)

theorem sumPairs_nodup : (sumPairs.map fun p => p.2.2).Nodup := by
  decide +kernel

theorem gol_sidon : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
    j = j' ∧ l = l' :=
  sidon_of_nodup sumPairs_nodup

theorem hBound00 : 2 * (BE (denLcm (NativeH.rawEntries 0 0)) (NativeH.hSpec 0 0)
    (NativeH.rawEntries 0 0) + BB (fullScale (denLcm (NativeH.rawEntries 0 0))) (hBook 0 0)) <
    2 ^ width := by decide +kernel

theorem hBound01 : 2 * (BE (denLcm (NativeH.rawEntries 0 1)) (NativeH.hSpec 0 1)
    (NativeH.rawEntries 0 1) + BB (fullScale (denLcm (NativeH.rawEntries 0 1))) (hBook 0 1)) <
    2 ^ width := by decide +kernel

theorem hBound02 : 2 * (BE (denLcm (NativeH.rawEntries 0 2)) (NativeH.hSpec 0 2)
    (NativeH.rawEntries 0 2) + BB (fullScale (denLcm (NativeH.rawEntries 0 2))) (hBook 0 2)) <
    2 ^ width := by decide +kernel

theorem hBound10 : 2 * (BE (denLcm (NativeH.rawEntries 1 0)) (NativeH.hSpec 1 0)
    (NativeH.rawEntries 1 0) + BB (fullScale (denLcm (NativeH.rawEntries 1 0))) (hBook 1 0)) <
    2 ^ width := by decide +kernel

theorem hBound11 : 2 * (BE (denLcm (NativeH.rawEntries 1 1)) (NativeH.hSpec 1 1)
    (NativeH.rawEntries 1 1) + BB (fullScale (denLcm (NativeH.rawEntries 1 1))) (hBook 1 1)) <
    2 ^ width := by decide +kernel

theorem hBound12 : 2 * (BE (denLcm (NativeH.rawEntries 1 2)) (NativeH.hSpec 1 2)
    (NativeH.rawEntries 1 2) + BB (fullScale (denLcm (NativeH.rawEntries 1 2))) (hBook 1 2)) <
    2 ^ width := by decide +kernel

theorem hBound20 : 2 * (BE (denLcm (NativeH.rawEntries 2 0)) (NativeH.hSpec 2 0)
    (NativeH.rawEntries 2 0) + BB (fullScale (denLcm (NativeH.rawEntries 2 0))) (hBook 2 0)) <
    2 ^ width := by decide +kernel

theorem hBound21 : 2 * (BE (denLcm (NativeH.rawEntries 2 1)) (NativeH.hSpec 2 1)
    (NativeH.rawEntries 2 1) + BB (fullScale (denLcm (NativeH.rawEntries 2 1))) (hBook 2 1)) <
    2 ^ width := by decide +kernel

theorem hBound22 : 2 * (BE (denLcm (NativeH.rawEntries 2 2)) (NativeH.hSpec 2 2)
    (NativeH.rawEntries 2 2) + BB (fullScale (denLcm (NativeH.rawEntries 2 2))) (hBook 2 2)) <
    2 ^ width := by decide +kernel

theorem hBound30 : 2 * (BE (denLcm (NativeH.rawEntries 3 0)) (NativeH.hSpec 3 0)
    (NativeH.rawEntries 3 0) + BB (fullScale (denLcm (NativeH.rawEntries 3 0))) (hBook 3 0)) <
    2 ^ width := by decide +kernel

theorem hBound31 : 2 * (BE (denLcm (NativeH.rawEntries 3 1)) (NativeH.hSpec 3 1)
    (NativeH.rawEntries 3 1) + BB (fullScale (denLcm (NativeH.rawEntries 3 1))) (hBook 3 1)) <
    2 ^ width := by decide +kernel

theorem hBound32 : 2 * (BE (denLcm (NativeH.rawEntries 3 2)) (NativeH.hSpec 3 2)
    (NativeH.rawEntries 3 2) + BB (fullScale (denLcm (NativeH.rawEntries 3 2))) (hBook 3 2)) <
    2 ^ width := by decide +kernel

theorem tBound00 : 2 * (BE (denLcm (NativeT.rawEntries 0 0)) (NativeT.tSpec 0 0)
    (NativeT.rawEntries 0 0) + BB (fullScale (denLcm (NativeT.rawEntries 0 0))) (tBook 0 0)) <
    2 ^ width := by decide +kernel

theorem tBound01 : 2 * (BE (denLcm (NativeT.rawEntries 0 1)) (NativeT.tSpec 0 1)
    (NativeT.rawEntries 0 1) + BB (fullScale (denLcm (NativeT.rawEntries 0 1))) (tBook 0 1)) <
    2 ^ width := by decide +kernel

theorem tBound02 : 2 * (BE (denLcm (NativeT.rawEntries 0 2)) (NativeT.tSpec 0 2)
    (NativeT.rawEntries 0 2) + BB (fullScale (denLcm (NativeT.rawEntries 0 2))) (tBook 0 2)) <
    2 ^ width := by decide +kernel

theorem tBound10 : 2 * (BE (denLcm (NativeT.rawEntries 1 0)) (NativeT.tSpec 1 0)
    (NativeT.rawEntries 1 0) + BB (fullScale (denLcm (NativeT.rawEntries 1 0))) (tBook 1 0)) <
    2 ^ width := by decide +kernel

theorem tBound11 : 2 * (BE (denLcm (NativeT.rawEntries 1 1)) (NativeT.tSpec 1 1)
    (NativeT.rawEntries 1 1) + BB (fullScale (denLcm (NativeT.rawEntries 1 1))) (tBook 1 1)) <
    2 ^ width := by decide +kernel

theorem tBound12 : 2 * (BE (denLcm (NativeT.rawEntries 1 2)) (NativeT.tSpec 1 2)
    (NativeT.rawEntries 1 2) + BB (fullScale (denLcm (NativeT.rawEntries 1 2))) (tBook 1 2)) <
    2 ^ width := by decide +kernel

theorem tBound20 : 2 * (BE (denLcm (NativeT.rawEntries 2 0)) (NativeT.tSpec 2 0)
    (NativeT.rawEntries 2 0) + BB (fullScale (denLcm (NativeT.rawEntries 2 0))) (tBook 2 0)) <
    2 ^ width := by decide +kernel

theorem tBound21 : 2 * (BE (denLcm (NativeT.rawEntries 2 1)) (NativeT.tSpec 2 1)
    (NativeT.rawEntries 2 1) + BB (fullScale (denLcm (NativeT.rawEntries 2 1))) (tBook 2 1)) <
    2 ^ width := by decide +kernel

theorem tBound22 : 2 * (BE (denLcm (NativeT.rawEntries 2 2)) (NativeT.tSpec 2 2)
    (NativeT.rawEntries 2 2) + BB (fullScale (denLcm (NativeT.rawEntries 2 2))) (tBook 2 2)) <
    2 ^ width := by decide +kernel

theorem tBound30 : 2 * (BE (denLcm (NativeT.rawEntries 3 0)) (NativeT.tSpec 3 0)
    (NativeT.rawEntries 3 0) + BB (fullScale (denLcm (NativeT.rawEntries 3 0))) (tBook 3 0)) <
    2 ^ width := by decide +kernel

theorem tBound31 : 2 * (BE (denLcm (NativeT.rawEntries 3 1)) (NativeT.tSpec 3 1)
    (NativeT.rawEntries 3 1) + BB (fullScale (denLcm (NativeT.rawEntries 3 1))) (tBook 3 1)) <
    2 ^ width := by decide +kernel

theorem tBound32 : 2 * (BE (denLcm (NativeT.rawEntries 3 2)) (NativeT.tSpec 3 2)
    (NativeT.rawEntries 3 2) + BB (fullScale (denLcm (NativeT.rawEntries 3 2))) (tBook 3 2)) <
    2 ^ width := by decide +kernel

end Option2.NativeStress.HTRouteKron

module

public import NativeH00Equilibrium
public import NativeH01Equilibrium
public import NativeH02Equilibrium
public import NativeH10Equilibrium
public import NativeH11Equilibrium
public import NativeH12Equilibrium
public import NativeH20Equilibrium
public import NativeH21Equilibrium
public import NativeH22Equilibrium
public import NativeH30Equilibrium
public import NativeH31Equilibrium
public import NativeH32Equilibrium
public import NativeHAnchorEnumeration

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open scoped BigOperators
open PolynomialJets AnchorSupport NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration

/-- Actual H00 equilibrium on every original column, combining the proved324
anchor identities with accepted structural off-anchor support. -/
theorem h00_all_columns (c : Fin 1053) :
    ∑ r : Fin 2184, weightC 0 0 r * equationLinearMatrix
      (translatedRow (fun v => ((pointCoordinates v : ℝ) : ℂ))) r c = 0 := by
  apply all_columns_of_fast_anchor 0 0 _ c
  intro p k
  simpa [anchorPoint] using h00_all_anchor_fast p k

/-- All3888 actual H anchor-column cancellations, with no caller premise. -/
theorem all_anchor_fast (i : Fin 4) (a : Fin 3) :
    ∀ (p : Fin 12) (k : Fin 27), fastContraction (rawEntries i a) (hSpec i a)
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex (anchorPoint i p) k) = 0 := by
  fin_cases i <;> fin_cases a
  · intro p k
    simpa [anchorPoint] using h00_all_anchor_fast p k
  · exact h01_all_anchor_fast
  · exact h02_all_anchor_fast
  · exact h10_all_anchor_fast
  · exact h11_all_anchor_fast
  · exact h12_all_anchor_fast
  · exact h20_all_anchor_fast
  · exact h21_all_anchor_fast
  · exact h22_all_anchor_fast
  · exact h30_all_anchor_fast
  · exact h31_all_anchor_fast
  · exact h32_all_anchor_fast

/-- Every one of the twelve frozen H components annihilates every one of the
1053 columns of the original2184-row linearization at the accepted native seed. -/
theorem all_columns (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightC i a r * equationLinearMatrix
      (translatedRow (fun v => ((pointCoordinates v : ℝ) : ℂ))) r c = 0 :=
  all_columns_of_fast_anchor i a (all_anchor_fast i a) c

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.h00_all_columns
#print axioms Option2.NativeStress.NativeH.Equilibrium.all_anchor_fast
#print axioms Option2.NativeStress.NativeH.Equilibrium.all_columns

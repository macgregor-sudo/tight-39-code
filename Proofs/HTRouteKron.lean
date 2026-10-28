module

public import HTKronNative
public import HTKronChecks
public import HTKronH
public import HTKronT00
public import HTKronT01
public import HTKronT02
public import HTKronT10
public import HTKronT11
public import HTKronT12
public import HTKronT20
public import HTKronT21
public import HTKronT22
public import HTKronT30
public import HTKronT31
public import HTKronT32
public import BookHTQuartic

@[expose] public section

/-!
# H/T reproduction by one Kronecker evaluation per component (first-party consumer)

Both target identities for every `z`, `i`, `a`, from the 24 kernel evaluations, the 24 bound
checks, column sortedness and the Sidon property, through the accepted bridges
`native_H_quadratic_variation` / `native_T_quadratic_variation`. The source-prepared consumers in
`BookNativeHTTransfer` are proved there from the old reproduction family (they take no
hypotheses), so their five statements are restated here from the new identities.
-/

set_option autoImplicit false
set_option maxRecDepth 16384

noncomputable section

namespace Option2.NativeStress.HTRouteKron

open scoped BigOperators InnerProductSpace ComplexConjugate
open BookHT.TangentCoordinates Option2.BookNativeBase

/-- Target 1: the native H contraction equals Book H, every block and component. -/
theorem native_H_reproduction (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    (NativeH.residualContraction
        (Option2.NativeStress.originalF (bookBase + realV z)) i).ofLp a = (BookHT.H z i).ofLp a := by
  fin_cases i <;> fin_cases a
  exacts [h_target 0 0 columns_sorted gol_sidon hCheck00 hBound00 z,
    h_target 0 1 columns_sorted gol_sidon hCheck01 hBound01 z,
    h_target 0 2 columns_sorted gol_sidon hCheck02 hBound02 z,
    h_target 1 0 columns_sorted gol_sidon hCheck10 hBound10 z,
    h_target 1 1 columns_sorted gol_sidon hCheck11 hBound11 z,
    h_target 1 2 columns_sorted gol_sidon hCheck12 hBound12 z,
    h_target 2 0 columns_sorted gol_sidon hCheck20 hBound20 z,
    h_target 2 1 columns_sorted gol_sidon hCheck21 hBound21 z,
    h_target 2 2 columns_sorted gol_sidon hCheck22 hBound22 z,
    h_target 3 0 columns_sorted gol_sidon hCheck30 hBound30 z,
    h_target 3 1 columns_sorted gol_sidon hCheck31 hBound31 z,
    h_target 3 2 columns_sorted gol_sidon hCheck32 hBound32 z]

/-- Target 2: the native T contraction equals Book T, every block and component. -/
theorem native_T_reproduction (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    (NativeT.Reproduction.residualT
        (Option2.NativeStress.originalF (bookBase + realV z)) i).ofLp a = (BookHT.T z i).ofLp a := by
  fin_cases i <;> fin_cases a
  exacts [t_target 0 0 columns_sorted gol_sidon tCheck00 tBound00 z,
    t_target 0 1 columns_sorted gol_sidon tCheck01 tBound01 z,
    t_target 0 2 columns_sorted gol_sidon tCheck02 tBound02 z,
    t_target 1 0 columns_sorted gol_sidon tCheck10 tBound10 z,
    t_target 1 1 columns_sorted gol_sidon tCheck11 tBound11 z,
    t_target 1 2 columns_sorted gol_sidon tCheck12 tBound12 z,
    t_target 2 0 columns_sorted gol_sidon tCheck20 tBound20 z,
    t_target 2 1 columns_sorted gol_sidon tCheck21 tBound21 z,
    t_target 2 2 columns_sorted gol_sidon tCheck22 tBound22 z,
    t_target 3 0 columns_sorted gol_sidon tCheck30 tBound30 z,
    t_target 3 1 columns_sorted gol_sidon tCheck31 tBound31 z,
    t_target 3 2 columns_sorted gol_sidon tCheck32 tBound32 z]

theorem native_H_blocks_eq (z : BookHT.Blocks) :
    NativeH.residualContraction
      (Option2.NativeStress.originalF (bookBase + realV z)) = BookHT.H z := by
  funext i
  apply PiLp.ext
  intro a
  exact native_H_reproduction z i a

theorem native_T_blocks_eq (z : BookHT.Blocks) :
    NativeT.Reproduction.residualT
      (Option2.NativeStress.originalF (bookBase + realV z)) = BookHT.T z := by
  funext i
  apply PiLp.ext
  intro a
  exact native_T_reproduction z i a

theorem native_quartic_identity_hermitian (z : BookHT.Blocks) :
    FourBlock.delta z =
      (∑ i, ‖NativeH.residualContraction
        (Option2.NativeStress.originalF (bookBase + realV z)) i‖ ^ 2) +
      (1 / 2 : ℝ) *
        (∑ i, ‖NativeT.Reproduction.residualT
          (Option2.NativeStress.originalF (bookBase + realV z)) i‖ ^ 2) +
      3 * (∑ i, ∑ a, conj (BookHT.sigma (z i) a) *
        NativeH.residualContraction
          (Option2.NativeStress.originalF (bookBase + realV z)) i a).re := by
  simpa only [native_H_blocks_eq, native_T_blocks_eq] using
    BookHT.quartic_identity_hermitian z

theorem native_axis_vanishing (i : Fin 4) (z : BookHT.Blocks) (hz : FourBlock.OnAxis i z) :
    NativeH.residualContraction
        (Option2.NativeStress.originalF (bookBase + realV z)) = 0 ∧
      NativeT.Reproduction.residualT
        (Option2.NativeStress.originalF (bookBase + realV z)) = 0 := by
  simpa only [native_H_blocks_eq, native_T_blocks_eq] using BookHT.axis_vanishing i z hz

theorem native_selected_zero_cone (z : BookHT.Blocks) :
    (NativeH.residualContraction
        (Option2.NativeStress.originalF (bookBase + realV z)) = 0 ∧
      NativeT.Reproduction.residualT
        (Option2.NativeStress.originalF (bookBase + realV z)) = 0) ↔
      ∃ i, FourBlock.OnAxis i z := by
  simpa only [native_H_blocks_eq, native_T_blocks_eq] using BookHT.zero_cone z

end Option2.NativeStress.HTRouteKron

end

#print axioms Option2.NativeStress.HTRouteKron.native_H_reproduction
#print axioms Option2.NativeStress.HTRouteKron.native_T_reproduction
#print axioms Option2.NativeStress.HTRouteKron.native_H_blocks_eq
#print axioms Option2.NativeStress.HTRouteKron.native_T_blocks_eq
#print axioms Option2.NativeStress.HTRouteKron.native_quartic_identity_hermitian
#print axioms Option2.NativeStress.HTRouteKron.native_axis_vanishing
#print axioms Option2.NativeStress.HTRouteKron.native_selected_zero_cone

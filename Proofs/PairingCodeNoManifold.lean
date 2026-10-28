module
public import PairingDefinitions
public import PairingCode
public import NativeOriginalCodeNoManifold24
@[expose] public section

noncomputable section
namespace Option2StatementCode

theorem originalCode_no_open24_chart
    {N : Set CodeModuli} {O : Set (EuclideanSpace ℝ (Fin 24))}
    (hN : IsOpen N) (hseed : originalCode ∈ N) (hO : IsOpen O) :
    IsEmpty (N ≃ₜ O) := by
  have hN' := quotientHomeomorph.isOpenMap N hN
  have hseed' : CKM.NativeGoodPhase.codeClass CKM.NativeGoodPhase.onePhase ∈
      quotientHomeomorph '' N :=
    ⟨originalCode, hseed, quotientHomeomorph_originalCode⟩
  have hempty := Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_open24_chart
    hN' hseed' hO
  exact ⟨fun e => hempty.false ((quotientHomeomorph.image N).symm.trans e)⟩

theorem originalCode_no_charted24_neighborhood
    (N : Set CodeModuli) (hN : IsOpen N) (hseed : originalCode ∈ N)
    [ChartedSpace (EuclideanSpace ℝ (Fin 24)) N] : False := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 24)) (quotientHomeomorph '' N) :=
    (quotientHomeomorph.image N).chartedSpace
  exact Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_charted24_neighborhood
    (quotientHomeomorph '' N) (quotientHomeomorph.isOpenMap N hN)
    ⟨originalCode, hseed, quotientHomeomorph_originalCode⟩

#print axioms originalCode_no_open24_chart
#print axioms originalCode_no_charted24_neighborhood
end Option2StatementCode

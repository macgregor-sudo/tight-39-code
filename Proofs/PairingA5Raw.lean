module
public import PairingDefinitions
public import PairingA5PreMap
public import A5Main
@[expose] public section

noncomputable section
/- Inline after the checked native algebra/coordinates. This is the actual
 native automorphism saturation, with no label permutations. The four branch
 parametrizations and the chosen normal-slice chart are not replaced by it. -/
namespace Option2StatementA5
open Glennie NativePolynomial CKM.NativeTightCode

end Option2StatementA5

/- Concrete raw family constructors. The bilinear product is constrained by
 its full native coordinate formula, not by conclusions about its solutions.
 A statement must existentially supply it with NativeProduct; no arbitrary
 product premise is intended. Native prodC supplies the exact witness. -/
namespace Option2StatementA5Raw
open Glennie NativePolynomial CKM.NativeFirstOrder
open Option2StatementA5Anchor Option2StatementA5
open ContinuousLinearMap
end Option2StatementA5Raw

namespace Option2StatementA5Raw
open CKM.NativeFirstOrder Option2StatementA5

theorem native_product_exists : ∃ m : Product, NativeProduct m :=
  ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native⟩

theorem rawMap62_eq_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4)
    (p : RawParam62 CKM.NativeGroupSlice.prodC) :
    rawMap62 CKM.NativeGroupSlice.prodC ξ hξ H p = CKM.NativeFourFamily.rawMap62 ξ hξ H p := rfl

theorem commonMap_eq_native (ξ : Fin 4 → ℂ)
    (p : CommonParam CKM.NativeGroupSlice.prodC) :
    commonMap CKM.NativeGroupSlice.prodC ξ p = CKM.NativeFourFamily.commonMap ξ p := rfl

/- Faithful existential raw chart: the product is fixed by its native formula
 and all four raw maps remain concrete, including their 70-parameter versions. -/
theorem raw_simultaneous_chart {ξ₀ : Fin 4 → ℂ} (hξ : CKM.NativeFourFamily.IsGoodPhase ξ₀) :
    ∃ m : Product, NativeProduct m ∧
    (∃ Φ : OpenPartialHomeomorph RawModel Cfg,
      (0 : RawModel) ∈ Φ.source ∧ Φ 0 = literalCfg ξ₀ ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))
        (literalCfg ξ₀) (commonMap m ξ₀) 0 ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap62 m ξ₀ hξ.1 H) 0) ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap m ξ₀ hξ.1 H) 0) ∧
      (∀ H H', H ≠ H' →
        Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩
            Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))) := by
  refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native, ?_⟩
  exact (CKM.NativeFourFamily.native_simultaneous_charts hξ).2

#print axioms raw_simultaneous_chart
end Option2StatementA5Raw

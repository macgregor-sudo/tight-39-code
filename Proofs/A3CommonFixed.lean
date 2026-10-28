module

public import A3Family
public import A3Automorphisms
public import A3Elimination
public import A3Quartet
public import KfixLiteral

@[expose] public section

/-!
# The jointly fixed first-order space has dimension eight at every phase
-/

noncomputable section

namespace CKM.NativeFirstOrder

theorem finrank_commonFixed (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ ↥(fixedSpace (compensated R0 (outcomeShift shift0)) ⊓
      fixedSpace (compensated R1 (outcomeShift shift1)) ⊓ firstOrderSystem (literalPoint ξ)) = 8 := by
  rw [kf_finrank_literal_eq ξ hξ, kf_finrank_std ξ hξ]

end CKM.NativeFirstOrder

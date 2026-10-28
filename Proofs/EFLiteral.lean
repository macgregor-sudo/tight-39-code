module

public import EFMain
public import TCSharp

@[expose] public section

/-!
# The accepted literal code at unit phases

The label equivalence `literalLabel i = (i / 3, i % 3)`, inverse `framePointIndex`, makes the frames
of `literalPoint ξ` exactly the accepted `CKM.NativeFirstOrder.literal_frame ξ hξ`. With the accepted
`CKM.NativeTightCode.literalPoint_overlapBound`, the equality theorem gives the baseline energy at
every unit phase (including the resonant `ξ = 1`) for every admissible `φ`, with the domain condition
discharged from `1/3 ∈ U`. No new tightness or reproduction hypothesis.
-/

noncomputable section

namespace CKM.NativeExactFrameEnergy

open Glennie SupportedStress.NativeFrames CKM.NativeTightCode CKM.NativeFirstOrder
  NativePolynomial.ConfigurationResiduals

/-- Literal labels `i ↦ (i / 3, i % 3)`, with inverse the accepted `framePointIndex`. -/
def literalLabel : Fin 39 ≃ Fin 13 × Fin 3 where
  toFun i := (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩)
  invFun x := framePointIndex x.1 x.2
  left_inv i := framePointIndex_div_mod i
  right_inv x := by
    rcases x with ⟨f, a⟩
    ext <;> simp [framePointIndex_val]; omega

theorem literal_frames (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∀ h, Frame (framesOf literalLabel (literalPoint ξ) h) := by
  intro h
  exact literal_frame ξ hξ h

theorem literal_cross (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf literalLabel (literalPoint ξ)) k = 1 / 3 :=
  (cross_eq_third_iff_overlapBound (literalPoint ξ) literalLabel (literal_frames ξ hξ)).mpr
    (literalPoint_overlapBound ξ hξ)

/-- Baseline equality at the literal code, from the equality theorem. -/
theorem literal_energy_eq_baseline (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M) :
    E39 φ (literalPoint ξ) = E0 φ := by
  refine (energy_eq_baseline_iff_overlapBound (literalPoint ξ) literalLabel (literal_frames ξ hξ)
    φ U hU hconvex hφ hbase m M hm hcurv ?_).mpr (literalPoint_overlapBound ξ hξ)
  intro k
  rw [literal_cross ξ hξ k]
  exact hbase

/-- The literal code minimizes the indexed energy on the exact-frame/domain-restricted class. -/
theorem literal_minimum (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U) :
    E39 φ (literalPoint ξ) ≤ E39 φ P := by
  rw [literal_energy_eq_baseline ξ hξ φ U hU hconvex hφ hbase m M hm hcurv]
  exact baseline_le_energy P e hframe φ U hU hconvex hφ hbase m M hm hcurv hnear

theorem literal_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Injective (literalPoint ξ) :=
  injective_of_overlapBound (literalPoint ξ) (literalPoint_pure ξ hξ)
    (literalPoint_overlapBound ξ hξ)

end CKM.NativeExactFrameEnergy

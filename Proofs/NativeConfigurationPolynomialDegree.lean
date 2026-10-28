module

public import NativeConfigurationTranslatedIdeal
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/-!
# Degree bounds for the actual configuration residuals

The original F rows are the literal coordinate-product, trace, frame-sum and
pairing formulas. Constants have degree zero and each coordinate has degree
at most one, both before and after translation. Finite-sum and product degree
inequalities therefore bound every original and translated F row by two.
No row enumeration, point-solution hypothesis or coefficient certificate is used.

First-party proofs using the named native formulas and Mathlib degree APIs;
no upstream proof body is copied. Existing native provenance and licenses
remain with NativeConfigurationTranslatedIdeal and its source contributors. Imported
degree APIs in Algebra/MvPolynomial/Degrees.lean and CommRing.lean remain
pinned to Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2. Thank you to the native-model, Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals

open MvPolynomial PolynomialJets CoordinateMaps FrameResiduals ConfigurationResidualIndices

private theorem fResidual_totalDegree_le_two_of_affine_hom
    (φ : MvPolynomial (Fin 1053) ℂ →+* MvPolynomial (Fin 1053) ℂ)
    (hC : ∀ c : ℂ, φ (C c) = C c)
    (hX : ∀ j : Fin 1053, (φ (X j)).totalDegree ≤ 1)
    (h t : ℂ) (r : FLabel) : (φ (fResidual h t r)).totalDegree ≤ 2 := by
  have hp (i : Fin 39) (k : Fin 27) : (φ (point i k)).totalDegree ≤ 1 :=
    hX (variableIndex i k)
  have hProduct (i j : Fin 39) (k : Fin 27) :
      (φ (coordinateProduct (C h) (point i) (point j) k)).totalDegree ≤ 2 := by
    rw [coordinateProduct_polynomial_apply]
    simp only [tensorPolynomial, map_sum, map_mul φ, hC]
    apply totalDegree_finsetSum_le
    intro a _
    apply totalDegree_finsetSum_le
    intro b _
    calc
      _ ≤ (φ (point i a) * φ (point j b)).totalDegree +
          (C (h * (IntegralStructureConstants.numerator a b k : ℂ))).totalDegree :=
        totalDegree_mul _ _
      _ ≤ 2 := by
        simpa only [totalDegree_C, Nat.add_zero] using
          (totalDegree_mul (φ (point i a)) (φ (point j b))).trans
            (Nat.add_le_add (hp i a) (hp j b))
  have hTrace (i : Fin 39) : (φ (coordinateTrace (point i))).totalDegree ≤ 1 := by
    rw [coordinateTrace_apply]
    simp only [map_add]
    exact (totalDegree_add _ _).trans
      (max_le ((totalDegree_add _ _).trans (max_le (hp i 0) (hp i 1))) (hp i 2))
  have hInt (c : ℤ) : (φ (c : MvPolynomial (Fin 1053) ℂ)).totalDegree = 0 := by
    have hConst : (c : MvPolynomial (Fin 1053) ℂ) = C (c : ℂ) :=
      (map_intCast (C : ℂ →+* MvPolynomial (Fin 1053) ℂ) c).symm
    rw [hConst, hC, totalDegree_C]
  have hPairing (i j : Fin 39) :
      (φ (coordinatePairing (point i) (point j))).totalDegree ≤ 2 := by
    simp only [coordinatePairing, map_sum, map_mul]
    apply totalDegree_finsetSum_le
    intro k _
    have hLeft :
        (φ (IntegralStructureConstants.coordinateTraceWeight k : MvPolynomial (Fin 1053) ℂ) *
          φ (point i k)).totalDegree ≤ 1 := by
      exact (totalDegree_mul _ _).trans (by simpa only [hInt, Nat.zero_add] using hp i k)
    exact (totalDegree_mul _ _).trans (Nat.add_le_add hLeft (hp j k))
  have hUnit (k : Fin 27) :
      (φ (coordinateUnit k : MvPolynomial (Fin 1053) ℂ)).totalDegree ≤ 2 := by
    unfold coordinateUnit
    split_ifs <;> simp only [map_one, map_zero, totalDegree_one, totalDegree_zero, zero_le]
  rcases r with ⟨i, k⟩ | (i | (⟨f, k⟩ | ij))
  · change (φ (coordinateProduct (C h) (point i) (point i) k - point i k)).totalDegree ≤ 2
    rw [map_sub]
    exact (totalDegree_sub _ _).trans (max_le (hProduct i i k) ((hp i k).trans (by decide)))
  · change (φ (coordinateTrace (point i) - 1)).totalDegree ≤ 2
    rw [map_sub, map_one]
    exact (totalDegree_sub _ _).trans
      (max_le ((hTrace i).trans (by decide)) (by simp only [totalDegree_one, zero_le]))
  · change (φ ((∑ a : Fin 3, point (framePointIndex f a) k) - coordinateUnit k)).totalDegree ≤ 2
    rw [map_sub, map_sum]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_finsetSum_le (fun a _ => hp (framePointIndex f a) k)).trans (by decide)
    · exact hUnit k
  · change (φ (coordinatePairing (point ij.val.1) (point ij.val.2) -
        (if ij.val.1.val / 3 = ij.val.2.val / 3 then 0 else C t))).totalDegree ≤ 2
    rw [map_sub]
    apply (totalDegree_sub _ _).trans
    apply max_le (hPairing _ _)
    split_ifs <;> simp only [map_zero, hC, totalDegree_zero, totalDegree_C, zero_le]

/-- Every literal original F row has polynomial total degree at most two. -/
theorem fRow_totalDegree_le_two (h t : ℂ) (r : Fin 2184) :
    (fRow h t r).totalDegree ≤ 2 := by
  exact fResidual_totalDegree_le_two_of_affine_hom (RingHom.id _) (fun _ => rfl)
    (fun j => by simp only [RingHom.id_apply, totalDegree_X, le_refl])
    h t (fNumber.symm r)

/-- Translation at any complex point preserves the degree-two bound on every
literal original F row, discharging the quartic consumer's degree premise. -/
theorem translated_fRow_totalDegree_le_two (h t : ℂ) (P : Fin 1053 → ℂ)
    (r : Fin 2184) : (translate P (fRow h t r)).totalDegree ≤ 2 := by
  let φ : MvPolynomial (Fin 1053) ℂ →+* MvPolynomial (Fin 1053) ℂ :=
    MvPolynomial.eval₂Hom C (fun j => X j + C (P j))
  have hC : ∀ c : ℂ, φ (C c) = C c := fun c => MvPolynomial.eval₂Hom_C _ _ c
  have hX : ∀ j : Fin 1053, (φ (X j)).totalDegree ≤ 1 := by
    intro j
    rw [show φ (X j) = X j + C (P j) from MvPolynomial.eval₂Hom_X' _ _ j]
    exact (totalDegree_add _ _).trans (by
      simp only [totalDegree_X, totalDegree_C]
      decide)
  exact fResidual_totalDegree_le_two_of_affine_hom φ hC hX h t (fNumber.symm r)

end NativePolynomial.ConfigurationResiduals

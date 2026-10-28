module

public import HTPhaseKronSem
public import A3Family

@[expose] public section

/-! # L1: the phased configuration `Φ(u)` IS the accepted literal family `literalCfg ξ`

For every unit phase `ξ`, with `u_a = ξ_a / ξ_base,a` (`ξ_base = exactPhases`, the Book base),
`PhiR Q12.toComplex u = pack (literalCfg ξ)` coordinatewise. The proof reads the accepted
`literalPoint`/`literalFamilyPoint` (A3), the accepted base bridge `point_bridge` (PointQ12Bridge) and
the accepted `literalPoint_low`/`literalPoint_eq_family`/`literalPoint_exactPhases` (A3Family).
First-party; no upstream implementation copied. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseKron
open CompactAlbert CKM.NativeFirstOrder NativePolynomial NativeH.Equilibrium
open QuadraticCertificate.ExactCKMConfiguration UnitaryErrorBases.ThreeCycleFourier UnitaryErrorBases.ComplexQuartet

/-! ## Octonion basis and the two moving family formulas -/

theorem nob4 : nativeOctonionBasis 4 = (0, 1) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [nativeOctonionBasis, nativeCoordinateBasis, firstUpperCoordinateIndex, fromUpperCoordinates]
theorem nob6 : nativeOctonionBasis 6 = (0, ⟨0, 0, 1, 0⟩) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [nativeOctonionBasis, nativeCoordinateBasis, firstUpperCoordinateIndex, fromUpperCoordinates]
theorem nob2 : nativeOctonionBasis 2 = (⟨0, 0, 1, 0⟩, 0) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [nativeOctonionBasis, nativeCoordinateBasis, firstUpperCoordinateIndex, fromUpperCoordinates]

noncomputable def g2 (α β : ℂ) : Fin 27 → ℝ :=
  ![1/3, Complex.normSq α/3, Complex.normSq β/3, 0, 0, 0, 0, -α.re/3, -α.im/3, 0, 0,
    0, 0, 0, 0, 0, 0, -β.re/3, β.im/3, 0, 0, -(α*β).re/3, (α*β).im/3, 0, 0, 0, 0]

noncomputable def g3 (γ δ : ℂ) : Fin 27 → ℝ :=
  ![1/3, Complex.normSq γ/3, Complex.normSq δ/3, 0, 0, 0, 0, 0, 0, -γ.re/3, γ.im/3,
    0, 0, -δ.re/3, -δ.im/3, 0, 0, 0, 0, 0, 0, 0, 0, -(γ*δ).re/3, (γ*δ).im/3, 0, 0]

theorem coords_g2 (α β : ℂ) :
    upperCoordinates (nativeOuterProductThird
      (Glennie.octMul (complexOctonion α) (nativeOctonionBasis 4))
      (Glennie.octMul (complexOctonion β) (nativeOctonionBasis 6))) = g2 α β := by
  rw [nob4, nob6]
  funext k
  fin_cases k <;>
    simp [upperCoordinates, nativeOuterProductThird, Glennie.octMul, Glennie.octConj,
      Glennie.octNormSq, complexOctonion, g2, Quaternion.normSq_def', Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem coords_g3 (γ δ : ℂ) :
    upperCoordinates (nativeOuterProductThird
      (Glennie.octMul (complexOctonion γ) (nativeOctonionBasis 6))
      (Glennie.octMul (complexOctonion δ) (nativeOctonionBasis 2))) = g3 γ δ := by
  rw [nob6, nob2]
  funext k
  fin_cases k <;>
    simp [upperCoordinates, nativeOuterProductThird, Glennie.octMul, Glennie.octConj,
      Glennie.octNormSq, complexOctonion, g3, Quaternion.normSq_def', Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Points `21..29` are family group 2 (window 2), points `30..38` group 3 (window 3). -/
theorem point_g2 (ξ : Fin 4 → ℂ) (p : ℕ) (h1 : 21 ≤ p) (h2 : p < 30) :
    upperCoordinates (literalPoint ξ ⟨p, by omega⟩) =
      g2 (ξ 0 * character (((p - 21) % 3 : ℕ) : PhaseIndex))
        (ξ 1 * character ((((p - 21) / 3 : ℕ) : PhaseIndex) + (((p - 21) % 3 : ℕ) : PhaseIndex))) := by
  rw [literalPoint_eq_family ξ 1 (((p - 21) / 3 : ℕ) : PhaseIndex) (((p - 21) % 3 : ℕ) : PhaseIndex)
    ⟨p, by omega⟩ (by simp only [ZMod.val_natCast]; simp; omega)]
  rw [← coords_g2]
  rfl

theorem point_g3 (ξ : Fin 4 → ℂ) (p : ℕ) (h1 : 30 ≤ p) (h2 : p < 39) :
    upperCoordinates (literalPoint ξ ⟨p, by omega⟩) =
      g3 (ξ 2 * character (((p - 30) % 3 : ℕ) : PhaseIndex))
        (ξ 3 * character ((((p - 30) / 3 : ℕ) : PhaseIndex) + (((p - 30) % 3 : ℕ) : PhaseIndex))) := by
  rw [literalPoint_eq_family ξ 2 (((p - 30) / 3 : ℕ) : PhaseIndex) (((p - 30) % 3 : ℕ) : PhaseIndex)
    ⟨p, by omega⟩ (by simp only [ZMod.val_natCast]; simp; omega)]
  rw [← coords_g3]
  rfl

end Option2.NativeStress.HTPhaseKron

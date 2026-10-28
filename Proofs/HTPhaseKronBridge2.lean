module

public import HTPhaseKronBridge

@[expose] public section

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseKron
open CompactAlbert CKM.NativeFirstOrder NativePolynomial NativeH.Equilibrium
open QuadraticCertificate.ExactCKMConfiguration UnitaryErrorBases.ThreeCycleFourier UnitaryErrorBases.ComplexQuartet

/-- Complexified literal coordinate by natural index (`0` outside the 1053 range). -/
noncomputable def Cn (ξ : Fin 4 → ℂ) (n : ℕ) : ℂ :=
  if h : n < 1053 then ((PartialAction.pack (literalCfg ξ) ⟨n, h⟩ : ℝ) : ℂ) else 0

theorem Cn_star (ξ : Fin 4 → ℂ) (n : ℕ) : star (Cn ξ n) = Cn ξ n := by
  unfold Cn; split_ifs <;> simp

theorem Cn_pc (ξ : Fin 4 → ℂ) (p c : ℕ) (hp : p < 39) (hc : c < 27) :
    Cn ξ (27 * p + c) = ((upperCoordinates (literalPoint ξ ⟨p, hp⟩) ⟨c, hc⟩ : ℝ) : ℂ) := by
  unfold Cn
  rw [dif_pos (by omega)]
  have key : ∀ (i : Fin 39) (k : Fin 27), i.val = p → k.val = c →
      literalCfg ξ i k = upperCoordinates (literalPoint ξ ⟨p, hp⟩) ⟨c, hc⟩ := by
    rintro ⟨i, hi⟩ ⟨k, hk⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    rfl
  simp only [PartialAction.pack]
  rw [key _ _ (show (27 * p + c) / 27 = p by omega) (show (27 * p + c) % 27 = c by omega)]

/-- The base link: the original `baseQ12` is the literal family at the Book base phases. -/
theorem base_link (n : ℕ) : Q12.toComplex (bq n) = Cn exactPhases n := by
  unfold bq Cn
  split_ifs with h
  · simp only [baseQ12, PartialAction.pack, literalCfg, literalPoint_exactPhases]
    rw [← FourSheets.PointQ12.point_bridge]
    rfl
  · simp

theorem exactPhases_unit' : IsUnitPhase exactPhases := by
  intro i
  fin_cases i <;> norm_num [exactPhases, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem ne_of_unit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (a : Fin 4) : ξ a ≠ 0 := by
  intro h; have := hξ a; rw [h, map_zero] at this; exact zero_ne_one this

theorem star_of_unit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (a : Fin 4) :
    (starRingEnd ℂ) (ξ a) = (ξ a)⁻¹ := by
  rw [Complex.inv_def, hξ a]; simp

/-- Phase ratios `u_a = ξ_a / ξ_base,a` as units. -/
noncomputable def Uph (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Fin 4 → ℂˣ := fun a =>
  Units.mk0 (ξ a / exactPhases a) (div_ne_zero (ne_of_unit hξ a) (ne_of_unit exactPhases_unit' a))

theorem mono_Uph (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m : Ex) :
    mono (Uph ξ hξ) m = (ξ 0 / exactPhases 0) ^ m.1 * (ξ 1 / exactPhases 1) ^ m.2.1 *
      (ξ 2 / exactPhases 2) ^ m.2.2.1 * (ξ 3 / exactPhases 3) ^ m.2.2.2 := by
  simp [mono, Uph, Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem normSq_mono (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m : Ex) :
    Complex.normSq (mono (Uph ξ hξ) m) = 1 := by
  rw [mono_Uph]
  simp only [map_mul, map_zpow₀, map_div₀]
  rw [hξ 0, hξ 1, hξ 2, hξ 3, exactPhases_unit' 0, exactPhases_unit' 1, exactPhases_unit' 2,
    exactPhases_unit' 3]
  simp

theorem mono_ne (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m : Ex) : mono (Uph ξ hξ) m ≠ 0 := by
  intro h; have := normSq_mono ξ hξ m; rw [h, map_zero] at this; exact zero_ne_one this

theorem star_mono (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m : Ex) :
    star (mono (Uph ξ hξ) m) = (mono (Uph ξ hξ) m)⁻¹ := by
  rw [Complex.inv_def, normSq_mono]; simp

theorem mono_neg (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m : Ex) :
    mono (Uph ξ hξ) (Ex.neg m) = (mono (Uph ξ hξ) m)⁻¹ := by
  rw [mono_Uph, mono_Uph]
  simp only [Ex.neg, zpow_neg, mul_inv]

/-- Assembling one moving plane from its complex character law. -/
theorem assemble (X Y Xb Yb M : ℂ) (hX : star X = X) (hY : star Y = Y) (hXb : star Xb = Xb)
    (hYb : star Yb = Yb) (hM : star M = M⁻¹)
    (h : X - Complex.I * Y = (Xb - Complex.I * Yb) * M) :
    X = 1/2 * (Xb - Complex.I * Yb) * M + 1/2 * (Xb + Complex.I * Yb) * M⁻¹ ∧
    Y = 1/2 * (Complex.I * (Xb - Complex.I * Yb)) * M - 1/2 * (Complex.I * (Xb + Complex.I * Yb)) * M⁻¹ := by
  have hc : X + Complex.I * Y = (Xb + Complex.I * Yb) * M⁻¹ := by
    have := congrArg star h
    simp only [star_sub, star_mul', hX, hY, hXb, hYb, hM, Complex.star_def, Complex.conj_I] at this
    linear_combination this
  constructor
  · linear_combination (1/2 : ℂ) * h + (1/2 : ℂ) * hc
  · linear_combination (Complex.I/2) * h - (Complex.I/2) * hc + Y * Complex.I_sq

end Option2.NativeStress.HTPhaseKron

module

public import NativeHIntegerBridge
public import NativeHIntegerRows

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open QuarticCertificate.RowBridge BookHT.TangentCoordinates

noncomputable def rationalShapeCoefficient (s : RowShape) (j k : Fin 24) : Q12 :=
  (s.quadratic.map fun t =>
    let v := termCoefficient j k t.1 t.2.1
    if v=0 then 0 else quadraticScale (Q12.lit 1 0 0 0 2) s * (t.2.2 : Q12) * v).sum

noncomputable def shapeUnscaled (s : RowShape) (j k : Fin 24) : ℂ :=
  (s.quadratic.map fun t => (t.2.2 : ℂ) * Q12.toComplex (termCoefficient j k t.1 t.2.1)).sum

theorem rationalShapeCoefficient_image (s : RowShape) (j k : Fin 24) :
    Q12.toComplex (rationalShapeCoefficient s j k) =
      quadraticScale (1/2 : ℂ) s * shapeUnscaled s j k := by
  unfold rationalShapeCoefficient shapeUnscaled
  rw [map_list_sum,← List.sum_map_mul_left]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  by_cases h : termCoefficient j k t.1 t.2.1=0
  · simp [h]
  · simp only [h,↓reduceIte,map_mul,map_intCast]
    have hs : Q12.toComplex (quadraticScale (Q12.lit 1 0 0 0 2) s) =
        quadraticScale (1/2 : ℂ) s := by
      simp [quadraticScale,apply_ite Q12.toComplex,Equilibrium.halfQ12_complex]
    rw [hs]
    ring

theorem integerShapeCoefficient_image (s : RowShape) (j k : Fin 24) :
    integerImage ((s.quadratic.map fun t =>
      integerScale t.2.2 (integerTermCoefficient j k t.1 t.2.1)).sum) =
      (denominator : ℂ)^2 * shapeUnscaled s j k := by
  unfold shapeUnscaled
  rw [map_list_sum,← List.sum_map_mul_left]
  simp only [List.map_map,Function.comp_def,integerImage_scale,integerTermCoefficient_image]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  ring

theorem integerImage_skipRow (n : ℤ) (w v : Coeff) :
    integerImage (if v=0 then 0 else integerScale n (integerMul w v)) =
      (n : ℂ) * integerImage w * integerImage v := by
  by_cases h : v=0 <;> simp [h,integerImage_scale,integerImage_mul,mul_assoc]

theorem rowContribution_image (d : Nat) (sH : HSpec) (j k : Fin 24)
    (e : NativeH.Entry) (hd : e.coefficient.denominator ∣ d) :
    integerImage (integerRowContribution d sH j k e) =
      (2*(d : ℂ)*(denominator : ℂ)^2) *
        (orientedValue sH e.coefficient *
          Q12.toComplex (rationalShapeCoefficient (labelShape e.label) j k)) := by
  unfold integerRowContribution
  rw [integerImage_skipRow,integerImage_oriented,integerShapeCoefficient_image,
    rationalShapeCoefficient_image]
  have hd' : ((d/e.coefficient.denominator : Nat) : ℂ) *
      (e.coefficient.denominator : ℂ) = d := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hs : ((if (labelShape e.label).halfScaled then 1 else 2 : ℤ) : ℂ) =
      2 * quadraticScale (1/2 : ℂ) (labelShape e.label) := by
    cases h : (labelShape e.label).halfScaled <;> norm_num [quadraticScale,h]
  simp only [Int.cast_mul,Int.cast_natCast]
  rw [hs]
  linear_combination
    (2 * quadraticScale (1/2 : ℂ) (labelShape e.label) *
      orientedValue sH e.coefficient * (denominator : ℂ)^2 *
      shapeUnscaled (labelShape e.label) j k) * hd'

theorem q12_skipRow (w v : Q12) : (if v=0 then 0 else w*v) = w*v := by
  by_cases h : v=0 <;> simp [h]

theorem integerNativeCoefficient_image (i : Fin 4) (a : Fin 3) (j k : Fin 24) :
    integerImage (integerNativeCoefficient i a j k) =
      (integerFullScale i a : ℂ) * Q12.toComplex (nativeCoefficient i a j k) := by
  have hn : nativeCoefficient i a j k =
      ((rawEntries i a).map fun e => orientedQ12 (hSpec i a) e.coefficient *
        rationalShapeCoefficient (labelShape e.label) j k).sum := by
    unfold nativeCoefficient
    apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    exact q12_skipRow _ _
  rw [integerNative_eq_fullChunk,integerChunk_eq_rowSum,map_list_sum,hn,map_list_sum]
  simp only [List.map_map,Function.comp_def,map_mul,orientedQ12_toComplex]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  rw [rowContribution_image _ _ _ _ _ (commonDenominator_dvd i a e he)]
  congr 1
  simp only [integerFullScale,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem integerBookCoefficient_image (i : Fin 4) (a : Fin 3) (j k : Fin 24) :
    integerImage (integerBookCoefficient i a j k) =
      (integerFullScale i a : ℂ) * Q12.toComplex (bookCoefficient i a j k) := by
  unfold integerBookCoefficient bookCoefficient integerBookTerms bookTerms
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp [integerImage,integerQ12,Q12.toComplex_apply,apply_ite Q12.toComplex]

/-- Exact denominator clearing is reversible; no coefficient equality is assumed
by the representation itself. -/
theorem nativeCoefficient_eq_of_integer (i : Fin 4) (a : Fin 3) (j k : Fin 24)
    (h : integerNativeCoefficient i a j k = integerBookCoefficient i a j k) :
    nativeCoefficient i a j k = bookCoefficient i a j k := by
  apply Q12.toComplex_injective
  have he := congrArg integerImage h
  rw [integerNativeCoefficient_image,integerBookCoefficient_image] at he
  exact mul_left_cancel₀ (integerFullScale_complex_ne_zero i a) he

end Option2.NativeStress.NativeH.Reproduction

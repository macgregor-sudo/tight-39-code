module

public import NativeHIntegerChunks
public import NativeHScalarCoefficient
public import NativeHQuadraticRestriction

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped ComplexConjugate
open BookHT.TangentCoordinates QuarticCertificate.RowBridge

def integerQ12 (x : Coeff) : Q12 := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩

theorem integerQ12_mul (x y : Coeff) :
    integerQ12 (integerMul x y) = integerQ12 x * integerQ12 y := by
  ext <;> simp [integerQ12, integerMul] <;> ring

theorem integerQ12_scale (n : ℤ) (x : Coeff) :
    integerQ12 (integerScale n x) = (n : Q12) * integerQ12 x := by
  ext <;> simp [integerQ12, integerScale]

noncomputable def integerImage : Coeff →+ ℂ where
  toFun x := Q12.toComplex (integerQ12 x)
  map_zero' := by simp [integerQ12, Q12.toComplex_apply]
  map_add' x y := by simp [integerQ12, Q12.toComplex_apply]; ring

theorem integerImage_mul (x y : Coeff) :
    integerImage (integerMul x y) = integerImage x * integerImage y := by
  change Q12.toComplex (integerQ12 (integerMul x y)) = _
  rw [integerQ12_mul, map_mul]
  rfl

theorem integerImage_scale (n : ℤ) (x : Coeff) :
    integerImage (integerScale n x) = (n : ℂ) * integerImage x := by
  change Q12.toComplex (integerQ12 (integerScale n x)) = _
  rw [integerQ12_scale, map_mul, map_intCast]
  rfl

theorem integerImage_conj (x : Coeff) :
    integerImage (integerConj x) = conj (integerImage x) := by
  change Q12.toComplex (integerQ12 (integerConj x)) = _
  have h : integerQ12 (integerConj x) = Q12.conj (integerQ12 x) := by
    ext <;> simp [integerQ12,integerConj,Q12.conj]
  rw [h,Q12.toComplex_conj]
  rfl

theorem integerImage_literal (c : Literal) :
    integerImage (integerLiteral c) = (c.denominator : ℂ) * c.toComplex := by
  have hn : (c.denominator : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt c.denominator_pos)
  simp only [integerImage, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    integerQ12, integerLiteral, Q12.toComplex_apply, Literal.toComplex]
  push_cast
  field_simp

theorem integerImage_oriented (s : HSpec) (c : Literal) :
    integerImage (integerOriented s c) = (c.denominator : ℂ) * orientedValue s c := by
  cases hc : s.conjugated <;> cases hn : s.negated <;>
    simp [integerOriented, orientedValue, hc, hn, integerImage_conj, integerImage_literal]

theorem integerImage_coefficient (q : Coeff) :
    integerImage q = (denominator : ℂ) * coefficient q := by
  exact integerImage_literal ⟨q.1,q.2.1,q.2.2.1,q.2.2.2,denominator,by decide⟩

theorem integerColumnValue_image (es : List BookHT.TangentCoordinates.Entry) (r : Fin 1053) :
    integerImage (integerColumnValue es r) = (denominator : ℂ) * sparseValue es r := by
  induction es with
  | nil => simp [integerColumnValue,sparseValue]
  | cons e es ih =>
      by_cases h : r=e.1
      · rw [integerColumnValue,if_pos h,sparseValue,if_pos h,map_add,
          integerImage_coefficient,ih,mul_add]
      · simp only [integerColumnValue,sparseValue,if_neg h,zero_add,ih]

theorem integerColumn_image (b : Fin 24) (r : Fin 1053) :
    integerImage (integerColumn b r) =
      (denominator : ℂ) * Q12.toComplex (columnQ12 b r) := by
  rw [columnQ12_eq,d6ColumnQ12_complex]
  exact integerColumnValue_image (d6Entries b) r

theorem integerImage_skipMul (x y : Coeff) :
    integerImage (if x=0 then 0 else if y=0 then 0 else integerMul x y) =
      integerImage x * integerImage y := by
  by_cases hx : x=0 <;> by_cases hy : y=0 <;>
    simp [hx,hy,integerImage_mul]

theorem integerTermCoefficient_image (j k : Fin 24) (p q : Fin 1053) :
    integerImage (integerTermCoefficient j k p q) =
      (denominator : ℂ)^2 * Q12.toComplex (termCoefficient j k p q) := by
  by_cases h : j=k <;>
    simp only [integerTermCoefficient,termCoefficient,h,↓reduceIte,
      map_add,map_zero,add_zero,integerImage_skipMul,integerColumn_image,
      nonzeroProduct_eq,map_mul] <;> ring

theorem denominator_dvd_fold (es : List NativeH.Entry) (e : NativeH.Entry) (he : e ∈ es) :
    e.coefficient.denominator ∣ (es.map fun e => e.coefficient.denominator).foldr Nat.lcm 1 := by
  induction es with
  | nil => simp at he
  | cons x xs ih =>
      simp only [List.map_cons,List.foldr_cons]
      rcases List.mem_cons.mp he with h | h
      · subst e
        exact Nat.dvd_lcm_left _ _
      · exact Nat.dvd_trans (ih h) (Nat.dvd_lcm_right _ _)

theorem denominator_fold_pos (es : List NativeH.Entry) :
    0 < (es.map fun e => e.coefficient.denominator).foldr Nat.lcm 1 := by
  induction es with
  | nil => decide
  | cons e es ih => exact Nat.lcm_pos e.coefficient.denominator_pos ih

theorem commonDenominator_pos (i : Fin 4) (a : Fin 3) : 0 < commonDenominator i a :=
  denominator_fold_pos (rawEntries i a)

theorem commonDenominator_dvd (i : Fin 4) (a : Fin 3) (e : NativeH.Entry)
    (he : e ∈ rawEntries i a) : e.coefficient.denominator ∣ commonDenominator i a :=
  denominator_dvd_fold _ e he

theorem integerFullScale_pos (i : Fin 4) (a : Fin 3) : 0 < integerFullScale i a := by
  unfold integerFullScale
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (commonDenominator_pos i a))
    (by decide)) (by decide)

theorem integerFullScale_complex_ne_zero (i : Fin 4) (a : Fin 3) :
    (integerFullScale i a : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (integerFullScale_pos i a)

end Option2.NativeStress.NativeH.Reproduction

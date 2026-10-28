module

public import PointStructure
public import Q12Consts
public import PointQ12Check

/-!
# P2: exact literal form of the accepted point and its complex bridge

`pointQ12 i k` reads the literal table (`Q12.lit`).
`pointQ12_eq_shape` is ONE kernel evaluation of the ring-generic shape over
the computable ring Q12 against the 1053 literals. `consts_bridge` is the
only real/complex arithmetic: 15 scalar facts (1/3, Re/Im of 1, ω, ω², and
of the four rational phases). Then `point_bridge` follows from
`complex_coords` and `shape_map` with no per-point work.
First-party composition, no borrowed text.
-/

@[expose] public section
noncomputable section

namespace FourSheets.PointQ12

open FourSheets.PointShape FourSheets.PointStructure NativePolynomial
open QuadraticCertificate.ExactCKMConfiguration
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

def pointRows : List (List Q12) :=
  [point_00, point_01, point_02, point_03, point_04, point_05, point_06, point_07, point_08,
   point_09, point_10, point_11, point_12, point_13, point_14, point_15, point_16, point_17,
   point_18, point_19, point_20, point_21, point_22, point_23, point_24, point_25, point_26,
   point_27, point_28, point_29, point_30, point_31, point_32, point_33, point_34, point_35,
   point_36, point_37, point_38]

/-- The literal exact point: point `i`, native coordinate `k`. -/
def pointQ12 (i : Fin 39) (k : Fin 27) : Q12 := (pointRows.getD i.val []).getD k.val 0

/-- The literal table IS the generic shape evaluated over Q12 (kernel computation). -/
theorem getD_of_ofFn {n : ℕ} (f : Fin n → Q12) (l : List Q12) (h : List.ofFn f = l)
    (k : Fin n) : l.getD k.val 0 = f k := by
  subst h; simp

theorem pointQ12_eq_shape (i : Fin 39) (k : Fin 27) : pointQ12 i k = shape q12Consts i k := by
  fin_cases i
  · exact getD_of_ofFn _ _ shape_row_00 k
  · exact getD_of_ofFn _ _ shape_row_01 k
  · exact getD_of_ofFn _ _ shape_row_02 k
  · exact getD_of_ofFn _ _ shape_row_03 k
  · exact getD_of_ofFn _ _ shape_row_04 k
  · exact getD_of_ofFn _ _ shape_row_05 k
  · exact getD_of_ofFn _ _ shape_row_06 k
  · exact getD_of_ofFn _ _ shape_row_07 k
  · exact getD_of_ofFn _ _ shape_row_08 k
  · exact getD_of_ofFn _ _ shape_row_09 k
  · exact getD_of_ofFn _ _ shape_row_10 k
  · exact getD_of_ofFn _ _ shape_row_11 k
  · exact getD_of_ofFn _ _ shape_row_12 k
  · exact getD_of_ofFn _ _ shape_row_13 k
  · exact getD_of_ofFn _ _ shape_row_14 k
  · exact getD_of_ofFn _ _ shape_row_15 k
  · exact getD_of_ofFn _ _ shape_row_16 k
  · exact getD_of_ofFn _ _ shape_row_17 k
  · exact getD_of_ofFn _ _ shape_row_18 k
  · exact getD_of_ofFn _ _ shape_row_19 k
  · exact getD_of_ofFn _ _ shape_row_20 k
  · exact getD_of_ofFn _ _ shape_row_21 k
  · exact getD_of_ofFn _ _ shape_row_22 k
  · exact getD_of_ofFn _ _ shape_row_23 k
  · exact getD_of_ofFn _ _ shape_row_24 k
  · exact getD_of_ofFn _ _ shape_row_25 k
  · exact getD_of_ofFn _ _ shape_row_26 k
  · exact getD_of_ofFn _ _ shape_row_27 k
  · exact getD_of_ofFn _ _ shape_row_28 k
  · exact getD_of_ofFn _ _ shape_row_29 k
  · exact getD_of_ofFn _ _ shape_row_30 k
  · exact getD_of_ofFn _ _ shape_row_31 k
  · exact getD_of_ofFn _ _ shape_row_32 k
  · exact getD_of_ofFn _ _ shape_row_33 k
  · exact getD_of_ofFn _ _ shape_row_34 k
  · exact getD_of_ofFn _ _ shape_row_35 k
  · exact getD_of_ofFn _ _ shape_row_36 k
  · exact getD_of_ofFn _ _ shape_row_37 k
  · exact getD_of_ofFn _ _ shape_row_38 k

private theorem s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

private theorem omega_eq : omega = ⟨-1/2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext <;> simp [omega]

private theorem omega_sq_eq : omega ^ 2 = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  rw [omega_eq, pow_two]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith [s3]

private theorem char0 : character 0 = 1 := by simp [character]
private theorem char1 : character 1 = omega := by
  rw [character, show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one]
private theorem char2 : character 2 = ⟨-1/2, -(Real.sqrt 3 / 2)⟩ := by
  rw [character, show ZMod.val (2 : ZMod 3) = 2 from rfl, omega_sq_eq]

/-- The 15 scalar facts. -/
theorem consts_bridge : realConsts.map Complex.ofRealHom = q12Consts.map Q12.toComplex := by
  simp only [Consts.map, realConsts, q12Consts, Consts.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Q12.toComplex_lit]
  all_goals funext r
  · rcases (by decide : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2) r with rfl | rfl | rfl <;>
      (simp [char0, char1, char2, omega_eq, Q12.toComplex_lit, charReQ, charImQ,
        phaseReQ, phaseImQ, exactPhases, Complex.div_re, Complex.div_im] <;>
      first | ring | norm_num | skip)
  · rcases (by decide : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2) r with rfl | rfl | rfl <;>
      (simp [char0, char1, char2, omega_eq, Q12.toComplex_lit, charReQ, charImQ,
        phaseReQ, phaseImQ, exactPhases, Complex.div_re, Complex.div_im] <;>
      first | ring | norm_num | skip)
  · fin_cases r <;>
      (simp [char0, char1, char2, omega_eq, Q12.toComplex_lit, charReQ, charImQ,
        phaseReQ, phaseImQ, exactPhases, Complex.div_re, Complex.div_im] <;>
      first | ring | norm_num | skip)
  · fin_cases r <;>
      (simp [char0, char1, char2, omega_eq, Q12.toComplex_lit, charReQ, charImQ,
        phaseReQ, phaseImQ, exactPhases, Complex.div_re, Complex.div_im] <;>
      first | ring | norm_num | skip)

/-- P2 bridge: the accepted real point's coordinates, complexified, are the literals. -/
theorem point_bridge (i : Fin 39) (k : Fin 27) :
    ((upperCoordinates (nativePoint i) k : ℝ) : ℂ) = Q12.toComplex (pointQ12 i k) := by
  rw [complex_coords, consts_bridge, ← shape_map, pointQ12_eq_shape]

/-- The consumer's point `P` in literal form (`finProdFinEquiv` convention: `v ↦ (v / 27, v % 27)`). -/
theorem P_literal :
    (fun v : Fin 1053 => ((pointCoordinates v : ℝ) : ℂ)) =
      fun v => Q12.toComplex (pointQ12 (v : Fin (39 * 27)).divNat (v : Fin (39 * 27)).modNat) := by
  funext v
  exact point_bridge _ _

theorem P_literal_index (i : Fin 39) (k : Fin 27) :
    ((pointCoordinates (NativePolynomial.ConfigurationResiduals.variableIndex i k) : ℝ) : ℂ) =
      Q12.toComplex (pointQ12 i k) := by
  have h := congrFun (pointValues_pointCoordinates i) k
  simp only [NativePolynomial.ConfigurationResiduals.MixedCoefficients.pointValues] at h
  rw [h]
  exact point_bridge i k

end FourSheets.PointQ12

#print axioms FourSheets.PointQ12.pointQ12_eq_shape
#print axioms FourSheets.PointQ12.consts_bridge
#print axioms FourSheets.PointQ12.point_bridge
#print axioms FourSheets.PointQ12.P_literal
#print axioms FourSheets.PointQ12.P_literal_index

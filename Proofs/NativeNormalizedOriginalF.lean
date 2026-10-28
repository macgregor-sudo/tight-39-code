module

public import NativeNormalizedProjectiveFamily
public import NativeActualPointPartialPreservation

@[expose] public section

/-!
Literal original-F binding of the existing normalized projective construction.
The first twelve points are the original nativePoint values; the remaining
points keep the fixed forward labels 12+3*r+k. The accepted original-equation
bridge supplies all 2184 residual rows without a new finite certificate.
No validity hypothesis, coordinate formula, quotient, or analytic immersion is
added. Dependencies and this composition retain their recorded evidence levels.

First-party composition of the named native owners; no upstream proof copied.
Imported provenance/notices remain with their owners. Thanks to the contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert

open scoped BigOperators
open UnitaryErrorBases.ThreeCycleNormalized
open NativePolynomial NativePolynomial.CoordinateMaps
open NativePolynomial.ConfigurationResiduals NativePolynomial.PartialAction
open QuadraticCertificate QuadraticCertificate.ExactCKMConfiguration

/-- The actual 39 native points, with the original twelve anchors unchanged. -/
def nativeNormalizedProjectivePoint
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (i : Fin 39) : Glennie.Albert :=
  if hi : i.val < 12 then nativePoint i else
    nativeCentralTriple
      (nativeNormalizedProjectiveArray x ⟨i.val / 3 - 4, by omega⟩)
      ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

/-- The same points in the original full upper-coordinate configuration space. -/
def nativeNormalizedProjectiveConfiguration
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) : Configuration ℝ :=
  fun i => upperCoordinates (nativeNormalizedProjectivePoint x i)

theorem nativeNormalizedProjectivePoint_anchor
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle))
    (i : Fin 39) (hi : i.val < 12) :
    nativeNormalizedProjectivePoint x i = nativePoint i := by
  simp only [nativeNormalizedProjectivePoint, dite_eq_left hi]

theorem nativeNormalizedProjectiveConfiguration_anchor
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle))
    (i : Fin 39) (hi : i.val < 12) :
    nativeNormalizedProjectiveConfiguration x i = upperCoordinates (nativePoint i) := by
  rw [nativeNormalizedProjectiveConfiguration, nativeNormalizedProjectivePoint_anchor x i hi]

/-- The exact original labels, including the fixed outcome order. -/
theorem nativeNormalizedProjectivePoint_completion
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (r : Fin 9) (k : Fin 3) :
    nativeNormalizedProjectivePoint x ⟨12 + 3 * r.val + k.val, by omega⟩ =
      nativeCentralTriple (nativeNormalizedProjectiveArray x r) k := by
  have hi : ¬ 12 + 3 * r.val + k.val < 12 := by omega
  have hr : (⟨(12 + 3 * r.val + k.val) / 3 - 4, by omega⟩ : Fin 9) = r := by
    apply Fin.ext
    change (12 + 3 * r.val + k.val) / 3 - 4 = r.val
    omega
  have hk : (⟨(12 + 3 * r.val + k.val) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = k := by
    apply Fin.ext
    change (12 + 3 * r.val + k.val) % 3 = k.val
    omega
  simp only [nativeNormalizedProjectivePoint, dite_eq_right hi]
  rw [hr, hk]

/-- The remaining 27 coordinate values are precisely the frozen native family. -/
theorem nativeNormalizedProjectiveConfiguration_completion
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (r : Fin 9) (k : Fin 3) :
    nativeNormalizedProjectiveConfiguration x ⟨12 + 3 * r.val + k.val, by omega⟩ =
      nativeNormalizedProjectiveFamily x r k := by
  rw [nativeNormalizedProjectiveConfiguration, nativeNormalizedProjectivePoint_completion]
  rfl

/-- All thirteen native frames, at the original frame/outcome labels. -/
theorem nativeNormalizedProjectivePoint_frames
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (f : Fin 13) :
    Glennie.Frame (fun k => nativeNormalizedProjectivePoint x (framePointIndex f k)) := by
  by_cases hf : f.val < 4
  · have hp : (fun k => nativeNormalizedProjectivePoint x (framePointIndex f k)) =
        (fun k => nativePoint (framePointIndex f k)) := by
      funext k
      apply nativeNormalizedProjectivePoint_anchor
      rw [framePointIndex_val]
      omega
    rw [hp]
    exact ExactCKMAllFrames.nativePoint_all_frames f
  · let r : Fin 9 := ⟨f.val - 4, by omega⟩
    have hp : (fun k => nativeNormalizedProjectivePoint x (framePointIndex f k)) =
        nativeCentralTriple (nativeNormalizedProjectiveArray x r) := by
      funext k
      have hi : framePointIndex f k = (⟨12 + 3 * r.val + k.val, by omega⟩ : Fin 39) := by
        apply Fin.ext
        rw [framePointIndex_val]
        dsimp only [r]
        omega
      rw [hi, nativeNormalizedProjectivePoint_completion]
    rw [hp]
    exact ((nativeNormalizedProjectiveFamily_actual_nine_frames x).1 r).1

private theorem point_idempotent
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (i : Fin 39) :
    Glennie.jordan (nativeNormalizedProjectivePoint x i)
      (nativeNormalizedProjectivePoint x i) = nativeNormalizedProjectivePoint x i := by
  let f : Fin 13 := ⟨i.val / 3, by omega⟩
  let k : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
  have hi : framePointIndex f k = i := by
    apply Fin.ext
    rw [framePointIndex_val]
    dsimp only [f, k]
    omega
  simpa only [hi] using (nativeNormalizedProjectivePoint_frames x f).idempotent k

private theorem point_trace
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (i : Fin 39) :
    Glennie.trace (nativeNormalizedProjectivePoint x i) = 1 := by
  let f : Fin 13 := ⟨i.val / 3, by omega⟩
  let k : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
  have hi : framePointIndex f k = i := by
    apply Fin.ext
    rw [framePointIndex_val]
    dsimp only [f, k]
    omega
  simpa only [hi] using (nativeNormalizedProjectivePoint_frames x f).trace_one k

/-- The literal four branches of original F, derived with no solution premise. -/
theorem nativeNormalizedProjectiveConfiguration_originalEquations
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) :
    OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ)
      (nativeNormalizedProjectiveConfiguration x) := by
  have hbase := (originalEquations_iff_all_fRows (1/2 : ℝ) (1/3 : ℝ)
    Actual.actualConfiguration).mpr Actual.actual_input_all_fRows
  have hnine := nativeNormalizedProjectiveFamily_actual_nine_frames x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rw [nativeNormalizedProjectiveConfiguration, product_half_native,
      fromUpperCoordinates_upperCoordinates, point_idempotent]
  · intro i
    rw [nativeNormalizedProjectiveConfiguration, trace_upper_native, point_trace]
  · intro f
    have hs := congrArg upperCoordinates
      (nativeNormalizedProjectivePoint_frames x f).sum_unit
    simpa only [upperCoordinates_add, upper_unit_native,
      Fin.sum_univ_three, nativeNormalizedProjectiveConfiguration] using hs
  · intro ij
    let i := ij.val.1
    let j := ij.val.2
    have hij : i.val < j.val := ij.property
    change coordinatePairing (nativeNormalizedProjectiveConfiguration x i)
      (nativeNormalizedProjectiveConfiguration x j) =
      if i.val / 3 = j.val / 3 then 0 else (1/3 : ℝ)
    by_cases hi : i.val < 12
    · by_cases hj : j.val < 12
      · simpa only [nativeNormalizedProjectiveConfiguration_anchor x i hi,
          nativeNormalizedProjectiveConfiguration_anchor x j hj,
          Actual.actualConfiguration] using hbase.pair ij
      · have hframe : i.val / 3 ≠ j.val / 3 := by omega
        rw [ite_eq_right hframe, nativeNormalizedProjectiveConfiguration_anchor x i hi,
          nativeNormalizedProjectiveConfiguration, pairing_decode_native,
          fromUpperCoordinates_upperCoordinates, fromUpperCoordinates_upperCoordinates,
          nativeNormalizedProjectivePoint, dite_eq_right hj, Glennie.jordan_comm]
        exact (hnine.1 _).2 _ i hi
    · have hj : ¬ j.val < 12 := by omega
      rw [nativeNormalizedProjectiveConfiguration, nativeNormalizedProjectiveConfiguration,
        pairing_decode_native, fromUpperCoordinates_upperCoordinates,
        fromUpperCoordinates_upperCoordinates, nativeNormalizedProjectivePoint,
        nativeNormalizedProjectivePoint, dite_eq_right hi, dite_eq_right hj]
      by_cases hf : i.val / 3 = j.val / 3
      · rw [ite_eq_left hf]
        have hr : (⟨i.val / 3 - 4, by omega⟩ : Fin 9) = ⟨j.val / 3 - 4, by omega⟩ := by
          apply Fin.ext
          change i.val / 3 - 4 = j.val / 3 - 4
          omega
        rw [hr]
        have hk : (⟨i.val % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) ≠
            ⟨j.val % 3, Nat.mod_lt _ (by decide)⟩ := by
          intro h
          have hv := congrArg Fin.val h
          change i.val % 3 = j.val % 3 at hv
          omega
        rw [((hnine.1 _).1).orthogonal _ _ hk]
        exact map_zero Glennie.traceLinear
      · rw [ite_eq_right hf]
        apply hnine.2
        intro h
        have hv := congrArg Fin.val h
        change i.val / 3 - 4 = j.val / 3 - 4 at hv
        omega

/-- Every original numbered polynomial, using exactly the accepted row numbering. -/
theorem nativeNormalizedProjectiveConfiguration_all_original_F
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (r : Fin 2184) :
    MvPolynomial.eval (pack (nativeNormalizedProjectiveConfiguration x))
      (fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0 :=
  (originalEquations_iff_all_fRows (1/2 : ℝ) (1/3 : ℝ) _).mp
    (nativeNormalizedProjectiveConfiguration_originalEquations x) r

end CompactAlbert

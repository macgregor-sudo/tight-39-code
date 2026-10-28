module

public import NativeHIntegerCompute

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open QuarticCertificate.RowBridge
open BookHT.TangentCoordinates

/-- The denominator is an explicit fixed input. Splitting the entry list never
recomputes or replaces the full-list denominator. -/
noncomputable def integerChunkCoefficient (d : Nat) (sH : HSpec)
    (es : List NativeH.Entry) (j k : Fin 24) : Coeff :=
  (es.map fun e =>
    let s := labelShape e.label
    let v := (s.quadratic.map fun t =>
      integerScale t.2.2 (integerTermCoefficient j k t.1 t.2.1)).sum
    if v = 0 then 0 else
      integerScale ((d / e.coefficient.denominator : Nat) *
        (if s.halfScaled then 1 else 2))
        (integerMul (integerOriented sH e.coefficient) v)).sum

theorem integerChunk_append (d : Nat) (sH : HSpec) (xs ys : List NativeH.Entry)
    (j k : Fin 24) :
    integerChunkCoefficient d sH (xs++ys) j k =
      integerChunkCoefficient d sH xs j k + integerChunkCoefficient d sH ys j k := by
  simp only [integerChunkCoefficient, List.map_append, List.sum_append]

theorem integerNative_eq_fullChunk (i : Fin 4) (a : Fin 3) (j k : Fin 24) :
    integerNativeCoefficient i a j k =
      integerChunkCoefficient (commonDenominator i a) (hSpec i a) (rawEntries i a) j k := rfl

theorem integerNative_split (i : Fin 4) (a : Fin 3) (j k : Fin 24) (n : Nat) :
    integerNativeCoefficient i a j k =
      integerChunkCoefficient (commonDenominator i a) (hSpec i a) ((rawEntries i a).take n) j k +
      integerChunkCoefficient (commonDenominator i a) (hSpec i a) ((rawEntries i a).drop n) j k := by
  rw [← integerChunk_append, List.take_append_drop, ← integerNative_eq_fullChunk]

end Option2.NativeStress.NativeH.Reproduction

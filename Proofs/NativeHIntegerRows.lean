module

public import NativeHIntegerChunks

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open QuarticCertificate.RowBridge BookHT.TangentCoordinates

noncomputable def integerRowContribution (d : Nat) (sH : HSpec)
    (j k : Fin 24) (e : NativeH.Entry) : Coeff :=
  let s := labelShape e.label
  let v := (s.quadratic.map fun t =>
    integerScale t.2.2 (integerTermCoefficient j k t.1 t.2.1)).sum
  if v = 0 then 0 else
    integerScale ((d / e.coefficient.denominator : Nat) * (if s.halfScaled then 1 else 2))
      (integerMul (integerOriented sH e.coefficient) v)

theorem integerChunk_eq_rowSum (d : Nat) (sH : HSpec) (es : List NativeH.Entry)
    (j k : Fin 24) :
    integerChunkCoefficient d sH es j k = (es.map (integerRowContribution d sH j k)).sum := rfl

theorem integerChunk_cons (d : Nat) (sH : HSpec) (e : NativeH.Entry)
    (es : List NativeH.Entry) (j k : Fin 24) :
    integerChunkCoefficient d sH (e::es) j k =
      integerRowContribution d sH j k e + integerChunkCoefficient d sH es j k := rfl

theorem integerChunk_nil (d : Nat) (sH : HSpec) (j k : Fin 24) :
    integerChunkCoefficient d sH [] j k = 0 := rfl

end Option2.NativeStress.NativeH.Reproduction

module

public import OriginalFAnchorSupportV3

@[expose] public section

/-!
Literal native H input binding only. Source native_covectors.json SHA256:
6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All five integer components and source list order are retained. Positive
denominators are part of the literal type. The transparent interpretation is
(A + B*i + C*sqrt(3) + D*i*sqrt(3))/N in Complex, without a Q12 dependency.
This asserts no cancellation, equilibrium, quadratic reproduction or native R.
-/

noncomputable section

namespace Option2.NativeStress.NativeH

open scoped BigOperators
open ConfigurationResidualIndices

structure Literal where
  A : Int
  B : Int
  C : Int
  D : Int
  denominator : Nat
  denominator_pos : 0 < denominator

def Literal.toComplex (c : Literal) : Complex :=
  ((c.A : Complex) + (c.B : Complex) * Complex.I +
    (c.C : Complex) * ((Real.sqrt 3 : Real) : Complex) +
    (c.D : Complex) * Complex.I * ((Real.sqrt 3 : Real) : Complex)) /
      (c.denominator : Complex)

structure Entry where
  label : FLabel
  coefficient : Literal

def idEntry (p : Fin 39) (k : Fin 27) (c : Literal) : Entry :=
  ⟨fId p k, c⟩

def sumEntry (f : Fin 13) (k : Fin 27) (c : Literal) : Entry :=
  ⟨fSum f k, c⟩

def pairEntry (p q : Fin 39) (hpq : p < q) (c : Literal) : Entry :=
  ⟨fPair ⟨(p,q), hpq⟩, c⟩

def lambda0 : List Entry := [
  idEntry 1 0 ⟨3, 0, 0, -5, 18, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-3, 0, 0, 5, 18, by decide⟩, -- source row 28
  idEntry 1 2 ⟨3, 0, 0, -5, 18, by decide⟩, -- source row 29
  idEntry 2 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 55
  idEntry 2 2 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 56
  idEntry 2 3 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 57
  idEntry 2 4 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 58
  idEntry 3 0 ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 82
  idEntry 3 2 ⟨4, 0, 0, 0, 3, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-2, 0, 0, 0, 3, by decide⟩, -- source row 84
  idEntry 3 4 ⟨0, -3, 1, 0, 6, by decide⟩, -- source row 85
  idEntry 4 0 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 108
  idEntry 4 1 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-1, 0, 0, 1, 2, by decide⟩, -- source row 111
  idEntry 4 4 ⟨0, 3, 1, 0, 3, by decide⟩, -- source row 112
  idEntry 5 0 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 135
  idEntry 5 1 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 136
  idEntry 5 2 ⟨-2, 0, 0, 1, 3, by decide⟩, -- source row 137
  idEntry 5 3 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 138
  idEntry 6 0 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 163
  idEntry 6 2 ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 164
  idEntry 6 3 ⟨15, 0, 0, 13, 18, by decide⟩, -- source row 165
  idEntry 6 4 ⟨0, 3, -1, 0, 6, by decide⟩, -- source row 166
  idEntry 7 0 ⟨9, 0, 0, 11, 36, by decide⟩, -- source row 189
  idEntry 7 1 ⟨9, 0, 0, 11, 36, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-9, 0, 0, -11, 12, by decide⟩, -- source row 191
  idEntry 7 3 ⟨0, 0, 0, -10, 9, by decide⟩, -- source row 192
  idEntry 7 4 ⟨0, -1, -1, 0, 3, by decide⟩, -- source row 193
  idEntry 8 0 ⟨9, 0, 0, -13, 36, by decide⟩, -- source row 216
  idEntry 8 1 ⟨9, 0, 0, -13, 36, by decide⟩, -- source row 217
  idEntry 8 2 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 218
  idEntry 8 3 ⟨0, 0, 0, -4, 9, by decide⟩, -- source row 219
  idEntry 8 4 ⟨0, -2, 0, 0, 3, by decide⟩, -- source row 220
  idEntry 9 0 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 243
  idEntry 9 1 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 244
  idEntry 9 2 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 245
  idEntry 9 3 ⟨21, 0, 0, 23, 36, by decide⟩, -- source row 246
  idEntry 9 4 ⟨0, 15, -1, 0, 12, by decide⟩, -- source row 247
  idEntry 10 0 ⟨3, 0, 0, 5, 36, by decide⟩, -- source row 270
  idEntry 10 1 ⟨3, 0, 0, 5, 36, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-3, 0, 0, -1, 12, by decide⟩, -- source row 272
  idEntry 10 3 ⟨3, 0, 0, -31, 36, by decide⟩, -- source row 273
  idEntry 10 4 ⟨0, 17, 1, 0, 12, by decide⟩, -- source row 274
  idEntry 11 0 ⟨0, 0, 0, -4, 9, by decide⟩, -- source row 297
  idEntry 11 1 ⟨0, 0, 0, -4, 9, by decide⟩, -- source row 298
  idEntry 11 2 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 299
  idEntry 11 3 ⟨9, 0, 0, -13, 36, by decide⟩, -- source row 300
  idEntry 11 4 ⟨0, -5, -5, 0, 12, by decide⟩, -- source row 301
  sumEntry 0 3 ⟨3, 0, 0, 5, 12, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨0, 21, 1, 0, 36, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨-1, 0, 0, -3, 12, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨0, -3, 5, 0, 36, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨3, 0, 0, 1, 36, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨9, 0, 0, 7, 36, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨3, 0, 0, 5, 36, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨0, 3, -1, 0, 36, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨-15, 0, 0, -1, 36, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨0, 15, -5, 0, 36, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨-3, 0, 0, -1, 9, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨0, -3, 1, 0, 18, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨-9, 0, 0, 5, 36, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨-9, 0, 0, 5, 36, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 0, -1, 9, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨3, 0, 0, -4, 9, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨0, 1, 0, 0, 3, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨0, 0, 0, 2, 9, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨0, 1, 1, 0, 6, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨3, 0, 0, 1, 36, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨-9, 0, 0, 5, 36, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨3, 0, 0, 1, 36, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨3, 0, 0, -7, 12, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨0, 7, -1, 0, 12, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨-1, 0, 0, 5, 12, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨0, -1, -1, 0, 6, by decide⟩, -- source row 1193
  pairEntry 0 4 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨-3, 0, 0, -1, 12, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1484
  pairEntry 1 6 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1485
  pairEntry 1 8 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨3, 0, 0, -7, 36, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨3, 0, 0, 2, 9, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨3, 0, 0, -1, 9, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨5, 0, 0, -1, 12, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨-5, 0, 0, 1, 12, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨-3, 0, 0, -1, 12, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨-3, 0, 0, -1, 12, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨-1, 0, 0, -3, 12, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩ -- source row 1721
]

def lambda2 : List Entry := [
  idEntry 0 19 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 19
  idEntry 0 20 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 20
  idEntry 1 0 ⟨-9, 0, 0, 5, 36, by decide⟩, -- source row 27
  idEntry 1 1 ⟨9, 0, 0, -5, 36, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-9, 0, 0, 5, 36, by decide⟩, -- source row 29
  idEntry 2 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 55
  idEntry 2 2 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 56
  idEntry 3 0 ⟨2, 0, 0, 0, 3, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-11, 0, 0, 3, 12, by decide⟩, -- source row 83
  idEntry 3 3 ⟨7, 0, 0, -3, 12, by decide⟩, -- source row 84
  idEntry 3 4 ⟨0, 3, -1, 0, 12, by decide⟩, -- source row 85
  idEntry 4 0 ⟨-1, 0, 0, -2, 6, by decide⟩, -- source row 108
  idEntry 4 1 ⟨2, 0, 0, 1, 6, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 110
  idEntry 4 3 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 111
  idEntry 4 4 ⟨0, 3, -5, 0, 12, by decide⟩, -- source row 112
  idEntry 5 0 ⟨-1, 0, 0, 2, 6, by decide⟩, -- source row 135
  idEntry 5 1 ⟨2, 0, 0, -1, 6, by decide⟩, -- source row 136
  idEntry 5 2 ⟨1, 0, 0, -5, 12, by decide⟩, -- source row 137
  idEntry 5 3 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 138
  idEntry 5 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 139
  idEntry 6 0 ⟨-6, 0, 0, -1, 9, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 163
  idEntry 6 2 ⟨3, 0, 0, 1, 6, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-6, 0, 0, 2, 9, by decide⟩, -- source row 165
  idEntry 6 4 ⟨0, 3, 1, 0, 3, by decide⟩, -- source row 166
  idEntry 7 0 ⟨-9, 0, 0, 23, 36, by decide⟩, -- source row 189
  idEntry 7 1 ⟨9, 0, 0, 5, 36, by decide⟩, -- source row 190
  idEntry 7 2 ⟨9, 0, 0, -11, 12, by decide⟩, -- source row 191
  idEntry 7 3 ⟨9, 0, 0, -23, 18, by decide⟩, -- source row 192
  idEntry 7 4 ⟨0, -5, 1, 0, 6, by decide⟩, -- source row 193
  idEntry 8 0 ⟨27, 0, 0, -13, 36, by decide⟩, -- source row 216
  idEntry 8 1 ⟨-9, 0, 0, -13, 36, by decide⟩, -- source row 217
  idEntry 8 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 218
  idEntry 8 3 ⟨9, 0, 0, 1, 18, by decide⟩, -- source row 219
  idEntry 8 4 ⟨0, -7, 3, 0, 6, by decide⟩, -- source row 220
  idEntry 9 0 ⟨-3, 0, 0, 2, 9, by decide⟩, -- source row 243
  idEntry 9 1 ⟨3, 0, 0, -5, 18, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 245
  idEntry 9 3 ⟨3, 0, 0, -14, 18, by decide⟩, -- source row 246
  idEntry 9 4 ⟨0, 6, 1, 0, 6, by decide⟩, -- source row 247
  idEntry 10 0 ⟨12, 0, 0, 1, 18, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-6, 0, 0, 1, 18, by decide⟩, -- source row 271
  idEntry 10 2 ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 272
  idEntry 10 3 ⟨3, 0, 0, -8, 18, by decide⟩, -- source row 273
  idEntry 10 4 ⟨0, 4, 1, 0, 6, by decide⟩, -- source row 274
  idEntry 11 0 ⟨-6, 0, 0, -4, 9, by decide⟩, -- source row 297
  idEntry 11 1 ⟨-3, 0, 0, 1, 18, by decide⟩, -- source row 298
  idEntry 11 2 ⟨6, 0, 0, -1, 6, by decide⟩, -- source row 299
  idEntry 11 3 ⟨15, 0, 0, -2, 18, by decide⟩, -- source row 300
  idEntry 11 4 ⟨0, 2, -3, 0, 6, by decide⟩, -- source row 301
  sumEntry 0 3 ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨0, 0, -1, 0, 18, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨11, 0, 0, -5, 12, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨0, 9, -1, 0, 36, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨-3, 0, 0, 1, 36, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨0, 0, 0, -1, 18, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨3, 0, 0, -1, 18, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨3, 0, 0, -2, 18, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨0, 0, 1, 0, 18, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨3, 0, 0, -1, 36, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨0, -3, 7, 0, 36, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨3, 0, 0, -1, 9, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨0, 3, 1, 0, 18, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨-3, 0, 0, 5, 36, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨3, 0, 0, -1, 36, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 0, -1, 9, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨3, 0, 0, -4, 9, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨0, 1, 0, 0, 3, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨-3, 0, 0, -1, 9, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨3, 0, 0, 7, 18, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨0, 1, -1, 0, 6, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨0, 0, 0, -1, 18, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨0, 0, 0, 1, 18, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨-3, 0, 0, 2, 18, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨1, 0, 0, -2, 6, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨0, 2, 1, 0, 6, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨0, 1, 0, 0, 3, by decide⟩, -- source row 1193
  pairEntry 0 4 (by decide) ⟨-1, 0, 0, -3, 12, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨-5, 0, 0, 1, 12, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1484
  pairEntry 1 8 (by decide) ⟨-5, 0, 0, 3, 12, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨3, 0, 0, -2, 18, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨-3, 0, 0, 2, 9, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨3, 0, 0, 1, 18, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨-7, 0, 0, 1, 12, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨2, 0, 0, -1, 6, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨-3, 0, 0, 1, 12, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨-2, 0, 0, 1, 6, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩ -- source row 1721
]

def lambda1 : List Entry := [
  idEntry 1 0 ⟨-3, 0, 0, -5, 36, by decide⟩, -- source row 27
  idEntry 1 1 ⟨3, 0, 0, 5, 36, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-3, 0, 0, -5, 36, by decide⟩, -- source row 29
  idEntry 1 11 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 38
  idEntry 1 12 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 39
  idEntry 2 0 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 54
  idEntry 2 1 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 55
  idEntry 2 2 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 56
  idEntry 3 0 ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-2, 0, 0, 0, 3, by decide⟩, -- source row 82
  idEntry 3 2 ⟨5, 0, 0, 3, 12, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-1, 0, 0, -3, 12, by decide⟩, -- source row 84
  idEntry 3 4 ⟨0, -3, 1, 0, 12, by decide⟩, -- source row 85
  idEntry 4 0 ⟨-1, 0, 0, -5, 12, by decide⟩, -- source row 108
  idEntry 4 1 ⟨5, 0, 0, 1, 12, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 111
  idEntry 4 4 ⟨0, 15, -1, 0, 12, by decide⟩, -- source row 112
  idEntry 5 0 ⟨-1, 0, 0, 3, 12, by decide⟩, -- source row 135
  idEntry 5 1 ⟨5, 0, 0, -3, 12, by decide⟩, -- source row 136
  idEntry 5 2 ⟨-7, 0, 0, -1, 12, by decide⟩, -- source row 137
  idEntry 5 3 ⟨-3, 0, 0, -5, 12, by decide⟩, -- source row 138
  idEntry 5 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 139
  idEntry 6 0 ⟨-3, 0, 0, 1, 9, by decide⟩, -- source row 162
  idEntry 6 1 ⟨3, 0, 0, -7, 18, by decide⟩, -- source row 163
  idEntry 6 2 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-15, 0, 0, 5, 18, by decide⟩, -- source row 165
  idEntry 6 4 ⟨0, -9, 1, 0, 6, by decide⟩, -- source row 166
  idEntry 7 0 ⟨9, 0, 0, -4, 18, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-9, 0, 0, -4, 18, by decide⟩, -- source row 190
  idEntry 7 2 ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-9, 0, 0, 17, 18, by decide⟩, -- source row 192
  idEntry 7 4 ⟨0, -1, -1, 0, 6, by decide⟩, -- source row 193
  idEntry 8 0 ⟨-9, 0, 0, 2, 18, by decide⟩, -- source row 216
  idEntry 8 1 ⟨0, 0, 0, 11, 18, by decide⟩, -- source row 217
  idEntry 8 2 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 218
  idEntry 8 3 ⟨9, 0, 0, -1, 18, by decide⟩, -- source row 219
  idEntry 8 4 ⟨0, 1, -3, 0, 6, by decide⟩, -- source row 220
  idEntry 9 0 ⟨9, 0, 0, -7, 18, by decide⟩, -- source row 243
  idEntry 9 1 ⟨9, 0, 0, 1, 9, by decide⟩, -- source row 244
  idEntry 9 2 ⟨-5, 0, 0, -1, 4, by decide⟩, -- source row 245
  idEntry 9 3 ⟨63, 0, 0, -5, 36, by decide⟩, -- source row 246
  idEntry 9 4 ⟨0, -9, 1, 0, 12, by decide⟩, -- source row 247
  idEntry 10 0 ⟨-9, 0, 0, 7, 36, by decide⟩, -- source row 270
  idEntry 10 1 ⟨9, 0, 0, -11, 36, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-3, 0, 0, 1, 12, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-27, 0, 0, 25, 36, by decide⟩, -- source row 273
  idEntry 10 4 ⟨0, -11, 3, 0, 12, by decide⟩, -- source row 274
  idEntry 11 0 ⟨3, 0, 0, 1, 9, by decide⟩, -- source row 297
  idEntry 11 1 ⟨-6, 0, 0, 1, 9, by decide⟩, -- source row 298
  idEntry 11 2 ⟨-3, 0, 0, 5, 12, by decide⟩, -- source row 299
  idEntry 11 3 ⟨-33, 0, 0, 19, 36, by decide⟩, -- source row 300
  idEntry 11 4 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 301
  sumEntry 0 3 ⟨3, 0, 0, -5, 12, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨0, -15, -1, 0, 36, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨-1, 0, 0, 2, 6, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨0, 3, 2, 0, 18, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨0, 0, 0, 1, 18, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨9, 0, 0, 5, 36, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨3, 0, 0, 1, 18, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨9, 0, 0, 1, 36, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨0, 3, 1, 0, 36, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨-6, 0, 0, -1, 18, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨0, 6, 1, 0, 18, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨0, 0, 0, -2, 9, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨0, 0, 1, 0, 9, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨3, 0, 0, -4, 18, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨-3, 0, 0, -4, 18, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨-3, 0, 0, 4, 9, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨0, -1, 0, 0, 3, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨-3, 0, 0, 1, 9, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨0, 0, 0, -5, 9, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨0, 1, 0, 0, 3, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨3, 0, 0, -1, 36, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨9, 0, 0, 1, 36, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨-3, 0, 0, -7, 36, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨-7, 0, 0, 5, 12, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨-1, 0, 0, -5, 12, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨0, 1, -1, 0, 6, by decide⟩, -- source row 1193
  pairEntry 0 4 (by decide) ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨-3, 0, 0, 1, 12, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨-7, 0, 0, -1, 12, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨-1, 0, 0, -3, 12, by decide⟩, -- source row 1484
  pairEntry 1 6 (by decide) ⟨3, 0, 0, 1, 6, by decide⟩, -- source row 1485
  pairEntry 1 8 (by decide) ⟨4, 0, 0, 1, 6, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨-9, 0, 0, 7, 36, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨0, 0, 0, -5, 9, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨-9, 0, 0, -1, 18, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨1, 0, 0, -2, 6, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨-1, 0, 0, 3, 12, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨0, 0, 0, 1, 6, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨-3, 0, 0, 1, 12, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨-5, 0, 0, -1, 12, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨-1, 0, 0, 3, 6, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩ -- source row 1721
]

def lambda22 : List Entry := [
  idEntry 1 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 27
  idEntry 1 1 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 29
  idEntry 2 5 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 59
  idEntry 2 6 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 60
  idEntry 12 0 ⟨-5, 0, 0, 0, 9, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-5, 0, 0, 0, 9, by decide⟩, -- source row 325
  idEntry 12 2 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 326
  idEntry 12 5 ⟨5, 0, 0, 0, 9, by decide⟩, -- source row 329
  idEntry 12 6 ⟨0, 0, 1, 0, 3, by decide⟩, -- source row 330
  idEntry 13 0 ⟨7, 0, 0, 0, 9, by decide⟩, -- source row 351
  idEntry 13 1 ⟨7, 0, 0, 0, 9, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-9, 0, 0, 1, 6, by decide⟩, -- source row 353
  idEntry 13 5 ⟨8, 0, 0, -3, 9, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, 9, -8, 0, 9, by decide⟩, -- source row 357
  idEntry 14 0 ⟨-1, 0, 0, -3, 18, by decide⟩, -- source row 378
  idEntry 14 1 ⟨-1, 0, 0, -3, 18, by decide⟩, -- source row 379
  idEntry 14 2 ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-7, 0, 0, 0, 9, by decide⟩, -- source row 383
  idEntry 14 6 ⟨0, 0, -1, 0, 9, by decide⟩, -- source row 384
  idEntry 15 0 ⟨-3, 0, 0, 1, 18, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-3, 0, 0, 1, 18, by decide⟩, -- source row 406
  idEntry 15 2 ⟨3, 0, 0, 1, 6, by decide⟩, -- source row 407
  idEntry 15 5 ⟨-3, 0, 0, 1, 9, by decide⟩, -- source row 410
  idEntry 15 6 ⟨0, -1, -1, 0, 1, by decide⟩, -- source row 411
  idEntry 16 0 ⟨0, 0, 0, 2, 9, by decide⟩, -- source row 432
  idEntry 16 1 ⟨0, 0, 0, 2, 9, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-9, 0, 0, -7, 6, by decide⟩, -- source row 434
  idEntry 16 5 ⟨0, 0, 0, 4, 9, by decide⟩, -- source row 437
  idEntry 16 6 ⟨0, -4, -2, 0, 3, by decide⟩, -- source row 438
  idEntry 17 0 ⟨6, 0, 0, -1, 9, by decide⟩, -- source row 459
  idEntry 17 1 ⟨6, 0, 0, -1, 9, by decide⟩, -- source row 460
  idEntry 17 2 ⟨-1, 0, 0, 1, 2, by decide⟩, -- source row 461
  idEntry 17 5 ⟨12, 0, 0, 4, 9, by decide⟩, -- source row 464
  idEntry 17 6 ⟨0, -2, 0, 0, 3, by decide⟩, -- source row 465
  idEntry 18 2 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 488
  idEntry 18 5 ⟨-7, 0, 0, 1, 6, by decide⟩, -- source row 491
  idEntry 18 6 ⟨0, 3, 1, 0, 6, by decide⟩, -- source row 492
  idEntry 19 0 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 513
  idEntry 19 1 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 515
  idEntry 19 5 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 518
  idEntry 19 6 ⟨0, 3, 1, 0, 6, by decide⟩, -- source row 519
  idEntry 20 0 ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 540
  idEntry 20 1 ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 541
  idEntry 20 2 ⟨-2, 0, 0, 3, 3, by decide⟩, -- source row 542
  idEntry 20 5 ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 545
  idEntry 20 6 ⟨0, -9, 1, 0, 6, by decide⟩, -- source row 546
  sumEntry 0 5 ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨0, 1, 0, 0, 3, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨0, 0, -1, 0, 9, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨0, -3, 1, 0, 18, by decide⟩, -- source row 1118
  sumEntry 4 0 ⟨-1, 0, 0, 0, 9, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨2, 0, 0, 0, 9, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨-1, 0, 0, 0, 9, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨0, 0, 1, 0, 9, by decide⟩, -- source row 1206
  sumEntry 4 16 ⟨0, 0, 2, 0, 9, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨3, 0, 0, -1, 18, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨-3, 0, 0, -1, 18, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1229
  sumEntry 5 6 ⟨0, 0, -4, 0, 9, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨3, 0, 0, 1, 6, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨0, 9, 5, 0, 18, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1252
  sumEntry 6 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1254
  sumEntry 6 5 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨0, 3, -1, 0, 18, by decide⟩, -- source row 1260
  sumEntry 6 16 ⟨0, 3, -1, 0, 9, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1279
  pairEntry 0 14 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1535
  pairEntry 12 15 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩ -- source row 1953
]

def lambda14 : List Entry := [
  idEntry 1 0 ⟨-1, 0, 0, 3, 6, by decide⟩, -- source row 27
  idEntry 1 1 ⟨1, 0, 0, -3, 6, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-1, 0, 0, 3, 6, by decide⟩, -- source row 29
  idEntry 1 15 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 42
  idEntry 1 16 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 43
  idEntry 12 0 ⟨-13, 0, 0, 1, 18, by decide⟩, -- source row 324
  idEntry 12 1 ⟨5, 0, 0, 1, 18, by decide⟩, -- source row 325
  idEntry 12 5 ⟨13, 0, 0, -1, 18, by decide⟩, -- source row 329
  idEntry 12 6 ⟨0, 3, -1, 0, 6, by decide⟩, -- source row 330
  idEntry 13 0 ⟨1, 0, 0, 2, 9, by decide⟩, -- source row 351
  idEntry 13 1 ⟨-7, 0, 0, -5, 18, by decide⟩, -- source row 352
  idEntry 13 2 ⟨3, 0, 0, 1, 6, by decide⟩, -- source row 353
  idEntry 13 5 ⟨-17, 0, 0, 5, 18, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, 3, -1, 0, 18, by decide⟩, -- source row 357
  idEntry 14 0 ⟨5, 0, 0, -5, 18, by decide⟩, -- source row 378
  idEntry 14 1 ⟨-2, 0, 0, 2, 9, by decide⟩, -- source row 379
  idEntry 14 2 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-11, 0, 0, -1, 18, by decide⟩, -- source row 383
  idEntry 14 6 ⟨0, -3, 1, 0, 18, by decide⟩, -- source row 384
  idEntry 15 0 ⟨9, 0, 0, 7, 18, by decide⟩, -- source row 405
  idEntry 15 1 ⟨0, 0, 0, -1, 9, by decide⟩, -- source row 406
  idEntry 15 5 ⟨-9, 0, 0, -7, 18, by decide⟩, -- source row 410
  idEntry 15 6 ⟨0, -5, -1, 0, 2, by decide⟩, -- source row 411
  idEntry 16 0 ⟨3, 0, 0, -5, 18, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-3, 0, 0, 2, 9, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-3, 0, 0, -4, 3, by decide⟩, -- source row 434
  idEntry 16 5 ⟨15, 0, 0, 5, 18, by decide⟩, -- source row 437
  idEntry 16 6 ⟨0, -11, -3, 0, 6, by decide⟩, -- source row 438
  idEntry 17 0 ⟨-3, 0, 0, 7, 18, by decide⟩, -- source row 459
  idEntry 17 1 ⟨15, 0, 0, 7, 18, by decide⟩, -- source row 460
  idEntry 17 2 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 461
  idEntry 17 5 ⟨21, 0, 0, 23, 18, by decide⟩, -- source row 464
  idEntry 17 6 ⟨0, -1, -1, 0, 6, by decide⟩, -- source row 465
  idEntry 18 0 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 486
  idEntry 18 1 ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 487
  idEntry 18 2 ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 488
  idEntry 18 5 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 491
  idEntry 18 6 ⟨0, 3, 1, 0, 6, by decide⟩, -- source row 492
  idEntry 19 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 513
  idEntry 19 1 ⟨5, 0, 0, 1, 6, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-2, 0, 0, -1, 3, by decide⟩, -- source row 515
  idEntry 19 5 ⟨1, 0, 0, 1, 2, by decide⟩, -- source row 518
  idEntry 19 6 ⟨0, -3, -1, 0, 6, by decide⟩, -- source row 519
  idEntry 20 0 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 540
  idEntry 20 1 ⟨-2, 0, 0, -1, 3, by decide⟩, -- source row 541
  idEntry 20 2 ⟨5, 0, 0, -1, 6, by decide⟩, -- source row 542
  idEntry 20 5 ⟨-3, 0, 0, 1, 6, by decide⟩, -- source row 545
  idEntry 20 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 546
  sumEntry 0 5 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨0, -1, -1, 0, 6, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨0, 3, 1, 0, 18, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨0, -9, 1, 0, 18, by decide⟩, -- source row 1118
  sumEntry 4 0 ⟨1, 0, 0, -1, 18, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨2, 0, 0, 1, 9, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨2, 0, 0, 1, 9, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨0, 3, -1, 0, 18, by decide⟩, -- source row 1206
  sumEntry 4 15 ⟨-2, 0, 0, 0, 3, by decide⟩, -- source row 1215
  sumEntry 4 16 ⟨0, 3, -1, 0, 9, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨0, 0, 0, -2, 9, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1229
  sumEntry 5 5 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1232
  sumEntry 5 6 ⟨0, -15, -5, 0, 18, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨-1, 0, 0, 3, 6, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨0, 15, 5, 0, 18, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1252
  sumEntry 6 0 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1254
  sumEntry 6 1 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1255
  sumEntry 6 5 ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨0, 0, 1, 0, 9, by decide⟩, -- source row 1260
  sumEntry 6 15 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1269
  sumEntry 6 16 ⟨0, 9, 1, 0, 18, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1279
  pairEntry 0 13 (by decide) ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 1455
  pairEntry 0 14 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨1, 0, 0, 1, 3, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨-1, 0, 0, 3, 6, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1535
  pairEntry 12 15 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨-1, 0, 0, -1, 3, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩ -- source row 1953
]

def lambda8 : List Entry := [
  idEntry 0 25 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 25
  idEntry 0 26 ⟨0, -1, 0, 0, 1, by decide⟩, -- source row 26
  idEntry 1 0 ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 27
  idEntry 1 1 ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 29
  idEntry 12 0 ⟨-23, 0, 0, -1, 18, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-5, 0, 0, -1, 18, by decide⟩, -- source row 325
  idEntry 12 2 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 326
  idEntry 12 5 ⟨23, 0, 0, 1, 18, by decide⟩, -- source row 329
  idEntry 12 6 ⟨0, -3, 1, 0, 6, by decide⟩, -- source row 330
  idEntry 13 0 ⟨8, 0, 0, -2, 9, by decide⟩, -- source row 351
  idEntry 13 1 ⟨7, 0, 0, 5, 18, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-3, 0, 0, -1, 3, by decide⟩, -- source row 353
  idEntry 13 5 ⟨-1, 0, 0, 1, 18, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, -21, -17, 0, 18, by decide⟩, -- source row 357
  idEntry 14 0 ⟨2, 0, 0, 4, 9, by decide⟩, -- source row 378
  idEntry 14 1 ⟨-5, 0, 0, -1, 18, by decide⟩, -- source row 379
  idEntry 14 2 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-25, 0, 0, 1, 18, by decide⟩, -- source row 383
  idEntry 14 6 ⟨0, 3, -1, 0, 18, by decide⟩, -- source row 384
  idEntry 15 0 ⟨3, 0, 0, 5, 9, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-3, 0, 0, 1, 18, by decide⟩, -- source row 406
  idEntry 15 2 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 407
  idEntry 15 5 ⟨-3, 0, 0, -2, 9, by decide⟩, -- source row 410
  idEntry 15 6 ⟨0, -1, 0, 0, 1, by decide⟩, -- source row 411
  idEntry 16 0 ⟨-15, 0, 0, 1, 18, by decide⟩, -- source row 432
  idEntry 16 1 ⟨3, 0, 0, 1, 18, by decide⟩, -- source row 433
  idEntry 16 2 ⟨1, 0, 0, -1, 1, by decide⟩, -- source row 434
  idEntry 16 5 ⟨-6, 0, 0, 7, 9, by decide⟩, -- source row 437
  idEntry 16 6 ⟨0, -4, 1, 0, 3, by decide⟩, -- source row 438
  idEntry 17 0 ⟨9, 0, 0, -5, 18, by decide⟩, -- source row 459
  idEntry 17 1 ⟨0, 0, 0, 2, 9, by decide⟩, -- source row 460
  idEntry 17 2 ⟨-3, 0, 0, 1, 6, by decide⟩, -- source row 461
  idEntry 17 5 ⟨0, 0, 0, 7, 9, by decide⟩, -- source row 464
  idEntry 17 6 ⟨0, -2, 1, 0, 3, by decide⟩, -- source row 465
  idEntry 18 0 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 486
  idEntry 18 1 ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 487
  idEntry 18 2 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 488
  idEntry 18 5 ⟨1, 0, 0, -1, 2, by decide⟩, -- source row 491
  idEntry 18 6 ⟨0, 3, -1, 0, 6, by decide⟩, -- source row 492
  idEntry 19 0 ⟨0, 0, 0, 1, 3, by decide⟩, -- source row 513
  idEntry 19 1 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 514
  idEntry 19 2 ⟨2, 0, 0, 0, 3, by decide⟩, -- source row 515
  idEntry 19 5 ⟨-5, 0, 0, 1, 6, by decide⟩, -- source row 518
  idEntry 19 6 ⟨0, 1, 1, 0, 2, by decide⟩, -- source row 519
  idEntry 20 0 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 540
  idEntry 20 2 ⟨5, 0, 0, -1, 3, by decide⟩, -- source row 542
  idEntry 20 5 ⟨-5, 0, 0, 1, 6, by decide⟩, -- source row 545
  idEntry 20 6 ⟨0, 3, -5, 0, 6, by decide⟩, -- source row 546
  sumEntry 0 5 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨0, -1, -1, 0, 6, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨0, -3, -1, 0, 18, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨2, 0, 0, 0, 3, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨0, -3, 1, 0, 9, by decide⟩, -- source row 1118
  sumEntry 4 0 ⟨-1, 0, 0, 1, 18, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨4, 0, 0, -1, 9, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨1, 0, 0, -1, 9, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨0, -3, 1, 0, 18, by decide⟩, -- source row 1206
  sumEntry 4 15 ⟨-2, 0, 0, 0, 3, by decide⟩, -- source row 1215
  sumEntry 4 16 ⟨0, -3, 1, 0, 9, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨3, 0, 0, -1, 18, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨-3, 0, 0, -1, 18, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨0, 0, 0, 1, 9, by decide⟩, -- source row 1229
  sumEntry 5 5 ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1232
  sumEntry 5 6 ⟨0, -3, -1, 0, 18, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨0, 6, -1, 0, 9, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1252
  sumEntry 6 1 ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1255
  sumEntry 6 5 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨0, -3, 1, 0, 18, by decide⟩, -- source row 1260
  sumEntry 6 15 ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1269
  sumEntry 6 16 ⟨0, 3, -1, 0, 18, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1279
  pairEntry 0 13 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1455
  pairEntry 0 14 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-2, 0, 0, 0, 3, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨-1, 0, 0, 1, 3, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨-1, 0, 0, -1, 6, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1535
  pairEntry 12 15 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨-1, 0, 0, 1, 6, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨-1, 0, 0, 0, 3, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨1, 0, 0, 0, 3, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨1, 0, 0, 1, 6, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨1, 0, 0, -1, 3, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨0, 0, 0, -1, 3, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨1, 0, 0, -1, 6, by decide⟩ -- source row 1953
]

def lambda4 : List Entry := [
  idEntry 0 0 ⟨-33, -56, -56, 33, 390, by decide⟩, -- source row 0
  idEntry 0 1 ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 1
  idEntry 0 2 ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 2
  idEntry 0 21 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 21
  idEntry 0 22 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 22
  idEntry 1 0 ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-33, -56, -56, 33, 260, by decide⟩, -- source row 28
  idEntry 1 2 ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 29
  idEntry 21 0 ⟨99, 168, -56, 33, 390, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-99, -168, -56, 33, 390, by decide⟩, -- source row 568
  idEntry 21 2 ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 569
  idEntry 21 7 ⟨290, -20, 56, -33, 325, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-240, 745, 224, -132, 975, by decide⟩, -- source row 575
  idEntry 22 0 ⟨-33, -56, -56, 33, 130, by decide⟩, -- source row 594
  idEntry 22 2 ⟨66, 112, 56, -33, 195, by decide⟩, -- source row 596
  idEntry 22 7 ⟨-99, -168, -468, -26, 975, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-132, -224, -349, 432, 975, by decide⟩, -- source row 602
  idEntry 23 0 ⟨-33, -56, 392, -231, 780, by decide⟩, -- source row 621
  idEntry 23 1 ⟨165, 280, 56, -33, 780, by decide⟩, -- source row 622
  idEntry 23 2 ⟨-231, -392, -168, 99, 780, by decide⟩, -- source row 623
  idEntry 23 7 ⟨-125, 300, -76, -257, 650, by decide⟩, -- source row 628
  idEntry 23 8 ⟨900, 375, 521, 372, 1950, by decide⟩, -- source row 629
  idEntry 24 0 ⟨0, 0, 56, -33, 195, by decide⟩, -- source row 648
  idEntry 24 1 ⟨99, 168, -56, 33, 390, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-33, -56, 0, 0, 195, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-389, -148, -76, -257, 650, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-156, -1417, 521, 372, 1950, by decide⟩, -- source row 656
  idEntry 25 0 ⟨66, 112, 0, 0, 195, by decide⟩, -- source row 675
  idEntry 25 1 ⟨-33, -56, 0, 0, 195, by decide⟩, -- source row 676
  idEntry 25 2 ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-125, 300, -76, -257, 650, by decide⟩, -- source row 682
  idEntry 25 8 ⟨900, 375, 521, 372, 1950, by decide⟩, -- source row 683
  idEntry 26 0 ⟨-66, -112, -56, 33, 195, by decide⟩, -- source row 702
  idEntry 26 1 ⟨-33, -56, 56, -33, 390, by decide⟩, -- source row 703
  idEntry 26 2 ⟨33, 56, -56, 33, 390, by decide⟩, -- source row 704
  idEntry 26 7 ⟨-771, 228, 300, 125, 1950, by decide⟩, -- source row 709
  idEntry 26 8 ⟨372, -521, 125, -300, 1950, by decide⟩, -- source row 710
  idEntry 27 0 ⟨-66, -112, -56, 33, 195, by decide⟩, -- source row 729
  idEntry 27 1 ⟨-33, -56, 56, -33, 390, by decide⟩, -- source row 730
  idEntry 27 2 ⟨99, 168, 56, -33, 390, by decide⟩, -- source row 731
  idEntry 27 7 ⟨-46, 178, 66, 112, 325, by decide⟩, -- source row 736
  idEntry 27 8 ⟨1032, 599, -297, -504, 1950, by decide⟩, -- source row 737
  idEntry 28 0 ⟨-33, -56, 56, -33, 195, by decide⟩, -- source row 756
  idEntry 28 1 ⟨33, 56, -56, 33, 390, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 758
  idEntry 28 7 ⟨-178, -46, 66, 112, 325, by decide⟩, -- source row 763
  idEntry 28 8 ⟨-24, -1193, -297, -504, 1950, by decide⟩, -- source row 764
  idEntry 29 0 ⟨363, 616, -56, 33, 780, by decide⟩, -- source row 783
  idEntry 29 1 ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 784
  idEntry 29 7 ⟨-33, -56, -56, 33, 650, by decide⟩, -- source row 790
  idEntry 29 8 ⟨-66, -112, -112, 66, 975, by decide⟩, -- source row 791
  sumEntry 0 7 ⟨-573, 564, 36, -323, 3900, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨636, -73, 323, 36, 3900, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨10497, -3696, 3696, 2047, 50700, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨-3696, 6403, 2047, -3696, 50700, by decide⟩, -- source row 1114
  sumEntry 7 0 ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨1719, -1692, -636, 73, 5850, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨-636, 73, -191, 188, 1950, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨2181, -908, -148, 389, 5070, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨1332, -3501, 2181, -908, 15210, by decide⟩, -- source row 1299
  sumEntry 8 0 ⟨-33, -56, -56, 33, 390, by decide⟩, -- source row 1308
  sumEntry 8 7 ⟨-375, 900, -264, -448, 2925, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨300, 125, 66, 112, 975, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨-1167, -444, -148, 389, 5070, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨2724, 6543, 2181, -908, 15210, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1335
  sumEntry 9 1 ⟨-33, -56, -56, 33, 390, by decide⟩, -- source row 1336
  sumEntry 9 7 ⟨-323, -36, 188, 191, 1300, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨108, -969, -73, -636, 3900, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨-165, -280, -512, -1509, 5070, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨198, 336, -501, -82, 2535, by decide⟩, -- source row 1353
  pairEntry 0 21 (by decide) ⟨231, 392, -56, 33, 780, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨33, 56, -56, 33, 390, by decide⟩, -- source row 1464
  pairEntry 0 24 (by decide) ⟨0, 0, 56, -33, 195, by decide⟩, -- source row 1466
  pairEntry 0 25 (by decide) ⟨99, 168, 56, -33, 390, by decide⟩, -- source row 1467
  pairEntry 0 27 (by decide) ⟨-33, -56, 0, 0, 195, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨-165, -280, 168, -99, 780, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 1501
  pairEntry 1 27 (by decide) ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 1544
  pairEntry 21 24 (by decide) ⟨-33, -56, -56, 33, 390, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨33, 56, 0, 0, 195, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨-33, -56, 56, -33, 390, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨33, 56, 56, -33, 390, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨-33, -56, 0, 0, 195, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨33, 56, 0, 0, 195, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨-33, -56, 56, -33, 390, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨-33, -56, 0, 0, 195, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨33, 56, -56, 33, 390, by decide⟩ -- source row 2106
]

def lambda25 : List Entry := [
  idEntry 0 0 ⟨3, -4, -4, -3, 15, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-3, 4, 4, 3, 15, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-3, 4, 4, 3, 15, by decide⟩, -- source row 2
  idEntry 1 0 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 27
  idEntry 1 1 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 29
  idEntry 2 7 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 61
  idEntry 2 8 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 62
  idEntry 21 0 ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 568
  idEntry 21 2 ⟨6, -8, 0, 0, 15, by decide⟩, -- source row 569
  idEntry 22 0 ⟨3, -4, 4, 3, 30, by decide⟩, -- source row 594
  idEntry 22 1 ⟨3, -4, 4, 3, 30, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-3, 4, -4, -3, 15, by decide⟩, -- source row 596
  idEntry 23 0 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 621
  idEntry 23 1 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 622
  idEntry 23 2 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 623
  idEntry 23 7 ⟨-57, -24, 24, -7, 150, by decide⟩, -- source row 628
  idEntry 23 8 ⟨24, 43, 7, 24, 150, by decide⟩, -- source row 629
  idEntry 24 0 ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 648
  idEntry 24 1 ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 649
  idEntry 24 2 ⟨6, -8, 0, 0, 15, by decide⟩, -- source row 650
  idEntry 25 0 ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 675
  idEntry 25 1 ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 676
  idEntry 25 2 ⟨-15, 20, 4, 3, 30, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-39, -48, 0, -25, 75, by decide⟩, -- source row 682
  idEntry 25 8 ⟨48, 11, -25, 0, 75, by decide⟩, -- source row 683
  idEntry 26 2 ⟨3, -4, -4, -3, 30, by decide⟩, -- source row 704
  idEntry 26 7 ⟨-57, -24, 24, -7, 75, by decide⟩, -- source row 709
  idEntry 26 8 ⟨24, 43, 7, 24, 75, by decide⟩, -- source row 710
  idEntry 27 0 ⟨-9, 12, 4, 3, 30, by decide⟩, -- source row 729
  idEntry 27 1 ⟨-9, 12, 4, 3, 30, by decide⟩, -- source row 730
  idEntry 27 2 ⟨9, -12, -4, -3, 15, by decide⟩, -- source row 731
  idEntry 27 7 ⟨9, -12, -12, -9, 50, by decide⟩, -- source row 736
  idEntry 27 8 ⟨6, -8, -8, -6, 25, by decide⟩, -- source row 737
  idEntry 28 0 ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 756
  idEntry 28 1 ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-27, 36, 4, 3, 60, by decide⟩, -- source row 758
  idEntry 28 7 ⟨-87, -84, 12, -41, 150, by decide⟩, -- source row 763
  idEntry 28 8 ⟨42, 19, -17, 6, 75, by decide⟩, -- source row 764
  idEntry 29 0 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 783
  idEntry 29 1 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 784
  idEntry 29 7 ⟨-33, -6, 18, 1, 75, by decide⟩, -- source row 790
  idEntry 29 8 ⟨12, 59, 23, 36, 150, by decide⟩, -- source row 791
  sumEntry 0 7 ⟨-243, 24, -24, 7, 300, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨-24, 257, -7, -24, 300, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨-573, -636, 36, -323, 3900, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨564, 73, -323, -36, 3900, by decide⟩, -- source row 1114
  sumEntry 7 0 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨-48, -36, 12, -16, 225, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨12, 9, -3, 4, 75, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨48, 36, -12, 16, 195, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨12, 9, -3, 4, 117, by decide⟩, -- source row 1299
  sumEntry 8 0 ⟨3, -4, -4, -3, 30, by decide⟩, -- source row 1308
  sumEntry 8 1 ⟨3, -4, -4, -3, 30, by decide⟩, -- source row 1309
  sumEntry 8 7 ⟨-48, -36, 12, -16, 225, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨12, 9, -3, 4, 75, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨-63, -16, 32, -1, 390, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨48, -189, -129, -128, 1170, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1335
  sumEntry 9 7 ⟨-57, -24, 24, -7, 300, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨24, 43, 7, 24, 300, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨3, -4, -4, -3, 78, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨-6, 8, 8, 6, 65, by decide⟩, -- source row 1353
  pairEntry 0 21 (by decide) ⟨-15, 20, 4, 3, 60, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨3, -4, 4, 3, 30, by decide⟩, -- source row 1464
  pairEntry 0 24 (by decide) ⟨-9, 12, 4, 3, 30, by decide⟩, -- source row 1466
  pairEntry 0 25 (by decide) ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 1467
  pairEntry 0 27 (by decide) ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨3, -4, 12, 9, 60, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨-15, 20, 4, 3, 60, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨3, -4, 4, 3, 30, by decide⟩, -- source row 1501
  pairEntry 1 24 (by decide) ⟨-9, 12, 4, 3, 30, by decide⟩, -- source row 1503
  pairEntry 1 25 (by decide) ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 1504
  pairEntry 1 27 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨3, -4, 4, 3, 30, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1544
  pairEntry 21 24 (by decide) ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨-3, 4, 4, 3, 30, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨3, -4, -4, -3, 30, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨3, -4, -4, -3, 30, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨3, -4, 0, 0, 15, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨-3, 4, 4, 3, 30, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨-3, 4, 0, 0, 15, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨3, -4, -4, -3, 30, by decide⟩ -- source row 2106
]

def lambda11 : List Entry := [
  idEntry 0 0 ⟨-5, 12, 0, 0, 39, by decide⟩, -- source row 0
  idEntry 0 1 ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 1
  idEntry 0 2 ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 2
  idEntry 1 0 ⟨5, -12, 0, 0, 26, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-5, 12, 0, 0, 26, by decide⟩, -- source row 28
  idEntry 1 2 ⟨5, -12, 0, 0, 26, by decide⟩, -- source row 29
  idEntry 1 17 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 44
  idEntry 1 18 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 45
  idEntry 21 0 ⟨5, -12, -12, -5, 78, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-25, 60, -12, -5, 78, by decide⟩, -- source row 568
  idEntry 21 2 ⟨25, -60, 12, 5, 78, by decide⟩, -- source row 569
  idEntry 21 7 ⟨58, -4, 12, 5, 65, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-68, -141, 48, 20, 195, by decide⟩, -- source row 575
  idEntry 22 0 ⟨-5, 12, -12, -5, 39, by decide⟩, -- source row 594
  idEntry 22 1 ⟨5, -12, 12, 5, 78, by decide⟩, -- source row 595
  idEntry 22 2 ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 596
  idEntry 22 7 ⟨-15, 36, -92, 18, 195, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-20, 48, -81, -76, 195, by decide⟩, -- source row 602
  idEntry 23 0 ⟨0, 0, 12, 5, 26, by decide⟩, -- source row 621
  idEntry 23 1 ⟨5, -12, 0, 0, 26, by decide⟩, -- source row 622
  idEntry 23 2 ⟨-20, 48, -12, -5, 78, by decide⟩, -- source row 623
  idEntry 23 7 ⟨-129, -96, 16, 63, 195, by decide⟩, -- source row 628
  idEntry 23 8 ⟨128, -3, 63, -16, 195, by decide⟩, -- source row 629
  idEntry 24 0 ⟨-5, 12, 0, 0, 39, by decide⟩, -- source row 648
  idEntry 24 1 ⟨5, -12, 36, 15, 78, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-5, 12, -36, -15, 78, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-43, -32, -16, -63, 130, by decide⟩, -- source row 655
  idEntry 24 8 ⟨128, -3, -189, 48, 390, by decide⟩, -- source row 656
  idEntry 25 0 ⟨-15, 36, 12, 5, 78, by decide⟩, -- source row 675
  idEntry 25 1 ⟨0, 0, -12, -5, 39, by decide⟩, -- source row 676
  idEntry 25 2 ⟨5, -12, 12, 5, 39, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-249, 192, 16, 63, 390, by decide⟩, -- source row 682
  idEntry 25 8 ⟨-32, 381, 63, -16, 390, by decide⟩, -- source row 683
  idEntry 26 0 ⟨25, -60, -12, -5, 78, by decide⟩, -- source row 702
  idEntry 26 1 ⟨-5, 12, -12, -5, 78, by decide⟩, -- source row 703
  idEntry 26 2 ⟨-5, 12, 12, 5, 78, by decide⟩, -- source row 704
  idEntry 26 7 ⟨63, -16, -32, 43, 130, by decide⟩, -- source row 709
  idEntry 26 8 ⟨-48, -189, -3, -128, 390, by decide⟩, -- source row 710
  idEntry 27 0 ⟨-5, 12, 12, 5, 78, by decide⟩, -- source row 729
  idEntry 27 1 ⟨5, -12, -12, -5, 39, by decide⟩, -- source row 730
  idEntry 27 2 ⟨0, 0, 12, 5, 39, by decide⟩, -- source row 731
  idEntry 27 7 ⟨-43, -32, -8, 53, 130, by decide⟩, -- source row 736
  idEntry 27 8 ⟨128, -3, 93, -88, 390, by decide⟩, -- source row 737
  idEntry 28 0 ⟨15, -36, 12, 5, 78, by decide⟩, -- source row 756
  idEntry 28 1 ⟨-15, 36, 12, 5, 78, by decide⟩, -- source row 757
  idEntry 28 2 ⟨15, -36, -24, -10, 78, by decide⟩, -- source row 758
  idEntry 28 7 ⟨189, -48, 88, 93, 390, by decide⟩, -- source row 763
  idEntry 28 8 ⟨-16, -63, 53, 8, 130, by decide⟩, -- source row 764
  idEntry 29 0 ⟨-15, 36, -24, -10, 78, by decide⟩, -- source row 783
  idEntry 29 1 ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 784
  idEntry 29 7 ⟨99, 168, -16, -63, 390, by decide⟩, -- source row 790
  idEntry 29 8 ⟨-168, 99, -63, 16, 390, by decide⟩, -- source row 791
  sumEntry 0 7 ⟨15, -36, -20, 48, 390, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨20, -48, 15, -36, 390, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨165, -396, 280, -672, 5070, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨280, -672, -165, 396, 5070, by decide⟩, -- source row 1114
  sumEntry 7 0 ⟨-5, 12, 0, 0, 78, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨99, 168, -88, -93, 1170, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨-56, 33, -53, -8, 390, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨745, 240, -80, 23, 1014, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨720, 807, 407, 240, 3042, by decide⟩, -- source row 1299
  sumEntry 8 1 ⟨-5, 12, 0, 0, 39, by decide⟩, -- source row 1309
  sumEntry 8 7 ⟨-189, 48, 128, -3, 1170, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨16, 63, 43, 32, 390, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨269, -240, -80, 23, 1014, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨-720, 2235, 407, 240, 3042, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨-5, 12, 0, 0, 78, by decide⟩, -- source row 1335
  sumEntry 9 1 ⟨-5, 12, 12, 5, 78, by decide⟩, -- source row 1336
  sumEntry 9 7 ⟨15, -36, -20, 48, 390, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨20, -48, 15, -36, 390, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨507, 0, 120, -119, 1014, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨0, 507, -119, -120, 1014, by decide⟩, -- source row 1353
  pairEntry 0 21 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 1464
  pairEntry 0 27 (by decide) ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨-10, 24, 12, 5, 78, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨5, -12, 12, 5, 39, by decide⟩, -- source row 1501
  pairEntry 1 24 (by decide) ⟨15, -36, 12, 5, 78, by decide⟩, -- source row 1503
  pairEntry 1 25 (by decide) ⟨15, -36, -12, -5, 78, by decide⟩, -- source row 1504
  pairEntry 1 27 (by decide) ⟨15, -36, -24, -10, 78, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨-5, 12, -12, -5, 78, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨-5, 12, 0, 0, 78, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨-5, 12, 0, 0, 78, by decide⟩, -- source row 1544
  pairEntry 21 24 (by decide) ⟨5, -12, -12, -5, 78, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨5, -12, 12, 5, 78, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨5, -12, 12, 5, 78, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨-5, 12, 12, 5, 78, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨-5, 12, 0, 0, 78, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨5, -12, 0, 0, 78, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨-5, 12, -12, -5, 78, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨-5, 12, 0, 0, 39, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨5, -12, -12, -5, 78, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨5, -12, 0, 0, 39, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨-5, 12, 12, 5, 78, by decide⟩ -- source row 2106
]

def lambda10 : List Entry := [
  idEntry 0 0 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 2
  idEntry 1 0 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 27
  idEntry 1 1 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 29
  idEntry 1 13 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 40
  idEntry 1 14 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 41
  idEntry 2 0 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 55
  idEntry 2 2 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 56
  idEntry 30 0 ⟨-63, 60, 20, 21, 174, by decide⟩, -- source row 810
  idEntry 30 1 ⟨63, -60, 20, 21, 174, by decide⟩, -- source row 811
  idEntry 30 2 ⟨21, -20, -20, -21, 174, by decide⟩, -- source row 812
  idEntry 30 9 ⟨50, -368, -100, -105, 493, by decide⟩, -- source row 819
  idEntry 30 10 ⟨-1236, -625, 160, 168, 1479, by decide⟩, -- source row 820
  idEntry 31 0 ⟨0, 0, 20, 21, 87, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-63, 60, -20, -21, 174, by decide⟩, -- source row 838
  idEntry 31 2 ⟨42, -40, 0, 0, 87, by decide⟩, -- source row 839
  idEntry 31 9 ⟨-315, 300, 432, 790, 1479, by decide⟩, -- source row 846
  idEntry 31 10 ⟨168, -160, -635, -36, 1479, by decide⟩, -- source row 847
  idEntry 32 0 ⟨-21, 20, -60, -63, 174, by decide⟩, -- source row 864
  idEntry 32 1 ⟨-42, 40, 0, 0, 87, by decide⟩, -- source row 865
  idEntry 32 2 ⟨147, -140, 20, 21, 174, by decide⟩, -- source row 866
  idEntry 32 9 ⟨-150, 1104, 36, -635, 1479, by decide⟩, -- source row 873
  idEntry 32 10 ⟨1236, 625, 790, -432, 1479, by decide⟩, -- source row 874
  idEntry 33 0 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-21, 20, -60, -63, 174, by decide⟩, -- source row 892
  idEntry 33 2 ⟨21, -20, 60, 63, 174, by decide⟩, -- source row 893
  idEntry 33 9 ⟨55, 268, 132, 475, 986, by decide⟩, -- source row 900
  idEntry 33 10 ⟨1068, 785, -1425, 396, 2958, by decide⟩, -- source row 901
  idEntry 34 0 ⟨63, -60, -20, -21, 174, by decide⟩, -- source row 918
  idEntry 34 1 ⟨0, 0, 20, 21, 87, by decide⟩, -- source row 919
  idEntry 34 2 ⟨-21, 20, -20, -21, 87, by decide⟩, -- source row 920
  idEntry 34 9 ⟨2685, -1596, -132, -475, 2958, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-276, 2065, 475, -132, 2958, by decide⟩, -- source row 928
  idEntry 35 0 ⟨-105, 100, 20, 21, 174, by decide⟩, -- source row 945
  idEntry 35 1 ⟨21, -20, 20, 21, 174, by decide⟩, -- source row 946
  idEntry 35 2 ⟨21, -20, -20, -21, 174, by decide⟩, -- source row 947
  idEntry 35 9 ⟨-475, 132, 268, -55, 986, by decide⟩, -- source row 954
  idEntry 35 10 ⟨-396, -1425, 785, -1068, 2958, by decide⟩, -- source row 955
  idEntry 36 0 ⟨-63, 60, -20, -21, 174, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-63, 60, 20, 21, 87, by decide⟩, -- source row 973
  idEntry 36 2 ⟨63, -60, -20, -21, 87, by decide⟩, -- source row 974
  idEntry 36 9 ⟨1105, -732, 68, -265, 986, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-612, 2385, 1105, -732, 2958, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-21, 20, -20, -21, 174, by decide⟩, -- source row 999
  idEntry 37 1 ⟨105, -100, -20, -21, 174, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨-63, 60, 20, 21, 87, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨-2055, 996, -60, -1745, 2958, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-60, -1745, 2055, -996, 2958, by decide⟩, -- source row 1009
  idEntry 38 0 ⟨42, -40, 20, 21, 87, by decide⟩, -- source row 1026
  idEntry 38 1 ⟨21, -20, -20, -21, 174, by decide⟩, -- source row 1027
  idEntry 38 9 ⟨-265, -68, -68, 265, 986, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨-732, -1105, -1105, 732, 2958, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨315, -300, 168, -160, 1479, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨-168, 160, 315, -300, 1479, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨0, 0, 840, -800, 7569, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨0, 0, -294, 280, 2523, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨3255, -3100, -3276, 3120, 42891, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨-29484, 28080, -3255, 3100, 128673, by decide⟩, -- source row 1116
  sumEntry 10 1 ⟨21, -20, 20, 21, 174, by decide⟩, -- source row 1363
  sumEntry 10 2 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨465, -1404, 732, 1105, 8874, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨-468, -155, -265, -68, 2958, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨-7323, -5040, 1680, 923, 15138, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨1680, 2605, 253, 560, 5046, by decide⟩, -- source row 1376
  sumEntry 11 1 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 1390
  sumEntry 11 9 ⟨1425, -396, -1068, -785, 8874, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨132, 475, 55, 268, 2958, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨-7815, 5040, 1680, 923, 15138, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨-1680, 2441, 253, 560, 5046, by decide⟩, -- source row 1403
  sumEntry 12 0 ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 1416
  sumEntry 12 1 ⟨-21, 20, -20, -21, 174, by decide⟩, -- source row 1417
  sumEntry 12 9 ⟨-210, 200, 0, 0, 493, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨336, -320, 0, 0, 1479, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨-841, 0, -560, 253, 1682, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨0, 2523, 923, -1680, 5046, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 1474
  pairEntry 0 36 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨-42, 40, 0, 0, 87, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 1480
  pairEntry 1 30 (by decide) ⟨63, -60, -20, -21, 174, by decide⟩, -- source row 1509
  pairEntry 1 31 (by decide) ⟨-42, 40, -20, -21, 87, by decide⟩, -- source row 1510
  pairEntry 1 33 (by decide) ⟨-63, 60, -20, -21, 174, by decide⟩, -- source row 1512
  pairEntry 1 34 (by decide) ⟨-63, 60, 20, 21, 174, by decide⟩, -- source row 1513
  pairEntry 1 36 (by decide) ⟨0, 0, 20, 21, 87, by decide⟩, -- source row 1515
  pairEntry 1 37 (by decide) ⟨21, -20, 20, 21, 174, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨-42, 40, 0, 0, 87, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 1552
  pairEntry 30 33 (by decide) ⟨-21, 20, 20, 21, 174, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨-21, 20, -20, -21, 174, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨-21, 20, -20, -21, 174, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨21, -20, -20, -21, 174, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨42, -40, 0, 0, 87, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨63, -60, 20, 21, 174, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨21, -20, 20, 21, 174, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨21, -20, 0, 0, 87, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨-21, 20, 20, 21, 174, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨-21, 20, 0, 0, 87, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨21, -20, -20, -21, 174, by decide⟩ -- source row 2178
]

def lambda5 : List Entry := [
  idEntry 0 0 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 2
  idEntry 0 23 ⟨1, 0, 0, 0, 1, by decide⟩, -- source row 23
  idEntry 0 24 ⟨0, 1, 0, 0, 1, by decide⟩, -- source row 24
  idEntry 1 0 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 27
  idEntry 1 1 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 29
  idEntry 2 0 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 55
  idEntry 2 2 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 56
  idEntry 30 0 ⟨-310, 936, 0, 0, 1479, by decide⟩, -- source row 810
  idEntry 30 1 ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 811
  idEntry 30 2 ⟨155, -468, -468, -155, 1479, by decide⟩, -- source row 812
  idEntry 30 9 ⟨3744, 1240, -2340, -775, 8381, by decide⟩, -- source row 819
  idEntry 30 10 ⟨21060, 6975, 3744, 1240, 25143, by decide⟩, -- source row 820
  idEntry 31 0 ⟨155, -468, -468, -155, 1479, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-155, 468, -468, -155, 2958, by decide⟩, -- source row 839
  idEntry 31 9 ⟨3744, 1240, -2340, -775, 8381, by decide⟩, -- source row 846
  idEntry 31 10 ⟨21060, 6975, 3744, 1240, 25143, by decide⟩, -- source row 847
  idEntry 32 0 ⟨0, 0, 936, 310, 1479, by decide⟩, -- source row 864
  idEntry 32 1 ⟨-465, 1404, 468, 155, 2958, by decide⟩, -- source row 865
  idEntry 32 2 ⟨775, -2340, -1404, -465, 2958, by decide⟩, -- source row 866
  idEntry 32 9 ⟨-15882, 10320, 9500, -5163, 25143, by decide⟩, -- source row 873
  idEntry 32 10 ⟨-18580, -14463, 906, -15280, 25143, by decide⟩, -- source row 874
  idEntry 33 0 ⟨0, 0, 468, 155, 1479, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-465, 1404, -468, -155, 2958, by decide⟩, -- source row 892
  idEntry 33 2 ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 893
  idEntry 33 9 ⟨131, -12940, 3580, -2969, 16762, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-27260, 11745, 3231, -22300, 50286, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-310, 936, 0, 0, 1479, by decide⟩, -- source row 918
  idEntry 34 1 ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 919
  idEntry 34 2 ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 920
  idEntry 34 9 ⟨-6069, 5780, 3580, -2969, 16762, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-17340, -18207, 3231, -22300, 50286, by decide⟩, -- source row 928
  idEntry 35 0 ⟨310, -936, -468, -155, 1479, by decide⟩, -- source row 945
  idEntry 35 1 ⟨155, -468, 468, 155, 2958, by decide⟩, -- source row 946
  idEntry 35 2 ⟨-155, 468, -468, -155, 2958, by decide⟩, -- source row 947
  idEntry 35 9 ⟨-8907, -10740, 5780, 6069, 50286, by decide⟩, -- source row 954
  idEntry 35 10 ⟨-22300, -3231, -6069, 5780, 50286, by decide⟩, -- source row 955
  idEntry 36 0 ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-155, 468, 1404, 465, 2958, by decide⟩, -- source row 973
  idEntry 36 2 ⟨0, 0, -468, -155, 1479, by decide⟩, -- source row 974
  idEntry 36 9 ⟨-2969, -3580, -12940, -131, 16762, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-22300, -3231, 11745, 27260, 50286, by decide⟩, -- source row 982
  idEntry 37 0 ⟨465, -1404, 468, 155, 2958, by decide⟩, -- source row 999
  idEntry 37 1 ⟨0, 0, -468, -155, 1479, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨0, 0, 468, 155, 1479, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨-26721, -32220, 5780, 6069, 50286, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-66900, -9693, -6069, 5780, 50286, by decide⟩, -- source row 1009
  idEntry 38 0 ⟨-775, 2340, -468, -155, 2958, by decide⟩, -- source row 1026
  idEntry 38 1 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 1027
  idEntry 38 9 ⟨8907, 10740, 5780, 6069, 50286, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨22300, 3231, -6069, 5780, 50286, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨-8907, -10740, -5780, -6069, 50286, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨-22300, -3231, 6069, -5780, 50286, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨-28080, -9300, 3100, -9360, 128673, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨9828, 3255, -1085, 3276, 42891, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨243049, 0, -96720, 48983, 1458294, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨0, 729147, 633047, 290160, 4374882, by decide⟩, -- source row 1116
  sumEntry 10 0 ⟨155, -468, 468, 155, 2958, by decide⟩, -- source row 1362
  sumEntry 10 1 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 1363
  sumEntry 10 2 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨40671, -9900, -19820, -10719, 150858, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨19820, 10719, 4519, -1100, 50286, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨74475, 57384, -32584, -405, 257346, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨-32584, -405, -8275, -6376, 85782, by decide⟩, -- source row 1376
  sumEntry 11 0 ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 1389
  sumEntry 11 9 ⟨-18207, 17340, 2480, -7488, 75429, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨-5780, -6069, 1550, -4680, 25143, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨1215, -97752, -32584, -405, 257346, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨19128, -24825, -8275, -6376, 85782, by decide⟩, -- source row 1403
  sumEntry 12 0 ⟨-155, 468, -468, -155, 2958, by decide⟩, -- source row 1416
  sumEntry 12 9 ⟨0, 0, 20, 21, 87, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨0, 0, -21, 20, 87, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨31335, -528, 12928, -6105, 85782, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨-26384, -19125, 6105, 12928, 85782, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨-155, 468, -468, -155, 1479, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨-155, 468, -468, -155, 2958, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 1474
  pairEntry 0 33 (by decide) ⟨0, 0, 468, 155, 1479, by decide⟩, -- source row 1475
  pairEntry 0 34 (by decide) ⟨-465, 1404, 468, 155, 2958, by decide⟩, -- source row 1476
  pairEntry 0 36 (by decide) ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨155, -468, 1404, 465, 2958, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 1480
  pairEntry 1 31 (by decide) ⟨-155, 468, 468, 155, 1479, by decide⟩, -- source row 1510
  pairEntry 1 37 (by decide) ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨-155, 468, 468, 155, 1479, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 1552
  pairEntry 30 33 (by decide) ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨-155, 468, 0, 0, 1479, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨155, -468, 468, 155, 2958, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨-155, 468, 468, 155, 2958, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨155, -468, -468, -155, 1479, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨0, 0, -468, -155, 1479, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨155, -468, -468, -155, 2958, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨-155, 468, 0, 0, 1479, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨155, -468, 468, 155, 2958, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨155, -468, 0, 0, 1479, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨-155, 468, -468, -155, 2958, by decide⟩ -- source row 2178
]

def lambda24 : List Entry := [
  idEntry 0 0 ⟨15, -8, -8, -15, 51, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 2
  idEntry 1 0 ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 27
  idEntry 1 1 ⟨15, -8, -8, -15, 51, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 29
  idEntry 2 0 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 54
  idEntry 2 1 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 55
  idEntry 2 2 ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 56
  idEntry 2 9 ⟨-1, 0, 0, 0, 1, by decide⟩, -- source row 63
  idEntry 2 10 ⟨0, -1, 0, 0, 1, by decide⟩, -- source row 64
  idEntry 30 0 ⟨-15, 8, -8, -15, 102, by decide⟩, -- source row 810
  idEntry 30 1 ⟨-15, 8, -8, -15, 102, by decide⟩, -- source row 811
  idEntry 30 2 ⟨15, -8, 24, 45, 102, by decide⟩, -- source row 812
  idEntry 30 9 ⟨-150, 80, 80, 150, 289, by decide⟩, -- source row 819
  idEntry 30 10 ⟨240, -128, -128, -240, 867, by decide⟩, -- source row 820
  idEntry 31 0 ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 837
  idEntry 31 1 ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-75, 40, 8, 15, 102, by decide⟩, -- source row 839
  idEntry 31 9 ⟨33, -480, 0, -289, 867, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-480, -611, 289, 0, 867, by decide⟩, -- source row 847
  idEntry 32 0 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 864
  idEntry 32 1 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 865
  idEntry 32 2 ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 866
  idEntry 33 0 ⟨-15, 8, 0, 0, 51, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-15, 8, 0, 0, 51, by decide⟩, -- source row 892
  idEntry 33 2 ⟨30, -16, 0, 0, 51, by decide⟩, -- source row 893
  idEntry 34 0 ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 918
  idEntry 34 1 ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 919
  idEntry 34 2 ⟨-75, 40, 8, 15, 102, by decide⟩, -- source row 920
  idEntry 34 9 ⟨33, -480, 0, -289, 867, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-480, -611, 289, 0, 867, by decide⟩, -- source row 928
  idEntry 35 2 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 947
  idEntry 35 9 ⟨-417, -240, 240, 161, 867, by decide⟩, -- source row 954
  idEntry 35 10 ⟨-240, -739, 161, -240, 867, by decide⟩, -- source row 955
  idEntry 36 0 ⟨-15, 8, -8, -15, 102, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-15, 8, -8, -15, 102, by decide⟩, -- source row 973
  idEntry 36 2 ⟨45, -24, 8, 15, 102, by decide⟩, -- source row 974
  idEntry 36 9 ⟨-75, 40, 40, 75, 289, by decide⟩, -- source row 981
  idEntry 36 10 ⟨120, -64, -64, -120, 867, by decide⟩, -- source row 982
  idEntry 37 0 ⟨15, -8, 8, 15, 102, by decide⟩, -- source row 999
  idEntry 37 1 ⟨15, -8, 8, 15, 102, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨-45, 24, -8, -15, 102, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨75, -40, -40, -75, 289, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-120, 64, 64, 120, 867, by decide⟩, -- source row 1009
  idEntry 38 9 ⟨-192, -360, 120, -64, 867, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨-120, -225, 75, -40, 289, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨-1767, 480, 0, 289, 1734, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨480, -1123, -289, 0, 1734, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨480, 900, -300, 160, 4437, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨-168, -315, 105, -56, 1479, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨-6069, -5780, 3580, 1077, 50286, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨17340, -18207, -8907, -22300, 150858, by decide⟩, -- source row 1116
  sumEntry 10 0 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1362
  sumEntry 10 2 ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨-192, -360, 120, -64, 2601, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨-120, -225, 75, -40, 867, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨480, 900, -300, 160, 4437, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨-168, -315, 105, -56, 1479, by decide⟩, -- source row 1376
  sumEntry 11 0 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1389
  sumEntry 11 1 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1390
  sumEntry 11 9 ⟨-192, -360, 120, -64, 2601, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨-120, -225, 75, -40, 867, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨-1425, -396, 804, 785, 8874, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨-132, 475, 55, 356, 2958, by decide⟩, -- source row 1403
  sumEntry 12 1 ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1417
  sumEntry 12 9 ⟨33, -480, 0, -289, 1734, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨-480, -611, 289, 0, 1734, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨-165, -1068, 132, -475, 2958, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨804, 785, -475, -132, 2958, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨-30, 16, 8, 15, 51, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨15, -8, 8, 15, 102, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 1474
  pairEntry 0 33 (by decide) ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 1475
  pairEntry 0 34 (by decide) ⟨0, 0, 8, 15, 51, by decide⟩, -- source row 1476
  pairEntry 0 36 (by decide) ⟨-15, 8, 0, 0, 51, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1480
  pairEntry 1 30 (by decide) ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 1509
  pairEntry 1 31 (by decide) ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 1510
  pairEntry 1 33 (by decide) ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 1512
  pairEntry 1 34 (by decide) ⟨0, 0, 8, 15, 51, by decide⟩, -- source row 1513
  pairEntry 1 36 (by decide) ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 1515
  pairEntry 1 37 (by decide) ⟨15, -8, 8, 15, 102, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨15, -8, -8, -15, 51, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 1552
  pairEntry 30 33 (by decide) ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨-15, 8, 0, 0, 51, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨-15, 8, 8, 15, 51, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨15, -8, -8, -15, 102, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨15, -8, 0, 0, 51, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨-15, 8, 8, 15, 102, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨-15, 8, 0, 0, 51, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨15, -8, -8, -15, 102, by decide⟩ -- source row 2178
]

structure HSpec where
  quadricIndex : Fin 48
  negated : Bool
  conjugated : Bool

def hSpec : Fin 4 → Fin 3 → HSpec :=
  ![![⟨0, true, false⟩, ⟨2, true, false⟩, ⟨1, false, false⟩],
    ![⟨22, false, false⟩, ⟨14, false, false⟩, ⟨8, false, true⟩],
    ![⟨4, false, true⟩, ⟨25, true, false⟩, ⟨11, false, false⟩],
    ![⟨10, false, false⟩, ⟨5, true, true⟩, ⟨24, true, false⟩]]

def rawEntries : Fin 4 → Fin 3 → List Entry :=
  ![![lambda0, lambda2, lambda1],
    ![lambda22, lambda14, lambda8],
    ![lambda4, lambda25, lambda11],
    ![lambda10, lambda5, lambda24]]

/-- Conjugation acts on complex coefficients; row labels never change. -/
def orientedValue (s : HSpec) (c : Literal) : Complex :=
  let z := if s.conjugated then star c.toComplex else c.toComplex
  if s.negated then -z else z

/-- All twelve actual sparse covectors in their prescribed H order. -/
def hEntries (i : Fin 4) (a : Fin 3) : List (Fin 2184 × Complex) :=
  (rawEntries i a).map fun e =>
    (fNumber e.label, orientedValue (hSpec i a) e.coefficient)

/-- The sum includes every occurrence. It is not a partial/default dictionary. -/
def sparseWeight {ι : Type*} [DecidableEq ι] (es : List (ι × Complex)) : ι → Complex := fun r =>
  (es.map fun e => if e.1 = r then e.2 else 0).sum

def weightC (i : Fin 4) (a : Fin 3) : AnchorSupport.Weights :=
  sparseWeight (hEntries i a)

/-- Positive denominators are retained before the transparent complex cast. -/
theorem denominator_positive (c : Literal) : 0 < c.denominator := c.denominator_pos

/-- Dense original-row contraction is exactly the actual sparse list sum. -/
theorem dense_sparse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (es : List (ι × Complex)) (g : ι → Complex) :
    (∑ r : ι, sparseWeight es r * g r) =
      (es.map fun e => e.2 * g e.1).sum := by
  classical
  induction es with
  | nil => simp [sparseWeight]
  | cons e es ih =>
    have hfun : sparseWeight (e :: es) = fun r =>
        (if e.1 = r then e.2 else 0) + sparseWeight es r := rfl
    rw [hfun]
    simp only [add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    simp

theorem weightC_dense_sparse (i : Fin 4) (a : Fin 3) (g : Fin 2184 → Complex) :
    (∑ r : Fin 2184, weightC i a r * g r) =
      ((hEntries i a).map fun e => e.2 * g e.1).sum :=
  dense_sparse (hEntries i a) g

end Option2.NativeStress.NativeH

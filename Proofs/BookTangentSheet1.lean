module

public import BookTangentPairingCore

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet1_pair01 : d6Entries 8 = (d6Entries 6).map negConjEntry := by
  change column8 = column6.map negConjEntry
  rfl

theorem sheet1_pair02 : d6Entries 10 = (d6Entries 7).map negConjEntry := by
  change column10 = column7.map negConjEntry
  rfl

theorem sheet1_pair12 : d6Entries 11 = (d6Entries 9).map negConjEntry := by
  change column11 = column9.map negConjEntry
  rfl

theorem sheet1_pair10 : d6Entries 6 = (d6Entries 8).map negConjEntry :=
  raw_bar_reverse sheet1_pair01

theorem sheet1_pair20 : d6Entries 7 = (d6Entries 10).map negConjEntry :=
  raw_bar_reverse sheet1_pair02

theorem sheet1_pair21 : d6Entries 9 = (d6Entries 11).map negConjEntry :=
  raw_bar_reverse sheet1_pair12

#check sheet1_pair01
#check sheet1_pair02
#check sheet1_pair12
#check sheet1_pair10
#check sheet1_pair20
#check sheet1_pair21

#print axioms sheet1_pair01
#print axioms sheet1_pair02
#print axioms sheet1_pair12
#print axioms sheet1_pair10
#print axioms sheet1_pair20
#print axioms sheet1_pair21

end Option2.NativeStress.BookHT.TangentCoordinates


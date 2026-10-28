module

public import BookTangentPairingCore

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet2_pair01 : d6Entries 14 = (d6Entries 12).map negConjEntry := by
  change column14 = column12.map negConjEntry
  rfl

theorem sheet2_pair02 : d6Entries 16 = (d6Entries 13).map negConjEntry := by
  change column16 = column13.map negConjEntry
  rfl

theorem sheet2_pair12 : d6Entries 17 = (d6Entries 15).map negConjEntry := by
  change column17 = column15.map negConjEntry
  rfl

theorem sheet2_pair10 : d6Entries 12 = (d6Entries 14).map negConjEntry :=
  raw_bar_reverse sheet2_pair01

theorem sheet2_pair20 : d6Entries 13 = (d6Entries 16).map negConjEntry :=
  raw_bar_reverse sheet2_pair02

theorem sheet2_pair21 : d6Entries 15 = (d6Entries 17).map negConjEntry :=
  raw_bar_reverse sheet2_pair12

#check sheet2_pair01
#check sheet2_pair02
#check sheet2_pair12
#check sheet2_pair10
#check sheet2_pair20
#check sheet2_pair21

#print axioms sheet2_pair01
#print axioms sheet2_pair02
#print axioms sheet2_pair12
#print axioms sheet2_pair10
#print axioms sheet2_pair20
#print axioms sheet2_pair21

end Option2.NativeStress.BookHT.TangentCoordinates


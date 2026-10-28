module

public import BookTangentPairingCore

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet3_pair01 : d6Entries 20 = (d6Entries 18).map negConjEntry := by
  change column20 = column18.map negConjEntry
  rfl

theorem sheet3_pair02 : d6Entries 22 = (d6Entries 19).map negConjEntry := by
  change column22 = column19.map negConjEntry
  rfl

theorem sheet3_pair12 : d6Entries 23 = (d6Entries 21).map negConjEntry := by
  change column23 = column21.map negConjEntry
  rfl

theorem sheet3_pair10 : d6Entries 18 = (d6Entries 20).map negConjEntry :=
  raw_bar_reverse sheet3_pair01

theorem sheet3_pair20 : d6Entries 19 = (d6Entries 22).map negConjEntry :=
  raw_bar_reverse sheet3_pair02

theorem sheet3_pair21 : d6Entries 21 = (d6Entries 23).map negConjEntry :=
  raw_bar_reverse sheet3_pair12

#check sheet3_pair01
#check sheet3_pair02
#check sheet3_pair12
#check sheet3_pair10
#check sheet3_pair20
#check sheet3_pair21

#print axioms sheet3_pair01
#print axioms sheet3_pair02
#print axioms sheet3_pair12
#print axioms sheet3_pair10
#print axioms sheet3_pair20
#print axioms sheet3_pair21

end Option2.NativeStress.BookHT.TangentCoordinates


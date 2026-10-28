module

public import BookTangentPairingCore

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet0_pair01 : d6Entries 2 = (d6Entries 0).map negConjEntry := by
  change column2 = column0.map negConjEntry
  rfl

theorem sheet0_pair02 : d6Entries 4 = (d6Entries 1).map negConjEntry := by
  change column4 = column1.map negConjEntry
  rfl

theorem sheet0_pair12 : d6Entries 5 = (d6Entries 3).map negConjEntry := by
  change column5 = column3.map negConjEntry
  rfl

theorem sheet0_pair10 : d6Entries 0 = (d6Entries 2).map negConjEntry :=
  raw_bar_reverse sheet0_pair01

theorem sheet0_pair20 : d6Entries 1 = (d6Entries 4).map negConjEntry :=
  raw_bar_reverse sheet0_pair02

theorem sheet0_pair21 : d6Entries 3 = (d6Entries 5).map negConjEntry :=
  raw_bar_reverse sheet0_pair12

#check sheet0_pair01
#check sheet0_pair02
#check sheet0_pair12
#check sheet0_pair10
#check sheet0_pair20
#check sheet0_pair21

#print axioms coefficient_negConj
#print axioms sparseValue_negConj
#print axioms sheet0_pair01
#print axioms sheet0_pair02
#print axioms sheet0_pair12
#print axioms sheet0_pair10
#print axioms sheet0_pair20
#print axioms sheet0_pair21

end Option2.NativeStress.BookHT.TangentCoordinates


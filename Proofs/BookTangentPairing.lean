module

public import BookTangentSheet0
public import BookTangentSheet1
public import BookTangentSheet2
public import BookTangentSheet3

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

/-- All 24 literal D6 columns have the supplied negative-conjugate partner. -/
theorem d6Entries_bar (b : Fin 24) :
    d6Entries (basisBar b) = (d6Entries b).map negConjEntry := by
  fin_cases b
  · exact sheet0_pair01
  · exact sheet0_pair02
  · exact sheet0_pair10
  · exact sheet0_pair12
  · exact sheet0_pair20
  · exact sheet0_pair21
  · exact sheet1_pair01
  · exact sheet1_pair02
  · exact sheet1_pair10
  · exact sheet1_pair12
  · exact sheet1_pair20
  · exact sheet1_pair21
  · exact sheet2_pair01
  · exact sheet2_pair02
  · exact sheet2_pair10
  · exact sheet2_pair12
  · exact sheet2_pair20
  · exact sheet2_pair21
  · exact sheet3_pair01
  · exact sheet3_pair02
  · exact sheet3_pair10
  · exact sheet3_pair12
  · exact sheet3_pair20
  · exact sheet3_pair21

#check d6Entries_bar
#print axioms d6Entries_bar

end Option2.NativeStress.BookHT.TangentCoordinates


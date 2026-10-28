module

public import BookTangentPairingCore

set_option Elab.async false

@[expose] public section

/-!
Compatibility of the literal finite-index maps.
Fin.forall_fin_succ and Fin.forall_fin_zero replace finite-set enumeration;
the three existing map definitions supply all table entries. No sparse evaluator,
column map, V, native tangent or metric theorem is introduced.


-/

namespace Option2.NativeStress.BookHT.TangentCoordinates

/-- The exact eigenvector ordering preserves the supplied conjugate pairing. -/
theorem eigenIndex_coordinateBar (j : Fin 24) :
    eigenIndex (Dictionary.coordinateBar j) = basisBar (eigenIndex j) := by
  revert j
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  simp [eigenIndex, Dictionary.coordinateBar, basisBar]

end Option2.NativeStress.BookHT.TangentCoordinates

#check @Option2.NativeStress.BookHT.TangentCoordinates.eigenIndex_coordinateBar
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.eigenIndex_coordinateBar

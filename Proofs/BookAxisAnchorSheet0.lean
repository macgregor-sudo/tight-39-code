module

public import BookAxisSparseSupport

set_option Elab.async false

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

/-- Every supplied entry in D6 sheet zero avoids its literal four anchor frames. -/
theorem sheet0_entries_avoid (k : Fin 6) :
    EntriesAvoidAnchor 0 (d6Entries ⟨k.val, by omega⟩) := by
  revert k
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  unfold EntriesAvoidAnchor AnchorSupport.AnchorCoordinate
  decide +kernel

#check @sheet0_entries_avoid
#print axioms sheet0_entries_avoid

end Option2.NativeStress.BookHT.TangentCoordinates

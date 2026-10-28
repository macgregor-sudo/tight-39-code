module

public import BookAxisSparseSupport

set_option Elab.async false

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet3_entries_avoid (k : Fin 6) :
    EntriesAvoidAnchor 3 (d6Entries ⟨18 + k.val, by omega⟩) := by
  revert k
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  unfold EntriesAvoidAnchor AnchorSupport.AnchorCoordinate
  decide +kernel

#check @sheet3_entries_avoid
#print axioms sheet3_entries_avoid

end Option2.NativeStress.BookHT.TangentCoordinates

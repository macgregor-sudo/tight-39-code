module

public import BookAxisSparseSupport

set_option Elab.async false

@[expose] public section

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem sheet1_entries_avoid (k : Fin 6) :
    EntriesAvoidAnchor 1 (d6Entries ⟨6 + k.val, by omega⟩) := by
  revert k
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  unfold EntriesAvoidAnchor AnchorSupport.AnchorCoordinate
  decide +kernel

#check @sheet1_entries_avoid
#print axioms sheet1_entries_avoid

end Option2.NativeStress.BookHT.TangentCoordinates

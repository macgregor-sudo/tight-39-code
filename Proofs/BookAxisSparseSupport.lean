module

public import BookNativeRealMapLinear

set_option Elab.async false

@[expose] public section

noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open AnchorSupport

/-- The original D6 sheet order: six columns per sheet. -/
def d6Sheet (b : Fin 24) : Fin 4 := ⟨b.val / 6, by omega⟩

/-- Only entry positions are used; no coefficient arithmetic is required. -/
def EntriesAvoidAnchor (i : Fin 4) (es : List Entry) : Prop :=
  ∀ e ∈ es, ¬ AnchorCoordinate i e.1

theorem sparseValue_eq_zero_of_avoids (i : Fin 4) (es : List Entry)
    (h : EntriesAvoidAnchor i es) (v : Fin 1053) (hv : AnchorCoordinate i v) :
    sparseValue es v = 0 := by
  revert h
  induction es with
  | nil => intro h; rfl
  | cons e es ih =>
      intro h
      have he : v ≠ e.1 := by
        intro heq
        exact h e (List.mem_cons_self ..) (heq ▸ hv)
      have ht : EntriesAvoidAnchor i es := fun f hf => h f (List.mem_cons_of_mem e hf)
      change (if v = e.1 then coefficient e.2 else 0) + sparseValue es v = 0
      rw [ite_eq_right he, ih ht, add_zero]

#check @sparseValue_eq_zero_of_avoids
#print axioms sparseValue_eq_zero_of_avoids

end Option2.NativeStress.BookHT.TangentCoordinates

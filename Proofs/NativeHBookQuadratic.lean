module

public import NativeHQuadraticRestriction

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators ComplexConjugate
open BookHT.Dictionary

theorem bookTerms_bound (i : Fin 4) (a : Fin 3) (e : Nat × Q12)
    (he : e ∈ bookTerms i a) : e.1 < 2^10 := by
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  dsimp
  unfold pairKey
  split_ifs <;> omega

theorem bookTerms_evaluate (i : Fin 4) (a : Fin 3) (z : BookHT.Blocks) :
    ((bookTerms i a).map fun e => Q12.toComplex e.2 *
      pairWeight (by decide) (realCoordinates z) e.1).sum = BookHT.H z i a := by
  rw [← selectedH_eq_Book]
  unfold bookTerms
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, pairWeight_pairKey,
    Fin.sum_univ_three]
  cases hc : (hSpec i a).conjugated <;> cases hn : (hSpec i a).negated <;>
    simp [orientedIndex, selectedH, hc, hn, quadric, termPolynomial,
      map_intCast, realCoordinates_bar] <;> ring

theorem bookTree_evaluate (i : Fin 4) (a : Fin 3) (z : BookHT.Blocks) :
    CoeffTree.evaluate Q12.toComplex (bookTree i a)
      (pairWeight (by decide) (realCoordinates z)) = BookHT.H z i a := by
  rw [bookTree, CoeffTree.evaluate_collect Q12.toComplex _ (bookTerms_bound i a)]
  exact bookTerms_evaluate i a z

/-- A single complete polynomial equality suffices for all Book blocks. -/
theorem homogeneousH_eq_Book_of_tree (i : Fin 4) (a : Fin 3)
    (h : restrictionTree i a = bookTree i a) (z : BookHT.Blocks) :
    homogeneousH i a (BookHT.TangentCoordinates.V (realCoordinates z)) = BookHT.H z i a := by
  rw [← restrictionTree_evaluate, h, bookTree_evaluate]

end Option2.NativeStress.NativeH.Reproduction

module

public import NativeHQuadraticCore

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators
open BookHT.TangentCoordinates BookHT.Dictionary

theorem filter_zero_sum {α R : Type*} [AddCommMonoid R] (l : List α)
    (p : α → Bool) (f : α → R) (h : ∀ a ∈ l, p a = false → f a = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have hi := ih (fun b hb => h b (by simp [hb]))
      cases hp : p a with
      | false => simp [hp, hi, h a (by simp) hp]
      | true => simp [hp, hi]

theorem sum_pair_product {α β R : Type*} [CommRing R] (c : R)
    (l : List α) (m : List β) (f : α → R) (g : β → R) :
    (l.map fun p => (m.map fun q => c * f p * g q).sum).sum =
      c * ((l.map f).sum * (m.map g).sum) := by
  simp_rw [List.sum_map_mul_left, List.sum_map_mul_right]
  rw [List.sum_map_mul_left]
  ring

theorem columnValue_eq (es : List BookHT.TangentCoordinates.Entry) (r : Fin 1053) :
    columnValue es r = sparseQ12 es r := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [columnValue, sparseQ12, ih]; rfl

theorem columnQ12_eq (b : Fin 24) (r : Fin 1053) :
    columnQ12 b r = d6ColumnQ12 b r := columnValue_eq (d6Entries b) r

theorem coordinateTerms_evaluate (v : Fin 1053) (y : Fin 24 → ℂ) :
    ((coordinateTerms v).map fun e => Q12.toComplex e.2 * y e.1).sum = V y v := by
  unfold coordinateTerms
  rw [filter_zero_sum]
  · simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def,
      columnQ12_eq, d6ColumnQ12_complex, V_apply, eigenColumn]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro e _ he
    have hz : e.2 = 0 := by simpa using he
    simp [hz]

theorem restrictionTerms_bound (i : Fin 4) (a : Fin 3) (e : Nat × Q12)
    (he : e ∈ restrictionTerms i a) : e.1 < 2^10 := by
  obtain ⟨_, _, hx⟩ := List.mem_flatMap.mp he
  obtain ⟨_, _, hy⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hy
  unfold pairKey
  split_ifs <;> omega

theorem restrictionTerms_evaluate (i : Fin 4) (a : Fin 3) (y : Fin 24 → ℂ) :
    ((restrictionTerms i a).map fun e => Q12.toComplex e.2 * pairWeight (by decide) y e.1).sum =
      homogeneousH i a (V y) := by
  rw [← collectedNative_evaluate]
  unfold restrictionTerms
  simp only [List.map_flatMap, sum_flatMap, List.map_map, Function.comp_def,
    map_mul, pairWeight_pairKey]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  change _ = Q12.toComplex e.2 *
    (V y (firstCoordinate e.1) * V y (secondCoordinate e.1))
  rw [← coordinateTerms_evaluate, ← coordinateTerms_evaluate]
  rw [← sum_pair_product]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  apply congrArg List.sum
  apply List.map_congr_left
  intro q _
  ring

theorem restrictionTree_evaluate (i : Fin 4) (a : Fin 3) (y : Fin 24 → ℂ) :
    CoeffTree.evaluate Q12.toComplex (restrictionTree i a) (pairWeight (by decide) y) =
      homogeneousH i a (V y) := by
  rw [restrictionTree, CoeffTree.evaluate_collect Q12.toComplex _ (restrictionTerms_bound i a)]
  exact restrictionTerms_evaluate i a y

end Option2.NativeStress.NativeH.Reproduction

module

public import NativeHQuadraticCompute
public import NativeHEquilibriumTransport
public import BookTangentQ12

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators
open ConfigurationResidualIndices QuarticCertificate.RowBridge
open BookHT.TangentCoordinates

theorem sum_flatMap {α R : Type*} [AddMonoid R] (l : List α) (f : α → List R) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

def pairWeight {R : Type*} [CommRing R] {n : Nat} (hn : 0 < n)
    (x : Fin n → R) (k : Nat) : R :=
  x ⟨(k/n)%n, Nat.mod_lt _ hn⟩ * x ⟨k%n, Nat.mod_lt _ hn⟩

theorem pairWeight_pairKey {R : Type*} [CommRing R] {n : Nat} (hn : 0 < n)
    (x : Fin n → R) (p q : Fin n) : pairWeight hn x (pairKey p q) = x p * x q := by
  unfold pairKey
  split_ifs <;>
    simp [pairWeight, Nat.mul_add_div hn, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, mul_comm]

theorem native_pairKey_bound (p q : Fin 1053) : pairKey p q < 2^21 := by
  unfold pairKey
  split_ifs <;> omega

theorem nativeTerms_bound (i : Fin 4) (a : Fin 3) (e : Nat × Q12)
    (he : e ∈ nativeTerms i a) : e.1 < 2^21 := by
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp he
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
  exact native_pairKey_bound _ _

/-- The homogeneous quadratic contraction in the original 2184-row order. -/
noncomputable def homogeneousH (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) : ℂ :=
  ∑ r : Fin 2184, weightC i a r * quadraticPartValue (1/2 : ℂ) r x

theorem nativeTerms_evaluate (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    ((nativeTerms i a).map fun e => Q12.toComplex e.2 * pairWeight (by decide) x e.1).sum =
      homogeneousH i a x := by
  rw [homogeneousH, weightC_dense_sparse]
  unfold nativeTerms hEntries
  simp only [List.map_flatMap, sum_flatMap, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  simp only [map_mul, orientedQ12_toComplex, map_intCast, pairWeight_pairKey,
    quadraticPartValue, quadTable, rowShape, fNumber.symm_apply_apply, quadraticValue]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  have hs : Q12.toComplex (quadraticScale (Q12.lit 1 0 0 0 2) (labelShape e.label)) =
      quadraticScale (1/2 : ℂ) (labelShape e.label) := by
    simp [quadraticScale, apply_ite Q12.toComplex, Equilibrium.halfQ12_complex]
  rw [hs]
  ring

theorem nativeTree_evaluate (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    CoeffTree.evaluate Q12.toComplex (nativeTree i a) (pairWeight (by decide) x) =
      homogeneousH i a x := by
  rw [nativeTree, CoeffTree.evaluate_collect Q12.toComplex _ (nativeTerms_bound i a)]
  exact nativeTerms_evaluate i a x

theorem collectedNative_evaluate (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    ((collectedNative i a).map fun e => Q12.toComplex e.2 * pairWeight (by decide) x e.1).sum =
      homogeneousH i a x := by
  rw [collectedNative, CoeffTree.entries_evaluate, nativeTree_evaluate]

end Option2.NativeStress.NativeH.Reproduction

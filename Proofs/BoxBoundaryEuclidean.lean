module

public import BoxBoundaryGeometry

@[expose] public section

/-! Euclidean target and endpoint cases for the checked box-face geometry.
These are geometric statements, not numeric dimension assertions. -/
noncomputable section
namespace SmallInductiveEuclideanA7
open Set

theorem isEmbedding_face_toEuclidean {n : ℕ} (a b : Fin (n+1) → ℝ)
    (i : Fin (n+1)) (side : Bool) :
    Topology.IsEmbedding (fun x : boxFace a b i side =>
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm (i.removeNth x.1)) :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toHomeomorph.isEmbedding.comp
    (isEmbedding_face_removeNth a b i side)

theorem frontier_openBox_zero (a b : Fin 0 → ℝ) : frontier (openBox a b) = ∅ := by
  rw [frontier_openBox_eq_faces (fun i => Fin.elim0 i)]
  simp

theorem boxFace_one_subsingleton (a b : Fin 1 → ℝ) (i : Fin 1) (side : Bool) :
    Subsingleton (boxFace a b i side) :=
  ⟨fun _x _y => (isEmbedding_face_removeNth a b i side).injective (Subsingleton.elim _ _)⟩

/-- The finite closed cover needed by a future closed-sum induction is a
cover of the actual boundary subtype, not merely a cover in ambient space. -/
theorem frontier_face_closed_cover {n : ℕ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) :
    (∀ j : Fin n × Bool, IsClosed
      ((Subtype.val : frontier (openBox a b) → (Fin n → ℝ)) ⁻¹' boxFace a b j.1 j.2)) ∧
    (⋃ j : Fin n × Bool,
      ((Subtype.val : frontier (openBox a b) → (Fin n → ℝ)) ⁻¹' boxFace a b j.1 j.2)) = Set.univ := by
  refine ⟨fun j => (isClosed_boxFace a b j.1 j.2).preimage continuous_subtype_val,?_⟩
  apply Set.eq_univ_of_forall
  intro x
  have hx := (Set.ext_iff.1 (frontier_openBox_eq_faces hab) x.1).1 x.2
  obtain ⟨i,side,hi⟩ := Set.mem_iUnion.1 hx |>.imp fun i hi => Set.mem_iUnion.1 hi
  exact Set.mem_iUnion.2 ⟨(i,side),hi⟩

#print axioms isEmbedding_face_toEuclidean
#print axioms frontier_openBox_zero
#print axioms boxFace_one_subsingleton
#print axioms frontier_face_closed_cover
end SmallInductiveEuclideanA7

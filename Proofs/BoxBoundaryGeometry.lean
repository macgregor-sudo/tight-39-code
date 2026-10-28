module

public import Mathlib.Topology.SmallInductiveDimension
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

/-! Exact geometric input to Euclidean small-inductive upper-bound induction.
Uses existing product closure, interval closure, and Fin coordinate insertion/
deletion APIs. No dimension normalization or closed-sum theorem is assumed.
 -/
noncomputable section
namespace SmallInductiveEuclideanA7
open Set TopologicalSpace
open scoped Topology

def openBox {n : ℕ} (a b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Ioo (a i) (b i))
def closedBox {n : ℕ} (a b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Icc (a i) (b i))
def boxFace {n : ℕ} (a b : Fin n → ℝ) (i : Fin n) (upper : Bool) : Set (Fin n → ℝ) :=
  closedBox a b ∩ {x | x i = if upper then b i else a i}

theorem isOpen_openBox {n : ℕ} (a b : Fin n → ℝ) : IsOpen (openBox a b) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem openBox_basis (n : ℕ) :
    IsTopologicalBasis {S : Set (Fin n → ℝ) | ∃ a b, (∀ i, a i < b i) ∧ S = openBox a b} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro S ⟨a,b,_,rfl⟩
    exact isOpen_openBox a b
  · intro x U hx hU
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hx)
    have he : Metric.ball x r = openBox (fun i => x i-r) (fun i => x i+r) := by
      rw [ball_pi x hr]
      simp only [Real.ball_eq_Ioo,openBox]
    refine ⟨_,⟨(fun i => x i-r),(fun i => x i+r),fun i => by linarith,rfl⟩,?_,?_⟩
    · rw [← he]
      exact Metric.mem_ball_self hr
    · rwa [← he]

theorem closure_openBox {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    closure (openBox a b) = closedBox a b := by
  simp only [openBox,closedBox,closure_pi_set,closure_Ioo (hab _).ne]

theorem isClosed_boxFace {n : ℕ} (a b : Fin n → ℝ) (i : Fin n) (upper : Bool) :
    IsClosed (boxFace a b i upper) :=
  (isClosed_set_pi (fun _ _ => isClosed_Icc)).inter
    (isClosed_eq (continuous_apply i) continuous_const)

/-- The frontier is the union of exactly 2n closed coordinate faces.
For n=0 the union is empty, as required. -/
theorem frontier_openBox_eq_faces {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ i, a i < b i) :
    frontier (openBox a b) = ⋃ i : Fin n, ⋃ side : Bool, boxFace a b i side := by
  rw [(isOpen_openBox a b).frontier_eq,closure_openBox hab]
  ext x
  simp only [Set.mem_sdiff,Set.mem_iUnion]
  constructor
  · rintro ⟨hc,ho⟩
    have hcl : ∀ i, a i ≤ x i ∧ x i ≤ b i := fun i => hc i (Set.mem_univ _)
    have hn : ¬ ∀ i, a i < x i ∧ x i < b i := by simpa [openBox] using ho
    obtain ⟨i,hi⟩ := not_forall.1 hn
    have hei : x i = a i ∨ x i = b i := by
      by_cases he : x i = a i
      · exact Or.inl he
      · right
        have ha : a i < x i := lt_of_le_of_ne (hcl i).1 (Ne.symm he)
        have hb : b i ≤ x i := not_lt.1 (fun hlt => hi ⟨ha,hlt⟩)
        exact le_antisymm (hcl i).2 hb
    rcases hei with hl | hu
    · exact ⟨i,false,hc,hl⟩
    · exact ⟨i,true,hc,hu⟩
  · rintro ⟨i,side,hc,he⟩
    refine ⟨hc,?_⟩
    intro ho
    have hlt : a i < x i ∧ x i < b i := ho i (Set.mem_univ _)
    change x i = (if side then b i else a i) at he
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he <;> linarith

/-- Deleting a fixed coordinate is a homeomorphism of its entire hyperplane.
For n=0 this identifies a singleton hyperplane in the line with the point space. -/
def coordinateHyperplaneHomeo {n : ℕ} (i : Fin (n+1)) (c : ℝ) :
    {x : Fin (n+1) → ℝ // x i = c} ≃ₜ (Fin n → ℝ) :=
  { toFun := fun x => i.removeNth x.1
    invFun := fun y => ⟨i.insertNth c y,by simp⟩
    left_inv := fun x => Subtype.ext (by
      change i.insertNth c (i.removeNth x.1) = x.1
      exact (congrArg (fun v : ℝ => i.insertNth v (i.removeNth x.1)) x.2.symm).trans
        (i.insertNth_self_removeNth x.1))
    right_inv := fun y => by
      exact Fin.removeNth_insertNth (α := fun _ : Fin (n+1) => ℝ) i c y
    continuous_toFun := continuous_pi fun j =>
      (continuous_apply (i.succAbove j)).comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (continuous_const : Continuous (fun _ : Fin n → ℝ => c)).finInsertNth i
        (continuous_id : Continuous (fun y : Fin n → ℝ => y)) }

/-- Every closed face has a genuine topological embedding into one fewer
coordinates, obtained by restriction of coordinate deletion. -/
theorem isEmbedding_face_removeNth {n : ℕ} (a b : Fin (n+1) → ℝ)
    (i : Fin (n+1)) (side : Bool) :
    Topology.IsEmbedding (fun x : boxFace a b i side => i.removeNth x.1) := by
  let f : boxFace a b i side → {x : Fin (n+1) → ℝ // x i = if side then b i else a i} :=
    fun x => ⟨x.1,x.2.2⟩
  have hf : Topology.IsEmbedding f := (Topology.IsEmbedding.subtypeVal.of_comp_iff).1
    (show Topology.IsEmbedding (Subtype.val ∘ f) from Topology.IsEmbedding.subtypeVal)
  have he : (coordinateHyperplaneHomeo i (if side then b i else a i)) ∘ f =
      (fun x : boxFace a b i side => i.removeNth x.1) := by rfl
  rw [← he]
  exact (coordinateHyperplaneHomeo i _).isEmbedding.comp hf

#print axioms openBox_basis
#print axioms frontier_openBox_eq_faces
#print axioms isEmbedding_face_removeNth
end SmallInductiveEuclideanA7

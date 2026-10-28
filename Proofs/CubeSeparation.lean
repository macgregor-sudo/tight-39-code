module

public import FixedPointTheorems.apply_cubical_sperner
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.SmallInductiveDimension
public import Mathlib.Tactic

@[expose] public section

/-! An opposite-face separation theorem for Euclidean small inductive
normalization. This proves the geometric content of Engelking, Dimension Theory
(1978), Theorem 1.8.1, via a clamped signed-distance fixed-point map. It does not
assume or establish the small-inductive partition characterization or Euclidean
normalization. First-party proof; the imported cube fixed-point implementation
retains its existing attributed upstream source and qualification.
Reference: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/engelking.pdf, pp72–73.
The fixed-point theorem is supplied by the imported dependency.
-/

noncomputable section
namespace SmallInductiveEuclideanA7
open Set Metric

/-- The strict-face form of Poincaré–Miranda, directly from the actual
qualified cube fixed-point theorem. Includes the zero-dimensional cube. -/
theorem exists_zero_of_strict_cube_faces {n : ℕ}
    (g : (@unit_cube n) → (Fin n → ℝ)) (hg : Continuous g)
    (hlo : ∀ x i, x.1 i = 0 → 0 < g x i)
    (hhi : ∀ x i, x.1 i = 1 → g x i < 0) :
    ∃ x : @unit_cube n, ∀ i, g x i = 0 := by
  let f : C(@unit_cube n,@unit_cube n) :=
    { toFun := fun x => ⟨(fun i => max 0 (min 1 (x.1 i + g x i))),
        (fun i => le_max_left _ _),
        (fun i => max_le (by norm_num) (min_le_left _ _))⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply continuous_pi
        intro i
        exact continuous_const.max (continuous_const.min
          (((continuous_apply i).comp continuous_subtype_val).add
            ((continuous_apply i).comp hg))) }
  obtain ⟨x,hx⟩ := fixed_point_unit_cube f
  refine ⟨x,fun i => ?_⟩
  have he : max 0 (min 1 (x.1 i + g x i)) = x.1 i := congrFun (congrArg Subtype.val hx) i
  have h0 : 0 ≤ x.1 i := x.2.1 i
  have h1 : x.1 i ≤ 1 := x.2.2 i
  rcases lt_trichotomy (g x i) 0 with hn | hz | hp
  · have hxi : 0 < x.1 i := lt_of_le_of_ne h0 (by
      intro h
      have := hlo x i h.symm
      linarith)
    have hc : max 0 (min 1 (x.1 i + g x i)) < x.1 i :=
      max_lt hxi (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    exact False.elim (ne_of_lt hc he)
  · exact hz
  · have hxi : x.1 i < 1 := lt_of_le_of_ne h1 (by
      intro h
      have := hhi x i h
      linarith)
    have hc : x.1 i < max 0 (min 1 (x.1 i + g x i)) :=
      lt_of_lt_of_le (lt_min hxi (by linarith)) (le_max_right _ _)
    exact False.elim (ne_of_lt hc he.symm)

/-- Opposite-face partitions of the actual closed unit cube have a common
point (Engelking 1.8.1). Closedness of each L is implied by the open complement
identity and is not an extra hidden assumption. -/
theorem cube_opposite_face_partitions_intersect {n : ℕ}
    (L U W : Fin n → Set (@unit_cube n))
    (hU : ∀ i, IsOpen (U i)) (hW : ∀ i, IsOpen (W i))
    (hdisj : ∀ i, Disjoint (U i) (W i))
    (hlo : ∀ x i, x.1 i = 0 → x ∈ U i)
    (hhi : ∀ x i, x.1 i = 1 → x ∈ W i)
    (hpart : ∀ i, (L i)ᶜ = U i ∪ W i) :
    ∃ x : @unit_cube n, ∀ i, x ∈ L i := by
  let lo : @unit_cube n := ⟨0,by constructor <;> intro i <;> norm_num⟩
  let hi : @unit_cube n := ⟨1,by constructor <;> intro i <;> norm_num⟩
  have hUc : ∀ i, ((U i)ᶜ).Nonempty := fun i =>
    ⟨hi,fun hx => Set.disjoint_left.1 (hdisj i) hx (hhi hi i rfl)⟩
  have hWc : ∀ i, ((W i)ᶜ).Nonempty := fun i =>
    ⟨lo,fun hx => Set.disjoint_left.1 (hdisj i) (hlo lo i rfl) hx⟩
  let g : (@unit_cube n) → (Fin n → ℝ) :=
    fun x i => infDist x (U i)ᶜ - infDist x (W i)ᶜ
  have hg : Continuous g := continuous_pi fun i =>
    (continuous_infDist_pt _).sub (continuous_infDist_pt _)
  have hpos : ∀ x i, x ∈ U i → 0 < g x i := by
    intro x i hx
    have hd : 0 < infDist x (U i)ᶜ :=
      ((hU i).isClosed_compl.notMem_iff_infDist_pos (hUc i)).1 (by simpa using hx)
    have hz : infDist x (W i)ᶜ = 0 := infDist_zero_of_mem
      (fun hw => Set.disjoint_left.1 (hdisj i) hx hw)
    change 0 < infDist x (U i)ᶜ - infDist x (W i)ᶜ
    rwa [hz,sub_zero]
  have hneg : ∀ x i, x ∈ W i → g x i < 0 := by
    intro x i hx
    have hd : 0 < infDist x (W i)ᶜ :=
      ((hW i).isClosed_compl.notMem_iff_infDist_pos (hWc i)).1 (by simpa using hx)
    have hz : infDist x (U i)ᶜ = 0 := infDist_zero_of_mem
      (fun hu => Set.disjoint_left.1 (hdisj i) hu hx)
    change infDist x (U i)ᶜ - infDist x (W i)ᶜ < 0
    rw [hz]
    linarith
  obtain ⟨x,hx⟩ := exists_zero_of_strict_cube_faces g hg
    (fun x i h => hpos x i (hlo x i h))
    (fun x i h => hneg x i (hhi x i h))
  refine ⟨x,fun i => ?_⟩
  by_contra hn
  have hm : x ∈ U i ∪ W i := by rwa [← hpart i]
  rcases hm with hu | hw
  · have := hpos x i hu
    rw [hx i] at this
    exact (lt_irrefl _ this)
  · have := hneg x i hw
    rw [hx i] at this
    exact (lt_irrefl _ this)

#print axioms exists_zero_of_strict_cube_faces
#print axioms cube_opposite_face_partitions_intersect
end SmallInductiveEuclideanA7

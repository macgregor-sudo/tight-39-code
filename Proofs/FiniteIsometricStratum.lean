module

public import FiniteOrbitMetric
public import Mathlib.Algebra.Group.Subgroup.Actions

@[expose] public section

/-! The actual orbit quotient map is locally isometric on every exact-stabilizer
stratum, including nontrivial and nonnormal stabilizers. The finite gap argument
handles the empty complement directly. No numeric dimension is asserted. -/
noncomputable section
namespace FiniteIsometricStrata
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

def exactStabilizerSet (H : Subgroup G) : Set X := {x | MulAction.stabilizer G x = H}

/-- Exact stabilizer strata are locally closed: the common fixed set of `H`
intersected with the open complement of the other finitely many fixed sets. -/
theorem isLocallyClosed_exactStabilizerSet (H : Subgroup G) :
    IsLocallyClosed (exactStabilizerSet (X := X) H) := by
  classical
  let U : Set X := ⋂ g : {g : G // g ∉ H}, {x : X | g.1 • x ≠ x}
  let Z : Set X := ⋂ g : H, {x : X | g.1 • x = x}
  have hU : IsOpen U := isOpen_iInter_of_finite fun g =>
    (isClosed_eq (continuous_const_smul g.1) continuous_id).isOpen_compl
  have hZ : IsClosed Z := isClosed_iInter fun g =>
    isClosed_eq (continuous_const_smul g.1) continuous_id
  refine ⟨U, Z, hU, hZ, ?_⟩
  ext x
  simp only [exactStabilizerSet, Set.mem_ofPred_eq, Set.mem_inter_iff,
    U, Z, Set.mem_iInter]
  constructor
  · intro hx
    constructor
    · intro g hfix
      apply g.2
      simpa only [hx] using (show g.1 ∈ MulAction.stabilizer G x from hfix)
    · intro g
      have hg : g.1 ∈ MulAction.stabilizer G x := by rw [hx]; exact g.2
      exact hg
  · rintro ⟨hout, hin⟩
    apply Subgroup.ext
    intro g
    constructor
    · intro hg
      by_contra hnot
      exact hout ⟨g, hnot⟩ hg
    · intro hg
      exact hin ⟨g, hg⟩

/-- A positive radius strictly below a quarter of every nonstabilizer displacement.
If the complement is empty, any positive radius works; the proof uses one. -/
theorem exists_quarter_gap (H : Subgroup G) (p : X)
    (hp : p ∈ exactStabilizerSet H) :
    ∃ r : ℝ, 0 < r ∧ ∀ g : G, g ∉ H → 4 * r < dist p (g • p) := by
  classical
  by_cases hne : ({g : G | g ∉ H} : Set G).Nonempty
  · obtain ⟨g, hg, hmin⟩ := Set.exists_min_image {g : G | g ∉ H}
      (fun g => dist p (g • p)) (Set.toFinite _) hne
    have hpos : 0 < dist p (g • p) := by
      apply dist_pos.mpr
      intro heq
      apply hg
      rw [← hp]
      exact heq.symm
    refine ⟨dist p (g • p) / 8, by positivity, ?_⟩
    intro h hh
    have hle := hmin h hh
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro g hg
    exact (hne ⟨g, hg⟩).elim

/-- Pairwise orbit distance is exactly ambient distance in the quarter-gap ball
on the exact-stabilizer stratum. -/
theorem orbitDist_eq_dist_on_stratum_ball (H : Subgroup G) (p : X) (r : ℝ)
    (hgap : ∀ g : G, g ∉ H → 4 * r < dist p (g • p))
    {y z : X} (hz : z ∈ exactStabilizerSet H)
    (hyball : y ∈ Metric.ball p r) (hzball : z ∈ Metric.ball p r) :
    orbitDist (G := G) y z = dist y z := by
  apply le_antisymm (orbitDist_le_dist y z)
  obtain ⟨g, hg⟩ := orbitDist_attained (G := G) y z
  rw [hg]
  by_cases hgH : g ∈ H
  · have hfix : g • z = z := by
      change g ∈ MulAction.stabilizer G z
      rw [hz]
      exact hgH
    rw [hfix]
  · have hy : dist p y < r := by simpa [Metric.mem_ball, dist_comm] using hyball
    have hz' : dist z p < r := hzball
    have h1 := dist_triangle p y (g • p)
    have h2 := dist_triangle y (g • z) (g • p)
    have h3 := dist_triangle y p z
    have h4 := hgap g hgH
    rw [dist_smul] at h2
    rw [dist_comm y p, dist_comm p z] at h3
    linarith

/-- Restricting the actual quotient map to the stratum inside this ball is an
isometry for the quotient metric whose topology is the orbit quotient topology. -/
theorem isometry_quotient_on_stratum_ball (H : Subgroup G) (p : X) (r : ℝ)
    (hgap : ∀ g : G, g ∉ H → 4 * r < dist p (g • p)) :
    Isometry (fun y : (exactStabilizerSet H ∩ Metric.ball p r : Set X) =>
      Quotient.mk (MulAction.orbitRel G X) y.1) := by
  apply Isometry.of_dist_eq
  intro y z
  exact orbitDist_eq_dist_on_stratum_ball H p r hgap z.2.1 y.2.2 z.2.2

/-- Every exact-stabilizer point has an explicitly bounded ball on which the
actual orbit projection, restricted to that stratum, is isometric. -/
theorem quotient_locally_isometric_on_exact_stabilizer (H : Subgroup G) (p : X)
    (hp : p ∈ exactStabilizerSet H) :
    ∃ r : ℝ, 0 < r ∧
      (∀ g : G, g ∉ H → 4 * r < dist p (g • p)) ∧
      Isometry (fun y : (exactStabilizerSet H ∩ Metric.ball p r : Set X) =>
        Quotient.mk (MulAction.orbitRel G X) y.1) := by
  obtain ⟨r, hr, hgap⟩ := exists_quarter_gap H p hp
  exact ⟨r, hr, hgap, isometry_quotient_on_stratum_ball H p r hgap⟩

#print axioms quotient_locally_isometric_on_exact_stabilizer
#print axioms isLocallyClosed_exactStabilizerSet
end FiniteIsometricStrata

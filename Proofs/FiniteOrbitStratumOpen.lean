module

public import FiniteIsometricStratum
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

/-! Open local isometries onto the actual quotient stratum. The quotient stratum
is the image of the exact-H stratum; its preimage is the union of the conjugate
stabilizer strata. No freeness or normality hypothesis occurs. -/
noncomputable section
namespace FiniteIsometricStrata
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

theorem stabilizer_le_of_quarter_gap (H : Subgroup G) (p : X) (r : ℝ)
    (hr : 0 < r) (hgap : ∀ g : G, g ∉ H → 4 * r < dist p (g • p))
    {z : X} (hz : z ∈ Metric.ball p r) : MulAction.stabilizer G z ≤ H := by
  intro g hg
  by_contra hnot
  have hfix : g • z = z := hg
  have h1 := dist_triangle p z (g • p)
  have h2 : dist z (g • p) = dist z p := by
    conv_lhs => lhs; rw [← hfix]
    exact dist_smul g z p
  have h3 := hgap g hnot
  have h4 : dist z p < r := hz
  rw [h2, dist_comm p z] at h1
  linarith

/-- A translate of an exact-H point which enters the small ball again has
stabilizer H: inclusion plus equality of finite stabilizer cardinalities. -/
theorem exactStabilizer_of_smul_mem_ball (H : Subgroup G) (p : X) (r : ℝ)
    (hr : 0 < r) (hgap : ∀ g : G, g ∉ H → 4 * r < dist p (g • p))
    {y : X} (hy : y ∈ exactStabilizerSet H) (g : G)
    (hgy : g • y ∈ Metric.ball p r) : g • y ∈ exactStabilizerSet H := by
  apply Subgroup.eq_of_le_of_card_ge (stabilizer_le_of_quarter_gap H p r hr hgap hgy)
  have heq := Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G)
    (a := y) (b := g • y) rfl).toEquiv
  change MulAction.stabilizer G y = H at hy
  rw [hy] at heq
  exact heq.le

def quotientStratum (H : Subgroup G) : Set (OrbitQuotient G X) :=
  Quotient.mk (MulAction.orbitRel G X) '' exactStabilizerSet H

/-- Exact image identity: the small exact-H patch maps onto the relative metric
ball in its actual quotient stratum. -/
theorem quotient_image_stratum_ball (H : Subgroup G) (p : X) (r : ℝ)
    (hp : p ∈ exactStabilizerSet H) (hr : 0 < r)
    (hgap : ∀ g : G, g ∉ H → 4 * r < dist p (g • p)) :
    Quotient.mk (MulAction.orbitRel G X) ''
      (exactStabilizerSet H ∩ Metric.ball p r) =
      Metric.ball (Quotient.mk (MulAction.orbitRel G X) p) r ∩ quotientStratum H := by
  ext q
  constructor
  · rintro ⟨y, ⟨hy, hyball⟩, rfl⟩
    refine ⟨?_, y, hy, rfl⟩
    change orbitDist (G := G) y p < r
    exact lt_of_le_of_lt (orbitDist_le_dist y p) hyball
  · rintro ⟨hqball, y, hy, rfl⟩
    change orbitDist (G := G) y p < r at hqball
    rw [orbitDist_comm y p] at hqball
    obtain ⟨g, hg⟩ := orbitDist_attained (G := G) p y
    have hgy : g • y ∈ Metric.ball p r := by
      simpa [Metric.mem_ball, dist_comm, ← hg] using hqball
    exact ⟨g • y, ⟨exactStabilizer_of_smul_mem_ball H p r hr hgap hy g hgy, hgy⟩,
      Quotient.sound ⟨g, rfl⟩⟩

/-- The local isometric restriction has open image in the quotient stratum. -/
theorem quotient_stratum_local_isometry_open_range (H : Subgroup G) (p : X)
    (hp : p ∈ exactStabilizerSet H) :
    ∃ r : ℝ, 0 < r ∧
      ∃ f : (exactStabilizerSet H ∩ Metric.ball p r : Set X) → quotientStratum (X := X) H,
        (∀ y, (f y).1 = Quotient.mk (MulAction.orbitRel G X) y.1) ∧
        Isometry f ∧ IsOpen (Set.range f) := by
  obtain ⟨r, hr, hgap⟩ := exists_quarter_gap H p hp
  let f : (exactStabilizerSet H ∩ Metric.ball p r : Set X) → quotientStratum (X := X) H :=
    fun y => ⟨Quotient.mk _ y.1, y.1, y.2.1, rfl⟩
  refine ⟨r, hr, f, fun _ => rfl, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro y z
    exact orbitDist_eq_dist_on_stratum_ball H p r hgap z.2.1 y.2.2 z.2.2
  · have heq : Set.range f = Subtype.val ⁻¹'
        Metric.ball (Quotient.mk (MulAction.orbitRel G X) p) r := by
      ext q
      constructor
      · rintro ⟨y, rfl⟩
        change orbitDist (G := G) y.1 p < r
        exact lt_of_le_of_lt (orbitDist_le_dist y.1 p) y.2.2
      · intro hq
        have hmem : q.1 ∈ Metric.ball (Quotient.mk (MulAction.orbitRel G X) p) r ∩
            quotientStratum H := ⟨hq, q.2⟩
        rw [← quotient_image_stratum_ball H p r hp hr hgap] at hmem
        obtain ⟨y, hy, heq⟩ := hmem
        exact ⟨⟨y, hy⟩, Subtype.ext heq⟩
    rw [heq]
    exact Metric.isOpen_ball.preimage continuous_subtype_val

#print axioms quotient_image_stratum_ball
#print axioms quotient_stratum_local_isometry_open_range
end FiniteIsometricStrata

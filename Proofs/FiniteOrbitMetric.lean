module

public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.Constructions
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! Finite isometric orbit distance, on the actual orbit quotient with its
quotient topology. No free action or normal stabilizer is assumed. -/
noncomputable section
namespace FiniteIsometricStrata
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

theorem exists_minimizer (x y : X) :
    ∃ g : G, ∀ h : G, dist x (g • y) ≤ dist x (h • y) := by
  obtain ⟨g, _, hg⟩ := Set.exists_min_image (Set.univ : Set G)
    (fun g => dist x (g • y)) Set.finite_univ ⟨1, Set.mem_univ _⟩
  exact ⟨g, fun h => hg h (Set.mem_univ _)⟩

def orbitDist (x y : X) : ℝ := dist x ((exists_minimizer (G := G) x y).choose • y)

theorem orbitDist_le (x y : X) (g : G) : orbitDist (G := G) x y ≤ dist x (g • y) :=
  (exists_minimizer (G := G) x y).choose_spec g

theorem orbitDist_attained (x y : X) : ∃ g : G, orbitDist (G := G) x y = dist x (g • y) :=
  ⟨_, rfl⟩

theorem orbitDist_nonneg (x y : X) : 0 ≤ orbitDist (G := G) x y := dist_nonneg

theorem orbitDist_le_dist (x y : X) : orbitDist (G := G) x y ≤ dist x y := by
  simpa using orbitDist_le x y (1 : G)

theorem orbitDist_self (x : X) : orbitDist (G := G) x x = 0 := by
  exact le_antisymm (by simpa using orbitDist_le_dist (G := G) x x) (orbitDist_nonneg x x)

theorem orbitDist_comm (x y : X) : orbitDist (G := G) x y = orbitDist (G := G) y x := by
  suffices h : ∀ x y : X, orbitDist (G := G) x y ≤ orbitDist (G := G) y x from
    le_antisymm (h x y) (h y x)
  intro x y
  obtain ⟨g, hg⟩ := orbitDist_attained (G := G) y x
  calc
    orbitDist (G := G) x y ≤ dist x (g⁻¹ • y) := orbitDist_le x y _
    _ = dist y (g • x) := by
      rw [← dist_smul g x (g⁻¹ • y), smul_inv_smul, dist_comm]
    _ = orbitDist (G := G) y x := hg.symm

theorem orbitDist_triangle (x y z : X) :
    orbitDist (G := G) x z ≤ orbitDist (G := G) x y + orbitDist (G := G) y z := by
  obtain ⟨g, hg⟩ := orbitDist_attained (G := G) x y
  obtain ⟨h, hh⟩ := orbitDist_attained (G := G) y z
  calc
    orbitDist (G := G) x z ≤ dist x ((g * h) • z) := orbitDist_le x z _
    _ ≤ dist x (g • y) + dist (g • y) ((g * h) • z) := dist_triangle _ _ _
    _ = orbitDist (G := G) x y + orbitDist (G := G) y z := by
      rw [mul_smul, dist_smul, ← hg, ← hh]

theorem orbitDist_eq_zero_iff (x y : X) :
    orbitDist (G := G) x y = 0 ↔ MulAction.orbitRel G X x y := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := orbitDist_attained (G := G) x y
    exact MulAction.mem_orbit_iff.mpr ⟨g, (dist_eq_zero.mp (hg.symm.trans h)).symm⟩
  · rintro ⟨g, rfl⟩
    exact le_antisymm (by simpa using orbitDist_le (g • y) y g) (orbitDist_nonneg _ _)

theorem orbitDist_congr {x x' y y' : X}
    (hx : MulAction.orbitRel G X x x') (hy : MulAction.orbitRel G X y y') :
    orbitDist (G := G) x y = orbitDist (G := G) x' y' := by
  have hxx := (orbitDist_eq_zero_iff x x').mpr hx
  have hyy := (orbitDist_eq_zero_iff y y').mpr hy
  have hxx' : orbitDist (G := G) x' x = 0 := (orbitDist_comm x' x).trans hxx
  have hyy' : orbitDist (G := G) y' y = 0 := (orbitDist_comm y' y).trans hyy
  have h1 := orbitDist_triangle (G := G) x x' y
  have h2 := orbitDist_triangle (G := G) x' y' y
  have h3 := orbitDist_triangle (G := G) x' x y'
  have h4 := orbitDist_triangle (G := G) x y y'
  linarith

abbrev OrbitQuotient (G X : Type*) [Group G] [MulAction G X] := Quotient (MulAction.orbitRel G X)

def quotientDist : OrbitQuotient G X → OrbitQuotient G X → ℝ :=
  Quotient.lift₂ (orbitDist (G := G)) (fun _ _ _ _ hx hy => orbitDist_congr hx hy)

theorem quotientDist_mk (x y : X) :
    quotientDist (Quotient.mk (MulAction.orbitRel G X) x)
      (Quotient.mk (MulAction.orbitRel G X) y) = orbitDist (G := G) x y := rfl

theorem quotientDist_topology (s : Set (OrbitQuotient G X)) :
    IsOpen s ↔ ∀ q ∈ s, ∃ ε > 0, ∀ q', quotientDist q q' < ε → q' ∈ s := by
  constructor
  · intro hs q
    induction q using Quotient.inductionOn with | h x => ?_
    intro hx
    change IsOpen ((Quotient.mk (MulAction.orbitRel G X)) ⁻¹' s) at hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨ε, hε, ?_⟩
    intro q'
    induction q' using Quotient.inductionOn with | h y => ?_
    intro hxy
    change orbitDist (G := G) x y < ε at hxy
    obtain ⟨g, hg⟩ := orbitDist_attained (G := G) x y
    have hmem : Quotient.mk (MulAction.orbitRel G X) (g • y) ∈ s :=
      hball (by simpa [Metric.mem_ball, dist_comm, ← hg] using hxy)
    have heq : Quotient.mk (MulAction.orbitRel G X) (g • y) =
        Quotient.mk (MulAction.orbitRel G X) y := Quotient.sound ⟨g, rfl⟩
    rwa [heq] at hmem
  · intro hs
    change IsOpen ((Quotient.mk (MulAction.orbitRel G X)) ⁻¹' s)
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε, hε, hball⟩ := hs (Quotient.mk _ x) hx
    refine ⟨ε, hε, ?_⟩
    intro y hy
    apply hball (Quotient.mk _ y)
    exact lt_of_le_of_lt (orbitDist_le_dist (G := G) x y)
      (by simpa [Metric.mem_ball, dist_comm] using hy)

/-- The quotient metric retains the pre-existing quotient topology definitionally. -/
instance orbitQuotientMetricSpace : MetricSpace (OrbitQuotient G X) :=
  MetricSpace.ofDistTopology quotientDist
    (fun q => Quotient.inductionOn q (orbitDist_self (G := G)))
    (fun q q' => Quotient.inductionOn₂ q q' (orbitDist_comm (G := G)))
    (fun q q' q'' => Quotient.inductionOn₃ q q' q'' (orbitDist_triangle (G := G)))
    quotientDist_topology
    (fun q q' => Quotient.inductionOn₂ q q'
      (fun x y h => Quotient.sound ((orbitDist_eq_zero_iff x y).mp h)))

theorem dist_quotient_mk (x y : X) :
    dist (Quotient.mk (MulAction.orbitRel G X) x)
      (Quotient.mk (MulAction.orbitRel G X) y) = orbitDist (G := G) x y := rfl

#print axioms orbitQuotientMetricSpace

end FiniteIsometricStrata

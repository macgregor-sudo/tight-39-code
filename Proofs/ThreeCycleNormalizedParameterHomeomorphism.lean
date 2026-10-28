module

public import ThreeCycleNormalizedTopology
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
Explicit topological parameter identifications for the actual normalized family.
The imported topology and continuity results provide the parameter identifications.

The matrix factor is explicitly the original special-unitary matrix subtype
modulo cubic scalar multiplication. No name alone identifies it with a separate
standard PSU(3) object. The phase factor is identified with mathlib's standard
Circle × Circle by an actual homeomorphism. No immersion, native-frame topology,
analytic structure or exhaustion is claimed. First-party composition of retained
project definitions and pinned mathlib APIs; no upstream proof body is copied.
Thanks to the Lean and mathlib contributors; their imported notices are retained.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

/-- The original matrix carrier, with exactly the original equations. -/
abbrev SpecialUnitaryParameter := {Q : Mat // IsSpecialUnitary Q}

/-- The central relation on the matrix factor alone. -/
def matrixCentralRelation (Q Q' : SpecialUnitaryParameter) : Prop :=
  ∃ c : ℂ, c ^ 3 = 1 ∧ Q'.val = c • Q.val

private def constantPhase : PhaseTriple := ⟨fun _ => 1, by constructor <;> simp⟩

private theorem fixedPhase_fibres (Q Q' : SpecialUnitaryParameter) :
    normalizedFamily Q.val constantPhase = normalizedFamily Q'.val constantPhase ↔
      matrixCentralRelation Q Q' := by
  simpa [matrixCentralRelation] using
    normalizedFamily_eq_iff Q.val Q'.val constantPhase constantPhase Q.property Q'.property

/-- The explicit cubic-scalar equivalence, without an opaque kernel relation. -/
def matrixCentralSetoid : Setoid SpecialUnitaryParameter where
  r := matrixCentralRelation
  iseqv := by
    exact {
      refl := fun Q => (fixedPhase_fibres Q Q).mp rfl
      symm := fun h => (fixedPhase_fibres _ _).mp ((fixedPhase_fibres _ _).mpr h).symm
      trans := fun h h' => (fixedPhase_fibres _ _).mp
        (((fixedPhase_fibres _ _).mpr h).trans ((fixedPhase_fibres _ _).mpr h')) }

/-- The standard quotient topology on the displayed matrix relation. -/
abbrev MatrixCentralQuotient := Quotient matrixCentralSetoid

private def fixedPhaseFamily : MatrixCentralQuotient → Family :=
  Quotient.lift (fun Q => normalizedFamily Q.val constantPhase)
    (fun Q Q' h => (fixedPhase_fibres Q Q').mpr h)

private theorem continuous_fixedPhaseFamily : Continuous fixedPhaseFamily := by
  apply Continuous.quotient_lift
  exact continuous_normalizedFamily.comp (continuous_subtype_val.prodMk continuous_const)

private theorem injective_fixedPhaseFamily : Function.Injective fixedPhaseFamily := by
  intro x y
  induction x using Quotient.inductionOn with | h Q =>
    induction y using Quotient.inductionOn with | h Q' =>
      intro h
      exact Quotient.sound ((fixedPhase_fibres Q Q').mp h)

instance t2Space_matrixCentralQuotient : T2Space MatrixCentralQuotient :=
  T2Space.of_injective_continuous injective_fixedPhaseFamily continuous_fixedPhaseFamily

/-- Separate the unchanged phase triple from the central matrix quotient. -/
def centralQuotientToProduct : CentralQuotient → MatrixCentralQuotient × PhaseTriple :=
  Quotient.lift (fun x => (Quotient.mk matrixCentralSetoid x.1, x.2)) (by
    intro x y h
    exact Prod.ext (Quotient.sound h.2) h.1)

/-- Join a cubic-scalar matrix class and its phase triple. -/
def productToCentralQuotient (x : MatrixCentralQuotient × PhaseTriple) : CentralQuotient :=
  Quotient.lift (fun Q => Quotient.mk centralSetoid (Q, x.2))
    (fun Q Q' h => Quotient.sound (show centralRelation (Q, x.2) (Q', x.2) from ⟨rfl, h⟩)) x.1

def centralQuotientProductEquiv : CentralQuotient ≃ MatrixCentralQuotient × PhaseTriple where
  toFun := centralQuotientToProduct
  invFun := productToCentralQuotient
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h x => rfl
  right_inv := by
    rintro ⟨x, d⟩
    induction x using Quotient.inductionOn with | h Q => rfl

theorem continuous_centralQuotientToProduct : Continuous centralQuotientToProduct := by
  apply Continuous.quotient_lift
  exact (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd

/-- An actual homeomorphism for the quotient of the product. -/
def centralQuotientProductHomeomorph : CentralQuotient ≃ₜ MatrixCentralQuotient × PhaseTriple :=
  Continuous.homeoOfEquivCompactToT2 (f := centralQuotientProductEquiv)
    continuous_centralQuotientToProduct

theorem centralQuotientProductHomeomorph_mk (Q : SpecialUnitaryParameter) (d : PhaseTriple) :
    centralQuotientProductHomeomorph (Quotient.mk centralSetoid (Q, d)) =
      (Quotient.mk matrixCentralSetoid Q, d) := rfl

private theorem phase_norm_eq_one (d : PhaseTriple) (j : Index) : ‖d.val j‖ = 1 := by
  have h := d.property.1 j
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (d.val j)]

/-- A phase entry as a point of mathlib's standard unit circle. -/
def phaseCircle (d : PhaseTriple) (j : Index) : Circle :=
  ⟨d.val j, by exact mem_sphere_zero_iff_norm.mpr (phase_norm_eq_one d j)⟩

/-- Complete two circle coordinates with the inverse of their product. -/
def phaseOfCircles (z : Circle × Circle) : PhaseTriple := by
  let a : ℂ := z.1
  let b : ℂ := z.2
  have ha : Complex.normSq a = 1 := Circle.normSq_coe z.1
  have hb : Complex.normSq b = 1 := Circle.normSq_coe z.2
  have hn : a * b ≠ 0 := mul_ne_zero (Circle.coe_ne_zero z.1) (Circle.coe_ne_zero z.2)
  refine ⟨fun j => if j = 0 then a else if j = 1 then b else (a * b)⁻¹, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact ha
    · exact hb
    · simp [map_inv₀, map_mul, ha, hb]
  · change (∏ j : Index, if j = 0 then a else if j = 1 then b else (a * b)⁻¹) = 1
    exact (Fin.prod_univ_three (fun j : Index =>
      if j = 0 then a else if j = 1 then b else (a * b)⁻¹)).trans (by
        change a * b * (a * b)⁻¹ = 1
        exact mul_inv_cancel₀ hn)

private theorem phaseOfCircles_leftInverse (d : PhaseTriple) :
    phaseOfCircles (phaseCircle d 0, phaseCircle d 1) = d := by
  apply Subtype.ext
  funext j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 :=
    (by decide : ∀ i : Index, i = 0 ∨ i = 1 ∨ i = 2) j
  rcases hj with rfl | rfl | rfl
  · simp [phaseOfCircles, phaseCircle]
  · simp [phaseOfCircles, phaseCircle]
  · simp only [phaseOfCircles, show (2 : Index) ≠ 0 by decide,
      show (2 : Index) ≠ 1 by decide, ↓reduceIte]
    change (d.val 0 * d.val 1)⁻¹ = d.val 2
    have hn : d.val 0 * d.val 1 ≠ 0 :=
      mul_ne_zero (Circle.coe_ne_zero (phaseCircle d 0)) (Circle.coe_ne_zero (phaseCircle d 1))
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn]
    exact ((Fin.prod_univ_three d.val).symm.trans d.property.2).symm

def phaseTripleEquiv : PhaseTriple ≃ Circle × Circle where
  toFun d := (phaseCircle d 0, phaseCircle d 1)
  invFun := phaseOfCircles
  left_inv := by exact phaseOfCircles_leftInverse
  right_inv := by
    intro z
    apply Prod.ext <;> apply Circle.ext <;> simp [phaseCircle, phaseOfCircles]

theorem continuous_phaseCircle (j : Index) : Continuous (fun d => phaseCircle d j) := by
  apply Continuous.subtype_mk
  exact (continuous_apply j).comp continuous_subtype_val

/-- The original norm-one/product-one phases are homeomorphic to two circles. -/
def phaseTripleHomeomorph : PhaseTriple ≃ₜ Circle × Circle :=
  Continuous.homeoOfEquivCompactToT2 (f := phaseTripleEquiv)
    ((continuous_phaseCircle 0).prodMk (continuous_phaseCircle 1))

theorem phaseTripleHomeomorph_apply (d : PhaseTriple) :
    phaseTripleHomeomorph d = (phaseCircle d 0, phaseCircle d 1) := rfl

theorem phaseTripleHomeomorph_symm_apply (z : Circle × Circle) :
    phaseTripleHomeomorph.symm z = phaseOfCircles z := rfl

/-- The exact central quotient split into its matrix factor and two circles. -/
def centralQuotientCircleHomeomorph : CentralQuotient ≃ₜ MatrixCentralQuotient × (Circle × Circle) :=
  centralQuotientProductHomeomorph.trans
    ((Homeomorph.refl MatrixCentralQuotient).prodCongr phaseTripleHomeomorph)

/-- The existing descended family in the explicit product-of-circles coordinates. -/
def circleParameterizedNormalizedFamily : MatrixCentralQuotient × (Circle × Circle) → Family :=
  descendedNormalizedFamily ∘ centralQuotientCircleHomeomorph.symm

/-- Representative binding to the existing normalized family and explicit phases. -/
theorem circleParameterizedNormalizedFamily_mk (Q : SpecialUnitaryParameter) (z : Circle × Circle) :
    circleParameterizedNormalizedFamily (Quotient.mk matrixCentralSetoid Q, z) =
      normalizedFamily Q.val (phaseOfCircles z) := rfl

/-- Transfer of the already proved closed embedding along the actual homeomorphism. -/
theorem isClosedEmbedding_circleParameterizedNormalizedFamily :
    Topology.IsClosedEmbedding circleParameterizedNormalizedFamily :=
  isClosedEmbedding_descendedNormalizedFamily.comp centralQuotientCircleHomeomorph.symm.isClosedEmbedding

end UnitaryErrorBases.ThreeCycleNormalized

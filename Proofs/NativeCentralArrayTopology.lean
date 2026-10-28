module

public import NativeComplementaryConstruction
public import NativePolynomialEvaluationStaged
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-!
Closed embeddings of the accepted actual native central triples and their
Fin9 arrays into the existing full upper-coordinate ambient space. The map
uses the native constructors unchanged, with a fixed independently chosen
forward/reverse order per frame. The continuous inverse reads original
outcome0, decodes all27 native coordinates and returns three times its hidden
matrix. No topology instance is installed on Glennie.Albert; the topology is
the ordinary finite Pi/product topology already used by original-F analysis.
Arbitrary matrices are embedded as affine native data, not asserted to be
states or frames. No scalar-representative, quotient or immersion conclusion is made here.
First-party composition of accepted coordinate/constructor identities and the
pinned Mathlib continuous-left-inverse closed-embedding theorem. Imported
owners retain their licences and attribution. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert.NativeCentralArrayTopology

open NativePolynomial
open UnitaryErrorBases.ThreeCycleFourier
open scoped Matrix.Norms.Elementwise

/-- Existing native central triples followed by every original upper coordinate.
Outcome0 agrees in both orientations. -/
def centralTripleCoordinates (reverse : Bool) (U : TitsComplexMatrix) :
    Fin 3 → Fin 27 → ℝ :=
  fun k => upperCoordinates
    ((if reverse then nativeReverseCentralTriple U else nativeCentralTriple U) k)

/-- The inverse uses the existing native decoder and actual hidden matrix. -/
def recoverCentralMatrix (p : Fin 3 → Fin 27 → ℝ) : TitsComplexMatrix :=
  (3 : ℂ) • (nativeTitsMatrixPair (fromUpperCoordinates (p 0))).2

/-- Independent fixed orientation choices, with all original r,k labels. -/
def centralArrayCoordinates (reverse : Fin 9 → Bool)
    (U : Fin 9 → TitsComplexMatrix) : Fin 9 → Fin 3 → Fin 27 → ℝ :=
  fun r => centralTripleCoordinates (reverse r) (U r)

def recoverCentralArray (p : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    Fin 9 → TitsComplexMatrix := fun r => recoverCentralMatrix (p r)

private def decode : TitsCoordinates →L[ℝ] (Fin 27 → ℝ) :=
  (upperCoordinateEquiv.toLinearMap.comp
    compactTitsCoordinateEquiv.symm.toLinearMap).toContinuousLinearMap

private def encode : (Fin 27 → ℝ) →L[ℝ] TitsCoordinates :=
  (compactTitsCoordinateEquiv.toLinearMap.comp
    upperCoordinateEquiv.symm.toLinearMap).toContinuousLinearMap

private theorem continuous_point_coordinates :
    Continuous (fun U : TitsComplexMatrix => upperCoordinates (nativeComplementaryPoint U)) := by
  change Continuous (fun U : TitsComplexMatrix =>
    decode ((fun _ => (1 / 3 : ℝ)), 0, (1 / 3 : ℂ) • U))
  have hscale : Continuous (fun U : TitsComplexMatrix => (1 / 3 : ℂ) • U) :=
    continuous_const_smul _
  exact decode.continuous.comp
    (continuous_const.prodMk (continuous_const.prodMk hscale))

theorem continuous_centralTripleCoordinates (reverse : Bool) :
    Continuous (centralTripleCoordinates reverse) := by
  apply continuous_pi
  intro k
  have hphase (c : ℂ) : Continuous (fun U : TitsComplexMatrix =>
      upperCoordinates (nativeComplementaryPoint (c • U))) :=
    continuous_point_coordinates.comp (continuous_const_smul c)
  cases reverse
  · fin_cases k
    · exact continuous_point_coordinates
    · exact hphase omega
    · exact hphase (omega ^ 2)
  · fin_cases k
    · exact continuous_point_coordinates
    · exact hphase (omega ^ 2)
    · exact hphase omega

theorem continuous_recoverCentralMatrix : Continuous recoverCentralMatrix := by
  change Continuous (fun p : Fin 3 → Fin 27 → ℝ => (3 : ℂ) • (encode (p 0)).2.2)
  have heval : Continuous (fun p : Fin 3 → Fin 27 → ℝ => p 0) := continuous_apply 0
  have he : Continuous (fun p : Fin 3 → Fin 27 → ℝ => encode (p 0)) :=
    encode.continuous.comp heval
  exact he.snd.snd.const_smul (3 : ℂ)

theorem recoverCentralMatrix_leftInverse (reverse : Bool) :
    Function.LeftInverse recoverCentralMatrix (centralTripleCoordinates reverse) := by
  intro U
  change (3 : ℂ) • (nativeTitsMatrixPair (fromUpperCoordinates
    (upperCoordinates ((if reverse then nativeReverseCentralTriple U
      else nativeCentralTriple U) 0)))).2 = U
  rw [fromUpperCoordinates_upperCoordinates]
  cases reverse <;> exact nativeComplementaryPoint_scaled_hidden U

theorem isClosedEmbedding_centralTripleCoordinates (reverse : Bool) :
    Topology.IsClosedEmbedding (centralTripleCoordinates reverse) :=
  (recoverCentralMatrix_leftInverse reverse).isClosedEmbedding
    continuous_recoverCentralMatrix (continuous_centralTripleCoordinates reverse)

theorem continuous_centralArrayCoordinates (reverse : Fin 9 → Bool) :
    Continuous (centralArrayCoordinates reverse) :=
  continuous_pi fun r => (continuous_centralTripleCoordinates (reverse r)).comp (continuous_apply r)

theorem continuous_recoverCentralArray : Continuous recoverCentralArray :=
  continuous_pi fun r => continuous_recoverCentralMatrix.comp (continuous_apply r)

theorem recoverCentralArray_leftInverse (reverse : Fin 9 → Bool) :
    Function.LeftInverse recoverCentralArray (centralArrayCoordinates reverse) := by
  intro U
  funext r
  exact recoverCentralMatrix_leftInverse (reverse r) (U r)

theorem isClosedEmbedding_centralArrayCoordinates (reverse : Fin 9 → Bool) :
    Topology.IsClosedEmbedding (centralArrayCoordinates reverse) :=
  (recoverCentralArray_leftInverse reverse).isClosedEmbedding
    continuous_recoverCentralArray (continuous_centralArrayCoordinates reverse)

end CompactAlbert.NativeCentralArrayTopology

module

public import BookTangentPairing
public import BookEigenIndexCompatibilityUniversal
public import BookRealFormTransport

set_option Elab.async false

@[expose] public section

/-!
The supplied D6 columns keep their original recursive sparse interpretation.
The exact eigenvector permutation and Book real structure yield real packed
coordinates, with an explicit equality to the supplied double sum. This is not
native tangent membership, point/basis or metric identification, or lambda L/Q.

-/

noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open scoped BigOperators ComplexConjugate
open Dictionary

attribute [local irreducible] sparseValue d6Entries

/-- The original sparse D6 column, in sheet order `6*s+k`. -/
def d6Column (b : Fin 24) : AnchorSupport.Ambient :=
  fun r => sparseValue (d6Entries b) r

theorem d6Column_bar (b : Fin 24) (r : Fin 1053) :
    d6Column (basisBar b) r = -conj (d6Column b r) := by
  change sparseValue (d6Entries (basisBar b)) r =
    -conj (sparseValue (d6Entries b) r)
  have hlist : d6Entries (basisBar b) = (d6Entries b).map negConjEntry :=
    d6Entries_bar b
  have heval : sparseValue (d6Entries (basisBar b)) r =
      sparseValue ((d6Entries b).map negConjEntry) r :=
    congrArg (fun es : List Entry => sparseValue es r) hlist
  exact Eq.trans heval (sparseValue_negConj (d6Entries b) r)

/-- Unit-vector coefficients in the supplied 24-eigenvector order. -/
def eigenCoefficient (j b : Fin 24) : ℂ := if b = eigenIndex j then 1 else 0

def eigenColumn (j : Fin 24) : AnchorSupport.Ambient := d6Column (eigenIndex j)

theorem eigenColumn_eq_sum (j : Fin 24) (r : Fin 1053) :
    eigenColumn j r = ∑ b, eigenCoefficient j b * d6Column b r := by
  simp [eigenCoefficient, eigenColumn]

theorem eigenColumn_bar (j : Fin 24) (r : Fin 1053) :
    eigenColumn (coordinateBar j) r = -conj (eigenColumn j r) := by
  change d6Column (eigenIndex (coordinateBar j)) r =
    -conj (d6Column (eigenIndex j) r)
  rw [eigenIndex_coordinateBar]
  exact d6Column_bar (eigenIndex j) r

/-- The supplied complex coefficient map, preserving all 1053 ambient labels. -/
def V : (Fin 24 → ℂ) →ₗ[ℂ] AnchorSupport.Ambient :=
  BookRealFormTransport.linearCombination eigenColumn

theorem V_apply (y : Fin 24 → ℂ) (r : Fin 1053) :
    V y r = ∑ j, y j * eigenColumn j r := rfl

theorem V_eq_supplied_sum (y : Fin 24 → ℂ) (r : Fin 1053) :
    V y r = ∑ j, y j * (∑ b, eigenCoefficient j b *
      sparseValue (d6Entries b) r) := by
  change (∑ j, y j * eigenColumn j r) =
    ∑ j, y j * (∑ b, eigenCoefficient j b * d6Column b r)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c : ℂ => y j * c) (eigenColumn_eq_sum j r)

theorem conj_V_of_realStructure (y : Fin 24 → ℂ)
    (hy : ∀ j, y (coordinateBar j) = -conj (y j)) (r : Fin 1053) :
    conj (V y r) = V y r :=
  BookRealFormTransport.linearCombination_conj coordinateBar coordinateBar_involutive
    eigenColumn eigenColumn_bar y hy r

/-- A real linear restriction to the exact Book real-structure submodule. -/
def realRestriction : BookRealFormTransport.realForm coordinateBar →ₗ[ℝ]
    (Fin 1053 → ℝ) :=
  BookRealFormTransport.realPartRestriction coordinateBar eigenColumn

theorem realRestriction_complex (y : BookRealFormTransport.realForm coordinateBar)
    (r : Fin 1053) : (realRestriction y r : ℂ) = V y.val r :=
  BookRealFormTransport.realPartRestriction_complex coordinateBar coordinateBar_involutive
    eigenColumn eigenColumn_bar y r

theorem V_realCoordinates_conj (z : Blocks) (r : Fin 1053) :
    conj (V (realCoordinates z) r) = V (realCoordinates z) r :=
  conj_V_of_realStructure (realCoordinates z) (realCoordinates_bar z) r

theorem V_realCoordinates_im (z : Blocks) (r : Fin 1053) :
    (V (realCoordinates z) r).im = 0 :=
  Complex.conj_eq_iff_im.mp (V_realCoordinates_conj z r)

/-- Real packed coordinates; native tangent membership remains unasserted. -/
def realV (z : Blocks) : Fin 1053 → ℝ :=
  realRestriction ⟨realCoordinates z, realCoordinates_bar z⟩

theorem realV_complex (z : Blocks) (r : Fin 1053) :
    (realV z r : ℂ) = V (realCoordinates z) r :=
  realRestriction_complex ⟨realCoordinates z, realCoordinates_bar z⟩ r

end Option2.NativeStress.BookHT.TangentCoordinates

open Option2.NativeStress.BookHT.TangentCoordinates

#check @d6Column_bar
#check @eigenColumn_bar
#check @V_eq_supplied_sum
#check @realRestriction_complex
#check @V_realCoordinates_im
#check @realV_complex
#print axioms d6Column_bar
#print axioms eigenColumn_bar
#print axioms V_eq_supplied_sum
#print axioms realRestriction_complex
#print axioms V_realCoordinates_im
#print axioms realV_complex

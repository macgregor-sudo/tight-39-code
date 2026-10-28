module

public import HTPhaseKronCore

@[expose] public section

/-! # Data representation of the pure T covectors (first-party)

The JSON row carries: original row index, Q12 literal `(A, B, C, D, N)`, twelve plane-lattice exponents `m_j`
(character `∏_j χ_j^{m_j}` of the α-lines of the 12 planes) and four literal u-exponents. The typed data module keeps
the label (↦ row index through `fNumber`), the literal and the u-exponents; `HTPCovRepXY` keeps row index and `m`.

`litPlaneChar j` is the literal plane-character map (PHASE P13): planes 2, 7, 9 ↦ u0⁻¹, u1, u0·u1;
planes 3, 5, 10 ↦ u2, u3⁻¹, u2·u3; planes 0, 1, 4, 6, 8, 11 (windows 0, 1) ↦ 1.
`litPlaneChar_eq_planeExp` proves it is the map `planeExp` that defines the phased configuration `PhiR`. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseComplete
open HTPhaseKron

def Ex.zero : Ex := (0, 0, 0, 0)
def Ex.smul (a : Int) (x : Ex) : Ex := (a * x.1, a * x.2.1, a * x.2.2.1, a * x.2.2.2)

/-- Literal plane-character exponents of planes 0..11 (PHASE P13). -/
def litPlaneChar : List Ex :=
  [(0, 0, 0, 0), (0, 0, 0, 0), (-1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 0, 0), (0, 0, 0, -1),
   (0, 0, 0, 0), (0, 1, 0, 0), (0, 0, 0, 0), (1, 1, 0, 0), (0, 0, 1, 1), (0, 0, 0, 0)]

/-- The literal map is the one used by the phased configuration (`planeExp`, `none` = character 1). -/
theorem litPlaneChar_eq_planeExp :
    ∀ j : Fin 12, (planeExp j.val).getD Ex.zero = litPlaneChar.getD j.val Ex.zero := by
  decide

/-- One JSON row as kept here: original row index and the twelve plane-lattice exponents. -/
structure PRow where
  row : ℕ
  m : List Int

/-- Image of plane-lattice exponents under the literal plane-character map. -/
def litImage (m : List Int) : Ex :=
  (List.zipWith Ex.smul m litPlaneChar).foldr Ex.add Ex.zero

end Option2.NativeStress.HTPhaseComplete

module

public import PointShape
public import Q12

/-!
# Exact Q12 scalar inputs for the accepted CKM point

`q12Consts : PointShape.Consts Q12`: 1/3, the characters 1, ω, ω² split into
real/imaginary parts (each in ℚ(√3)), and the four exact rational phases
(3+4i)/5, (5+12i)/13, (15+8i)/17, (21+20i)/29 split likewise. All entries
are `Q12.lit` literals (briefs/Q12-LITERAL-FORMAT.md).
First-party, no borrowed text.
-/

@[expose] public section

namespace FourSheets.PointQ12

open FourSheets.PointShape

def charReQ : Fin 3 → Q12 := ![Q12.lit 1 0 0 0 1, Q12.lit (-1) 0 0 0 2, Q12.lit (-1) 0 0 0 2]
def charImQ : Fin 3 → Q12 := ![Q12.lit 0 0 0 0 1, Q12.lit 0 0 1 0 2, Q12.lit 0 0 (-1) 0 2]
def phaseReQ : Fin 4 → Q12 :=
  ![Q12.lit 3 0 0 0 5, Q12.lit 5 0 0 0 13, Q12.lit 15 0 0 0 17, Q12.lit 21 0 0 0 29]
def phaseImQ : Fin 4 → Q12 :=
  ![Q12.lit 4 0 0 0 5, Q12.lit 12 0 0 0 13, Q12.lit 8 0 0 0 17, Q12.lit 20 0 0 0 29]

def q12Consts : Consts Q12 :=
  ⟨Q12.lit 1 0 0 0 3, fun r => charReQ r, fun r => charImQ r, phaseReQ, phaseImQ⟩

end FourSheets.PointQ12

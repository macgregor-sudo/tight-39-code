module

public import NativeHQuadraticCompute

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open ConfigurationResidualIndices QuarticCertificate.RowBridge
open BookHT.TangentCoordinates

/-- Evaluate only a nonzero cross product; no arithmetic is changed. -/
def nonzeroProduct (x y : Q12) : Q12 :=
  if x = 0 then 0 else if y = 0 then 0 else x*y

theorem nonzeroProduct_eq (x y : Q12) : nonzeroProduct x y = x*y := by
  by_cases hx : x=0 <;> by_cases hy : y=0 <;> simp [nonzeroProduct,hx,hy]

noncomputable def termCoefficient (j k : Fin 24) (p q : Fin 1053) : Q12 :=
  nonzeroProduct (columnQ12 (eigenIndex j) p) (columnQ12 (eigenIndex k) q) +
    if j=k then 0 else
      nonzeroProduct (columnQ12 (eigenIndex k) p) (columnQ12 (eigenIndex j) q)

/-- One symmetric monomial coefficient, evaluated directly from actual native
rows. This is an alternate evaluation order, not new coefficient data. -/
noncomputable def nativeCoefficient (i : Fin 4) (a : Fin 3) (j k : Fin 24) : Q12 :=
  ((rawEntries i a).map fun e =>
    let s := labelShape e.label
    let v := (s.quadratic.map fun t =>
      let d := termCoefficient j k t.1 t.2.1
      if d = 0 then 0 else quadraticScale (Q12.lit 1 0 0 0 2) s * (t.2.2 : Q12) * d).sum
    if v = 0 then 0 else orientedQ12 (hSpec i a) e.coefficient * v).sum

def bookCoefficient (i : Fin 4) (a : Fin 3) (j k : Fin 24) : Q12 :=
  ((bookTerms i a).map fun e => if e.1 = pairKey j k then e.2 else 0).sum

end Option2.NativeStress.NativeH.Reproduction

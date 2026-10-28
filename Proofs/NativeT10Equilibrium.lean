module

public import NativeT10Block0
public import NativeT10Block1
public import NativeT10Block2
public import NativeT10Block3
public import NativeT10Block4
public import NativeT10Block5
public import NativeT10Block6

@[expose] public section

set_option Elab.async false
namespace Option2.NativeStress.NativeT
open NativeH NativeH.Equilibrium NativePolynomial.ConfigurationResiduals

theorem t10_all_points : ∀ (p : Fin 39) (k : Fin 27),
    fastContraction lambda6 ⟨6, false, false⟩ (Q12.lit 1 0 0 0 2) baseQ12
      (variableIndex p k) = 0 := by
  intro p k
  fin_cases p
  · exact t10_block0 0 k
  · exact t10_block0 1 k
  · exact t10_block0 2 k
  · exact t10_block0 3 k
  · exact t10_block0 4 k
  · exact t10_block0 5 k
  · exact t10_block1 0 k
  · exact t10_block1 1 k
  · exact t10_block1 2 k
  · exact t10_block1 3 k
  · exact t10_block1 4 k
  · exact t10_block1 5 k
  · exact t10_block2 0 k
  · exact t10_block2 1 k
  · exact t10_block2 2 k
  · exact t10_block2 3 k
  · exact t10_block2 4 k
  · exact t10_block2 5 k
  · exact t10_block3 0 k
  · exact t10_block3 1 k
  · exact t10_block3 2 k
  · exact t10_block3 3 k
  · exact t10_block3 4 k
  · exact t10_block3 5 k
  · exact t10_block4 0 k
  · exact t10_block4 1 k
  · exact t10_block4 2 k
  · exact t10_block4 3 k
  · exact t10_block4 4 k
  · exact t10_block4 5 k
  · exact t10_block5 0 k
  · exact t10_block5 1 k
  · exact t10_block5 2 k
  · exact t10_block5 3 k
  · exact t10_block5 4 k
  · exact t10_block5 5 k
  · exact t10_block6 0 k
  · exact t10_block6 1 k
  · exact t10_block6 2 k

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.t10_all_points

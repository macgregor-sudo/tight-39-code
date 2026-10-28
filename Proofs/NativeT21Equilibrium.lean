module

public import NativeT21Block0
public import NativeT21Block1
public import NativeT21Block2
public import NativeT21Block3
public import NativeT21Block4
public import NativeT21Block5
public import NativeT21Block6

@[expose] public section

set_option Elab.async false
namespace Option2.NativeStress.NativeT
open NativeH NativeH.Equilibrium NativePolynomial.ConfigurationResiduals

theorem t21_all_points : ∀ (p : Fin 39) (k : Fin 27),
    fastContraction lambda9 ⟨9, false, false⟩ (Q12.lit 1 0 0 0 2) baseQ12
      (variableIndex p k) = 0 := by
  intro p k
  fin_cases p
  · exact t21_block0 0 k
  · exact t21_block0 1 k
  · exact t21_block0 2 k
  · exact t21_block0 3 k
  · exact t21_block0 4 k
  · exact t21_block0 5 k
  · exact t21_block1 0 k
  · exact t21_block1 1 k
  · exact t21_block1 2 k
  · exact t21_block1 3 k
  · exact t21_block1 4 k
  · exact t21_block1 5 k
  · exact t21_block2 0 k
  · exact t21_block2 1 k
  · exact t21_block2 2 k
  · exact t21_block2 3 k
  · exact t21_block2 4 k
  · exact t21_block2 5 k
  · exact t21_block3 0 k
  · exact t21_block3 1 k
  · exact t21_block3 2 k
  · exact t21_block3 3 k
  · exact t21_block3 4 k
  · exact t21_block3 5 k
  · exact t21_block4 0 k
  · exact t21_block4 1 k
  · exact t21_block4 2 k
  · exact t21_block4 3 k
  · exact t21_block4 4 k
  · exact t21_block4 5 k
  · exact t21_block5 0 k
  · exact t21_block5 1 k
  · exact t21_block5 2 k
  · exact t21_block5 3 k
  · exact t21_block5 4 k
  · exact t21_block5 5 k
  · exact t21_block6 0 k
  · exact t21_block6 1 k
  · exact t21_block6 2 k

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.t21_all_points

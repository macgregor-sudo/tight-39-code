module

public import NativeHEquilibriumTransport
public import NativeHAnchorSupport

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open scoped BigOperators
open NativePolynomial.ConfigurationResiduals PolynomialJets AnchorSupport
open QuadraticCertificate.ExactCKMConfiguration

/-- Common points0..2, followed by the panel's actual nine labelled points. -/
def anchorPoint (i : Fin 4) (p : Fin 12) : Fin 39 :=
  ⟨if p.val < 3 then p.val else 9 * i.val + p.val, by split_ifs <;> omega⟩

theorem anchorPoint_coordinate (i : Fin 4) (p : Fin 12) (k : Fin 27) :
    AnchorCoordinate i (variableIndex (anchorPoint i p) k) := by
  simp only [AnchorCoordinate, variableIndex_val, anchorPoint]
  split_ifs <;> omega

/-- Every original anchor coordinate occurs, with its original coordinate label. -/
theorem anchorPoint_covers (i : Fin 4) (v : Fin 1053) (hv : AnchorCoordinate i v) :
    ∃ (p : Fin 12) (k : Fin 27), variableIndex (anchorPoint i p) k = v := by
  let k : Fin 27 := ⟨v.val % 27, Nat.mod_lt _ (by decide)⟩
  by_cases hc : v.val < 81
  · let p : Fin 12 := ⟨v.val / 27, by omega⟩
    refine ⟨p,k,?_⟩
    apply Fin.ext
    simp only [variableIndex_val, anchorPoint, p, k]
    split_ifs <;> omega
  · have hi := hv
    simp only [AnchorCoordinate] at hi
    let p : Fin 12 := ⟨v.val / 27 - 9 * i.val, by omega⟩
    refine ⟨p,k,?_⟩
    apply Fin.ext
    simp only [variableIndex_val, anchorPoint, p, k]
    split_ifs <;> omega

/-- One complete finite panel-component cancellation plus accepted off-anchor
support gives all1053 columns of that component at the exact fixed point. -/
theorem all_columns_of_fast_anchor (i : Fin 4) (a : Fin 3)
    (hzero : ∀ (p : Fin 12) (k : Fin 27),
      fastContraction (rawEntries i a) (hSpec i a) (Q12.lit 1 0 0 0 2) baseQ12
        (variableIndex (anchorPoint i p) k) = 0) :
    ∀ c : Fin 1053, ∑ r : Fin 2184, weightC i a r *
      equationLinearMatrix (translatedRow (fun v => ((pointCoordinates v : ℝ) : ℂ))) r c = 0 := by
  apply AnchorRowSupport.all_columns_of_anchor_columns _ _ i (weightsUseAnchor i a)
  intro c hc
  obtain ⟨p,k,rfl⟩ := anchorPoint_covers i c hc
  rw [← fastContraction_to_original_column, hzero, map_zero]

end Option2.NativeStress.NativeH.Equilibrium

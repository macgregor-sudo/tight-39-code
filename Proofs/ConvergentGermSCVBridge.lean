/-
First-party isolated compatibility prototype, 2026-10-23.
No outgoing project license is selected here. Imports the accepted unchanged
ConvergentResidualJetMap and the retained Apache-2.0 SCV analytic-germ core.
The map is the identity on actual neighborhood germs and preserves constants.
No Noetherian or Weierstrass premise is introduced by this bridge.
-/
module

public import ConvergentResidualJetMap
public import SeveralComplexVariables.AnalyticGerm

@[expose] public section

noncomputable section

namespace ConvergentGermSCVBridge

open ConvergentResidualJets
open scoped Topology

/-- The accepted carrier and the retained SCV carrier have the same actual germs. -/
def germEquiv (n : ℕ) :
    GermRing n ≃ₐ[ℂ] SeveralComplexVariables.AnalyticGerm ℂ (0 : Fin n → ℂ) where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The bridge preserves the underlying neighborhood germ, not just an abstract ring. -/
theorem germEquiv_val (n : ℕ) (u : GermRing n) :
    (germEquiv n u).val = u.val := rfl

/-- Analytic representatives are carried to those same representatives. -/
theorem germEquiv_ofAnalyticAt {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    germEquiv n (ofAnalyticAt f hf) =
      SeveralComplexVariables.AnalyticGerm.ofAnalyticAt f hf := rfl

/-- The actual scalar evaluation maps agree across the bridge. -/
theorem eval_germEquiv (n : ℕ) (u : GermRing n) :
    SeveralComplexVariables.AnalyticGerm.eval (0 : Fin n → ℂ) (germEquiv n u) =
      evalAtZero n u := rfl

end ConvergentGermSCVBridge

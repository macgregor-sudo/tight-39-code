module
public import PairingDefinitions
public import A5Defs
public import GPCode
@[expose] public section

noncomputable section
/- Inline Mathlib-only finite matrix definitions; no restricted variations. -/
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace Option2StatementA3Matrix
end Option2StatementA3Matrix

/- Exact finite A5 anchor data extracted from selected A3/A5 sources.
No phase assumptions are discarded: these formulas are defined at every phase;
unit/good hypotheses remain in the native endpoint statements. -/
namespace Option2StatementA5Anchor
open Glennie NativePolynomial CompactAlbert
open UnitaryErrorBases.ComplexQuartet
open scoped Matrix
namespace Anchor0
end Anchor0

namespace Anchor1
end Anchor1

namespace Anchor2
end Anchor2

namespace Anchor3
end Anchor3

end Option2StatementA5Anchor

/- Exact quartet and anchored point constructors; requires A5AnchorDefinitions
 and the checked A3MatrixDefinitions. The Hermitian construction proofs are
 included rather than assumed. -/
namespace Option2StatementA5Anchor
open Glennie NativePolynomial CompactAlbert
open UnitaryErrorBases.ComplexQuartet
open scoped Matrix
namespace Anchor1
end Anchor1

namespace Anchor2
end Anchor2

namespace Anchor3
end Anchor3

end Option2StatementA5Anchor


namespace Option2StatementA5Anchor

theorem anchorPsi_eq_native (H : Fin 4) :
    anchorΨ H = CKM.NativeFourFamily.anchorΨ H := by rfl

theorem anchorPsiInv_eq_native (H : Fin 4) :
    anchorΨinv H = CKM.NativeFourFamily.anchorΨinv H := by rfl

theorem anchorRelabel_eq_native (H : Fin 4) :
    anchorRelabel H = CKM.NativeFourFamily.anchorRelabel H := by rfl

theorem preCfg_eq_native (ξ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) :
    preCfg ξ H g h d = CKM.NativeFourFamily.preCfg ξ H g h d := by rfl

#print axioms preCfg_eq_native
end Option2StatementA5Anchor

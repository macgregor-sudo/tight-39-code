module

public import RealMatrixKernelComplexification
public import BookRealCoordinates
public import NativePhaseRank
public import NativePhaseRawBook

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseBookComplexificationA6
open PhaseRankA6 PhaseRawBookA6 PhasePivotA6 BookHT HTPhaseComplete
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open NativePolynomial Matrix
open BookHT.NativeNormalKernelBridge (unpackNative)

/-- Only the common factor uses a noncanonical real basis. The Book24 factor
always uses the explicit actual-entry real/imaginary convention. -/
def commonRealEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Common ξ ≃ₗ[ℝ] (Fin 56 → ℝ) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_common hξ,Module.finrank_pi,Fintype.card_fin])

def realModelCoordinates {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (CoordinateIndex → ℝ) ≃ₗ[ℝ] Model ξ :=
  (splitCoordinates ℝ).trans ((commonRealEquiv hξ).symm.prodCongr bookRealEquiv.symm)

def nativeRealCoordinates {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (CoordinateIndex → ℝ) ≃ₗ[ℝ] LinearMap.ker (realJ ξ).mulVecLin :=
  (realModelCoordinates hξ).trans
    ((rawBookEquiv hξ).toLinearEquiv.trans (tangentKernelEquiv ξ))

def kernelEquivOfMatrixEq {m n : Type*} [Fintype n] {M N : Matrix m n ℂ} (h : M = N) :
    LinearMap.ker M.mulVecLin ≃ₗ[ℂ] LinearMap.ker N.mulVecLin := by
  subst N
  exact LinearEquiv.refl _ _

theorem kernelEquivOfMatrixEq_val {m n : Type*} [Fintype n] {M N : Matrix m n ℂ}
    (h : M = N) (v : LinearMap.ker M.mulVecLin) : (kernelEquivOfMatrixEq h v).val = v.val := by
  subst N
  rfl

/-- This cast is exactly the proved original-row real-to-complex matrix identity. -/
def nativeKernelCast (ξ : Fin 4 → ℂ) :
    LinearMap.ker (complexMatrix (realJ ξ)).mulVecLin ≃ₗ[ℂ] LinearMap.ker (nativeJ ξ).mulVecLin :=
  kernelEquivOfMatrixEq (realJ_map_complex ξ)

theorem nativeKernelCast_val (ξ : Fin 4 → ℂ)
    (v : LinearMap.ker (complexMatrix (realJ ξ)).mulVecLin) :
    (nativeKernelCast ξ v).val = v.val := kernelEquivOfMatrixEq_val _ _

/-- The actual1053×80 REAL raw tangent matrix. Common56/Book24 columns are
kept separate by CoordinateIndex; Book columns are actual re/im directions. -/
def nativeRealMatrix {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : Matrix (Fin 1053) CoordinateIndex ℝ :=
  LinearMap.toMatrix' (kernelAmbient (realJ ξ) (nativeRealCoordinates hξ))

def nativeComplexMatrix {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : Matrix (Fin 1053) CoordinateIndex ℂ :=
  complexMatrix (nativeRealMatrix hξ)

/-- The actual complex native kernel, in common56 plus REAL-Book24 coordinates.
Complex linearity belongs to the extended real matrix, never to Vxi or Blocks. -/
def nativeBookComplexEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (CoordinateIndex → ℂ) ≃ₗ[ℂ] LinearMap.ker (nativeJ ξ).mulVecLin :=
  (complexKernelEquiv (realJ ξ) (nativeRealCoordinates hξ)).trans (nativeKernelCast ξ)

theorem nativeBookComplexEquiv_matrix {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (x : CoordinateIndex → ℂ) :
    (nativeBookComplexEquiv hξ x).val = nativeComplexMatrix hξ *ᵥ x := by
  rw [nativeBookComplexEquiv,LinearEquiv.trans_apply,nativeKernelCast_val]
  rfl

theorem nativeBookComplexEquiv_inverse {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (v : LinearMap.ker (nativeJ ξ).mulVecLin) :
    (nativeBookComplexEquiv hξ).symm v =
      inverseCoordinates (realJ ξ) (nativeRealCoordinates hξ) ((nativeKernelCast ξ).symm v) := by
  rw [nativeBookComplexEquiv,LinearEquiv.symm_trans_apply,complexKernelEquiv_symm]

theorem complexKernelEquiv_ofReal {m n κ : Type*} [Fintype n] [Fintype κ] [DecidableEq κ]
    (M : Matrix m n ℝ) (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) (x : κ → ℝ) :
    (complexKernelEquiv M e (fun k => (x k : ℂ))).val = fun j => ((e x).val j : ℂ) := by
  change (complexKernelMap M e (fun k => (x k : ℂ))).val = _
  have hre := complexKernelMap_re M e (fun k => (x k : ℂ))
  have him := complexKernelMap_im M e (fun k => (x k : ℂ))
  have hr : (fun k => (x k : ℂ).re) = x := rfl
  have hi : (fun k => (x k : ℂ).im) = 0 := rfl
  rw [hr] at hre
  rw [hi,map_zero] at him
  ext j
  apply Complex.ext
  · exact congrFun hre j
  · exact congrFun him j

 theorem nativeRealCoordinates_model {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (v : Model ξ) :
    (nativeRealCoordinates hξ ((realModelCoordinates hξ).symm v)).val =
      PartialAction.pack (rawBookEquiv hξ v).val := by
  simp only [nativeRealCoordinates,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rfl

/-- On actual real Book coordinates this is precisely the incoming raw native
map o+c+unpackNative(Vxi z), with no projection or conjugation change. -/
theorem nativeBookComplexEquiv_real_model {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (o : orbitC ξ) (c : fixQK ξ) (z : Blocks) :
    (nativeBookComplexEquiv hξ (fun k =>
      (((realModelCoordinates hξ).symm ((o,c),z) k : ℝ) : ℂ))).val =
    fun j => ((PartialAction.pack ((o : Cfg)+(c : Cfg)+unpackNative (Vxi ξ hξ.1 z)) j : ℝ) : ℂ) := by
  rw [nativeBookComplexEquiv,LinearEquiv.trans_apply,nativeKernelCast_val,
    complexKernelEquiv_ofReal,nativeRealCoordinates_model,rawBookEquiv_coe]

#print axioms Option2.NativeStress.PhaseBookComplexificationA6.nativeBookComplexEquiv
#print axioms Option2.NativeStress.PhaseBookComplexificationA6.nativeBookComplexEquiv_real_model
end Option2.NativeStress.PhaseBookComplexificationA6

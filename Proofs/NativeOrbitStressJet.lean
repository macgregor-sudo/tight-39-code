module

public import StressOrbitHessian
public import GSResidual
public import OriginalResidualSmoothnessV2

@[expose] public section

noncomputable section
namespace CKM.NativeGroupSlice.OrbitStressJet

open Option2.NativeStress.AnalyticDerivative
open CKM.NativeFirstOrder

-- Explicit derivative types avoid inference expansion; the completed native
-- covariance term still exceeds the default200000 elaboration heartbeats.
-- The external60-second/M3584 check remains unchanged.
set_option maxHeartbeats 1000000

/-- The genuine off-shell covariance differentiated along the accepted group
chart. The derivative of rowAction is used, never a false linearity in A. -/
theorem infinitesimal_covariance (D : derC) (x : Cfg) :
    (fderiv ℝ originalF x) (actC (D : CEnd) x) =
      ((fderiv ℝ (fun A : derC => rowAction (groupChart A)) 0) D) (originalF x) := by
  have hlin : HasStrictFDerivAt (actC.flip x) (actC.flip x) (groupChart (0 : derC)) :=
    (actC.flip x).hasStrictFDerivAt
  have hactStrict := hlin.comp (0 : derC) hasStrictFDerivAt_groupChart
  have hact : HasFDerivAt (fun A : derC => actC (groupChart A) x)
      ((actC.flip x).comp derC.subtypeL) 0 := hactStrict.hasFDerivAt
  have hbase : actC (groupChart 0) x = x := by
    rw [groupChart_zero, actC_one]
    rfl
  have hdf : HasFDerivAt originalF (fderiv ℝ originalF x) x :=
    ((originalF_contDiff 2).contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  have hdfbase : HasFDerivAt originalF (fderiv ℝ originalF x)
      (actC (groupChart 0) x) := by
    rw [hbase]
    exact hdf
  have hleft : HasFDerivAt (fun A : derC => originalF (actC (groupChart A) x))
      ((fderiv ℝ originalF x).comp ((actC.flip x).comp derC.subtypeL)) (0 : derC) :=
    HasFDerivAt.comp (f := fun A : derC => actC (groupChart A) x)
      (0 : derC) hdfbase hact
  have hrho : DifferentiableAt ℝ (fun A : derC => rowAction (groupChart A)) 0 :=
    ((analyticAt_rowAction (groupChart 0)).comp (analyticAt_groupChart 0)).differentiableAt
  let ev : ((Fin 2184 → ℝ) →L[ℝ] (Fin 2184 → ℝ)) →L[ℝ] (Fin 2184 → ℝ) :=
    ContinuousLinearMap.apply ℝ (Fin 2184 → ℝ) (originalF x)
  have hev : HasFDerivAt ev ev (rowAction (groupChart (0 : derC))) := ev.hasFDerivAt
  have hright : HasFDerivAt (fun A : derC => rowAction (groupChart A) (originalF x))
      (ev.comp (fderiv ℝ (fun A : derC => rowAction (groupChart A)) (0 : derC)))
      (0 : derC) :=
    HasFDerivAt.comp (f := fun A : derC => rowAction (groupChart A))
      (0 : derC) hev hrho.hasFDerivAt
  have heq : (fun A : derC => originalF (actC (groupChart A) x)) =
      fun A : derC => rowAction (groupChart A) (originalF x) :=
    funext fun A => originalF_actC (groupChart_mem_autC A) x
  rw [heq] at hleft
  have h := congrArg (fun L : derC →L[ℝ] (Fin 2184 → ℝ) => L D)
    (hleft.unique hright)
  simpa only [ev, groupChart_zero, actC_one, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply, Submodule.subtypeL_apply] using h

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Actual native orbit tangents may be removed from a derivative-kernel
direction under any continuous stationary real-linear residual covector. -/
theorem originalF_sub_orbit_hessian (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (v o : Cfg) (hv : (fderiv ℝ originalF (literalCfg ξ)) v = 0)
    (ho : o ∈ orbitC ξ) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ originalF (literalCfg ξ)) = 0) :
    ell ((fderiv ℝ (fderiv ℝ originalF) (literalCfg ξ)) (v-o) (v-o)) =
      ell ((fderiv ℝ (fderiv ℝ originalF) (literalCfg ξ)) v v) := by
  rcases ho with ⟨A, hA, rfl⟩
  let D : derC := ⟨A, hA⟩
  exact SupportedStress.OrbitHessian.sub_orbit_invariant originalF (actC A)
    ((fderiv ℝ (fun A : derC => rowAction (groupChart A)) 0) D)
    (originalF_contDiff 2) (fun x => infinitesimal_covariance D x)
    (literalCfg ξ) v ell (originalF_literalCfg ξ hξ) hv hann

end CKM.NativeGroupSlice.OrbitStressJet

#print axioms CKM.NativeGroupSlice.OrbitStressJet.infinitesimal_covariance
#print axioms CKM.NativeGroupSlice.OrbitStressJet.originalF_sub_orbit_hessian

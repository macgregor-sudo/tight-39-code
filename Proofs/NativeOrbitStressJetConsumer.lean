module

public import NativeOrbitStressJet
public import BookNativeNormalKernelBridge

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHT.NativeOrbitStressJet

open TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice
open QuadraticCertificate.ExactCKMConfiguration

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The requested exact native seed, with arbitrary stationary stress. -/
theorem exact_seed_sub_orbit_hessian
    (v o : Cfg)
    (hv : (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) v = 0)
    (ho : o ∈ orbitC exactPhases) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0) :
    ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
      (v-o) (v-o)) =
      ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases)) v v) :=
  CKM.NativeGroupSlice.OrbitStressJet.originalF_sub_orbit_hessian
    exactPhases exactPhases_unit v o hv ho ell hann

/-- Actual normalProjection removes an actual orbit tangent, so it preserves
the stressed Hessian on the full derivative kernel. -/
theorem normalProjection_hessian
    (v : Cfg) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hv : (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) v = 0)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0) :
    ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
      (normalProjection v : Cfg) (normalProjection v : Cfg)) =
      ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases)) v v) := by
  have h := exact_seed_sub_orbit_hessian v (v - (normalProjection v : Cfg)) hv
    (sub_normalProjection_mem_orbit v) ell hann
  simpa only [sub_sub_cancel] using h

/-- The genuine raw unpacked realV direction has its kernel membership proved
by the frozen Book tangent binding; no H/T reproduction is imported. -/
theorem bookDirection_normalProjection_hessian
    (z : Blocks) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0) :
    ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
      (normalProjection (bookDirection z) : Cfg) (normalProjection (bookDirection z) : Cfg)) =
      ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
        (bookDirection z) (bookDirection z)) :=
  normalProjection_hessian (bookDirection z) ell (bookDirection_mem_tangent z) hann

/-- An importing use with the raw realV map displayed explicitly. -/
example (z : Blocks) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0) :
    ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
      (normalProjection (unpackNative (realV z)) : Cfg)
      (normalProjection (unpackNative (realV z)) : Cfg)) =
      ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
        (unpackNative (realV z)) (unpackNative (realV z))) :=
  bookDirection_normalProjection_hessian z ell hann

theorem normalProjection_half_quadratic
    (v : Cfg) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hv : (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) v = 0)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0) :
    ell ((1/2 : ℝ) •
      (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases))
        (normalProjection v : Cfg) (normalProjection v : Cfg)) =
      (1/2 : ℝ) • ell
        ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases)) v v) := by
  rw [map_smul, normalProjection_hessian v ell hv hann]

end Option2.NativeStress.BookHT.NativeOrbitStressJet

#print Option2.NativeStress.BookHT.NativeOrbitStressJet.exact_seed_sub_orbit_hessian
#print Option2.NativeStress.BookHT.NativeOrbitStressJet.normalProjection_hessian
#print Option2.NativeStress.BookHT.NativeOrbitStressJet.bookDirection_normalProjection_hessian
#print axioms Option2.NativeStress.BookHT.NativeOrbitStressJet.exact_seed_sub_orbit_hessian
#print axioms Option2.NativeStress.BookHT.NativeOrbitStressJet.normalProjection_hessian
#print axioms Option2.NativeStress.BookHT.NativeOrbitStressJet.bookDirection_normalProjection_hessian
#print axioms Option2.NativeStress.BookHT.NativeOrbitStressJet.normalProjection_half_quadratic

module

public import NativePhasePivot
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhasePivotLocusA6
open PhasePivotA6 HTPhaseKron
open PolynomialJets NativePolynomial.ConfigurationResiduals
open QuarticCertificate.PipelineNaturality

/-- Laurent monomials commute with an actual ring map via the induced unit map. -/
theorem map_mono {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (U : Fin 4 → Rˣ) (m : Ex) :
    f (mono U m) = mono (fun i => Units.map f.toMonoidHom (U i)) m := by
  unfold mono
  change (↑((Units.map f.toMonoidHom)
    (U 0 ^ m.1 * U 1 ^ m.2.1 * U 2 ^ m.2.2.1 * U 3 ^ m.2.2.2)) : S) = _
  simp only [map_mul, map_zpow]

/-- Exact naturality of all1053 source-bound Laurent coordinates. -/
theorem map_PhiR {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (v : Fin 1053) :
    f (PhiR ι U v) = PhiR (f.comp ι) (fun i => Units.map f.toMonoidHom (U i)) v := by
  unfold PhiR
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  simp only [Function.comp_apply, ev, map_mul, RingHom.comp_apply, map_mono]

/-- Entrywise ring maps preserve the entire actual finite phase Jacobian. -/
theorem map_J {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ι : Q12 →+* R) (U : Fin 4 → Rˣ) :
    (J ι U).map f = J (f.comp ι) (fun i => Units.map f.toMonoidHom (U i)) := by
  ext r c
  change f (equationLinearMatrix
    (fun r => translate (PhiR ι U) (fRow (ι half) (ι thirdQ12) r)) r c) = _
  rw [map_equationLinearMatrix]
  have hphi : (fun v => f (PhiR ι U v)) =
      PhiR (f.comp ι) (fun i => Units.map f.toMonoidHom (U i)) := funext (map_PhiR f ι U)
  simp only [PolynomialJets.map_translate, FourSheets.PointBridge.Rows.map_fRow, hphi]
  rfl

/-- Determinants of the fixed973 selection commute with that same ring map. -/
theorem map_pivot {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (ι : Q12 →+* R) (U : Fin 4 → Rˣ) :
    f (selectedMinor (J ι U)).det =
      (selectedMinor (J (f.comp ι) (fun i => Units.map f.toMonoidHom (U i)))).det := by
  rw [f.map_det]
  congr 1
  have h := map_J f ι U
  exact congrArg selectedMinor h

end Option2.NativeStress.PhasePivotLocusA6

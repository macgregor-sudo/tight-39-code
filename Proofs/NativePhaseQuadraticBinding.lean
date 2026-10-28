module

public import NativePhasePivotFactor
public import FreeVariables
public import RankBridge

@[expose] public section

/-!
Actual Laurent/native quadratic binding for the phase obstruction relations. No Hilbert bound,
annihilator, kernel basis or Book span witness is postulated as a theorem.
The final finite-certificate theorem exposes its polynomial identity as input.
First-party proofs; generic coefficient-map facts are imported unchanged.
-/

noncomputable section
namespace Option2.NativeStress.PhaseHilbertA6
open MvPolynomial PolynomialJets
open PhasePivotA6 PhasePivotLocusA6 HTPhaseKron
open NativePolynomial NativePolynomial.ConfigurationResiduals QuarticCertificate.PipelineNaturality
open CKM.NativeFirstOrder
open scoped BigOperators

/-- Every original row, translated by the actual formal Laurent configuration. -/
def formalRows (r : Fin 2184) : MvPolynomial (Fin 1053) LaurentPhaseRing :=
  translate (PhiR formalCoefficients formalUnit)
    (fRow (formalCoefficients half) (formalCoefficients thirdQ12) r)

/-- Every unchanged original row at the literal native phase configuration. -/
def nativeRows (ξ : Fin 4 → ℂ) (r : Fin 2184) : MvPolynomial (Fin 1053) ℂ :=
  translate (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ))
    (fRow (1/2 : ℂ) (1/3 : ℂ) r)

theorem phaseEval_formalRows (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (r : Fin 2184) :
    map (phaseEval ξ hξ) (formalRows r) = nativeRows ξ r := by
  have hphi : (fun v => phaseEval ξ hξ (PhiR formalCoefficients formalUnit v)) =
      (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ)) := by
    funext v
    rw [map_PhiR, phaseEval_formalCoefficients]
    have hu : (fun i => Units.map (phaseEval ξ hξ).toMonoidHom (formalUnit i)) =
        Uph ξ hξ := funext (phaseEval_formalUnit ξ hξ)
    rw [hu]
    exact phi_bridge ξ hξ v
  unfold formalRows nativeRows
  rw [PolynomialJets.map_translate, FourSheets.PointBridge.Rows.map_fRow, hphi]
  have hc := phaseEval_formalCoefficients ξ hξ
  have hh := RingHom.congr_fun hc half
  have ht := RingHom.congr_fun hc thirdQ12
  simpa only [RingHom.comp_apply, toComplex_half, toComplex_third] using
    congrArg₂ (fun a b => translate
      (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ)) (fRow a b r)) hh ht

theorem nativeRows_linearMatrix (ξ : Fin 4 → ℂ) :
    Matrix.of (equationLinearMatrix (nativeRows ξ)) = nativeJ ξ := rfl

/-- Restriction is written over the Laurent ring without pretending it is a field. -/
def formalRestrictedQuadric (B : Matrix (Fin 1053) (Fin 80) LaurentPhaseRing)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing) (s : Fin 48) :
    MvPolynomial (Fin 80) LaurentPhaseRing :=
  aeval (fun j => ∑ t, C (B j t) * X t) (equationAnnihilatorQuadric formalRows (w s))

theorem phaseEval_formalRestrictedQuadric (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (B : Matrix (Fin 1053) (Fin 80) LaurentPhaseRing)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing) (s : Fin 48) :
    map (phaseEval ξ hξ) (formalRestrictedQuadric B w s) =
      ChainMid.restrictedQuadric (B.map (phaseEval ξ hξ)) (nativeRows ξ)
        (fun k r => phaseEval ξ hξ (w k r)) s := by
  unfold formalRestrictedQuadric
  rw [map_restrictAlongMatrix (phaseEval ξ hξ) (fun j t => B j t),
    map_equationAnnihilatorQuadric]
  simp only [phaseEval_formalRows]
  rfl

def formalChangedQuadric (B : Matrix (Fin 1053) (Fin 80) LaurentPhaseRing)
    (M : Matrix (Fin 80) (Fin 56 ⊕ Fin 24) LaurentPhaseRing)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing) (s : Fin 48) :
    MvPolynomial (Fin 56 ⊕ Fin 24) LaurentPhaseRing :=
  aeval (fun j => ∑ t, C (M j t) * X t) (formalRestrictedQuadric B w s)

theorem phaseEval_formalChangedQuadric (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (B : Matrix (Fin 1053) (Fin 80) LaurentPhaseRing)
    (M : Matrix (Fin 80) (Fin 56 ⊕ Fin 24) LaurentPhaseRing)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing) (s : Fin 48) :
    map (phaseEval ξ hξ) (formalChangedQuadric B M w s) =
      ChainMid.linSubst (M.map (phaseEval ξ hξ))
        (ChainMid.restrictedQuadric (B.map (phaseEval ξ hξ)) (nativeRows ξ)
          (fun k r => phaseEval ξ hξ (w k r)) s) := by
  unfold formalChangedQuadric
  rw [map_restrictAlongMatrix (phaseEval ξ hξ) (fun j t => M j t),
    phaseEval_formalRestrictedQuadric]
  rfl

/-- All-column annihilation specializes; its formal identity is still an input. -/
theorem native_annihilation_of_formal (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing)
    (hw : ∀ s j, ∑ r, w s r * J formalCoefficients formalUnit r j = 0) :
    ∀ s j, ∑ r, phaseEval ξ hξ (w s r) * nativeJ ξ r j = 0 := by
  have hJ := map_J (phaseEval ξ hξ) formalCoefficients formalUnit
  rw [phaseEval_formalCoefficients] at hJ
  have hu : (fun i => Units.map (phaseEval ξ hξ).toMonoidHom (formalUnit i)) =
      Uph ξ hξ := funext (phaseEval_formalUnit ξ hξ)
  rw [hu, J_native] at hJ
  intro s j
  have h := congrArg (phaseEval ξ hξ) (hw s j)
  simp only [map_sum, map_mul, map_zero] at h
  simpa only [← hJ, Matrix.map_apply] using h

/-- A finite Laurent identity specializes into the exact native D6 span.
No injectivity of phase evaluation is used. This DOES NOT provide the identity,
the annihilator/kernel properties, a coordinate inverse, or a Hilbert bound. -/
theorem native_span_of_finite_formal_identity (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (B : Matrix (Fin 1053) (Fin 80) LaurentPhaseRing)
    (M : Matrix (Fin 80) (Fin 56 ⊕ Fin 24) LaurentPhaseRing)
    (w : Fin 48 → Fin 2184 → LaurentPhaseRing)
    (t : Fin 48 → MvPolynomial (Fin 24) ℂ)
    (a : Fin 48 → Fin 48 → LaurentPhaseRing)
    (hidentity : ∀ k, rename (Sum.inr : Fin 24 → Fin 56 ⊕ Fin 24)
        (map complexConstants (t k)) = ∑ s, a k s • formalChangedQuadric B M w s) :
    ∀ k, rename (Sum.inr : Fin 24 → Fin 56 ⊕ Fin 24) (t k) ∈
      Submodule.span ℂ (Set.range fun s =>
        ChainMid.linSubst (M.map (phaseEval ξ hξ))
          (ChainMid.restrictedQuadric (B.map (phaseEval ξ hξ)) (nativeRows ξ)
            (fun k r => phaseEval ξ hξ (w k r)) s)) := by
  have hc : (phaseEval ξ hξ).comp complexConstants = RingHom.id ℂ := by
    ext z
    exact phaseEval_complexConstants ξ hξ z
  intro k
  have h := congrArg (map (phaseEval ξ hξ)) (hidentity k)
  simp only [map_rename, map_map, hc, map_id, map_sum,
    map_smul_polynomial, phaseEval_formalChangedQuadric] at h
  rw [h]
  exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨s, rfl⟩)

end Option2.NativeStress.PhaseHilbertA6

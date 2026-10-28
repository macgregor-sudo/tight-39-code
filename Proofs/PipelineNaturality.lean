module

public import PIntegralRing
public import PolynomialJetPrerequisitesModule
public import PointBridge
public import PointQ12Bridge

/-!
# Naturality of the consumer's polynomial pipeline under coefficient ring homomorphisms

Purpose. The consumer builds its objects from the F rows by MvPolynomial operations:
`fRow → translate P → homogeneousComponent → Σ wᵢ • (·) → aeval along a matrix B → coeff`.
Every one of these commutes with `MvPolynomial.map φ` for a ring homomorphism `φ`. This module
records the commutation lemmas generically (any `CommRing`s `R → S`), and instantiates them at
the F rows over the `p`-integral ring `A_p = Q12.PIntegral1048573`:

* the image in `ℂ` (along the injective `Q12.pIntegralToComplex`) of the `A_p` rows is exactly
  the consumer's row family `fun r => translate PointBridge.P (fRow (1/2) (1/3) r)`;
* the image in `ZMod 1048573` (along `Q12.reduceMod1048573`) is the same construction with the
  reduced point and the constants `2⁻¹`, `3⁻¹`;
* consequently the consumer's Jacobian entries and annihilator quadrics are the `ℂ`-images of
  the corresponding `A_p` objects, whose `ZMod p` images the kernel computes.

What is verified: all statements, by the Lean kernel, standard axioms. The point membership
`P ∈ A_p^1053` is one kernel evaluation over the 1053 literal coordinates.
What is assumed: the consumer module `PolynomialJetPrerequisitesModule` (its `translate`,
`map_translate`, `equationLinearMatrix`, `equationAnnihilatorQuadric`, `homogeneousLinearMul`),
the four-sheets modules `PointBridge` (`Rows.map_fRow`, `P`) and `PointQ12Bridge`
(`pointQ12`, `P_literal`), with their original coordinate conventions.

No equality over `ℂ` is inferred from a modular computation: the `ZMod p` statements are images
of exact `A_p` objects, used only to transfer nonvanishing.

First-party proofs (no borrowed code).
-/

@[expose] public section
noncomputable section

namespace QuarticCertificate.PipelineNaturality

open MvPolynomial PolynomialJets

/-! ## Generic naturality lemmas -/

section Generic

variable {σ τ ι R S : Type*} [CommRing R] [CommRing S]

/-- Homogeneous components commute with coefficient maps. -/
theorem map_homogeneousComponent (φ : R →+* S) (n : ℕ) (f : MvPolynomial σ R) :
    map φ (homogeneousComponent n f) = homogeneousComponent n (map φ f) := by
  ext d
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs
  · rfl
  · exact map_zero φ

/-- Scalar multiplication commutes with coefficient maps. -/
theorem map_smul_polynomial (φ : R →+* S) (a : R) (f : MvPolynomial σ R) :
    map φ (a • f) = φ a • map φ f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

/-- Translation commutes with coefficient maps (the consumer's own lemma, restated). -/
theorem map_translate' (φ : R →+* S) (P : σ → R) (f : MvPolynomial σ R) :
    map φ (translate P f) = translate (fun j => φ (P j)) (map φ f) :=
  PolynomialJets.map_translate φ P f

/-- The consumer's linear coefficient matrix is natural: entries map entrywise. -/
theorem map_equationLinearMatrix (φ : R →+* S) (g : ι → MvPolynomial σ R) (i : ι) (j : σ) :
    φ (equationLinearMatrix g i j) = equationLinearMatrix (fun i => map φ (g i)) i j :=
  (coeff_map φ (g i) (Finsupp.single j 1)).symm

/-- The consumer's annihilator quadric `Σᵢ wᵢ • homogeneousComponent 2 (gᵢ)` is natural. -/
theorem map_equationAnnihilatorQuadric [Fintype ι] (φ : R →+* S) (g : ι → MvPolynomial σ R)
    (weights : ι → R) :
    map φ (equationAnnihilatorQuadric g weights) =
      equationAnnihilatorQuadric (fun i => map φ (g i)) (fun i => φ (weights i)) := by
  unfold equationAnnihilatorQuadric
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_polynomial, map_homogeneousComponent]

/-- Substitution `X_j ↦ g_j` commutes with coefficient maps. -/
theorem map_aeval_substitution (φ : R →+* S) (g : σ → MvPolynomial τ R)
    (f : MvPolynomial σ R) :
    map φ (aeval g f) = aeval (fun j => map φ (g j)) (map φ f) := by
  rw [aeval_def, aeval_def, algebraMap_eq, algebraMap_eq, map_eval₂]
  rfl

/-- **Restriction along a matrix.** Substituting `X_j ↦ Σ_t B_{jt} Y_t` commutes with
coefficient maps, the matrix being mapped entrywise. -/
theorem map_restrictAlongMatrix [Fintype τ] (φ : R →+* S) (B : σ → τ → R)
    (f : MvPolynomial σ R) :
    map φ (aeval (fun j => ∑ t, C (B j t) * X t) f) =
      aeval (fun j => ∑ t, C (φ (B j t)) * X t) (map φ f) := by
  rw [map_aeval_substitution]
  have hsub : (fun j => map φ (∑ t, C (B j t) * X t)) =
      fun j => ∑ t, C (φ (B j t)) * (X t : MvPolynomial τ S) := by
    funext j
    simp only [map_sum, map_mul, map_C, map_X]
  rw [hsub]

/-- Homogeneity is preserved by coefficient maps. -/
theorem isHomogeneous_map (φ : R →+* S) {f : MvPolynomial σ R} {n : ℕ}
    (hf : f.IsHomogeneous n) : (map φ f).IsHomogeneous n := by
  intro d hd
  apply hf
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

/-- The coefficient map on homogeneous elements of degree `n`. -/
def mapHomogeneous (φ : R →+* S) (n : ℕ) :
    homogeneousSubmodule σ R n → homogeneousSubmodule σ S n :=
  fun a => ⟨map φ a.val, (mem_homogeneousSubmodule n _).2
    (isHomogeneous_map φ ((mem_homogeneousSubmodule n _).1 a.property))⟩

theorem mapHomogeneous_val (φ : R →+* S) (n : ℕ) (a : homogeneousSubmodule σ R n) :
    (mapHomogeneous φ n a).val = map φ a.val := rfl

/-- The consumer's `homogeneousLinearMul` (used by premise 3, `a i = z · b i`) is natural. -/
theorem mapHomogeneous_homogeneousLinearMul (φ : R →+* S) (z : homogeneousSubmodule σ R 1)
    (n : ℕ) (b : homogeneousSubmodule σ R n) :
    mapHomogeneous φ (n + 1) (homogeneousLinearMul z n b) =
      homogeneousLinearMul (mapHomogeneous φ 1 z) n (mapHomogeneous φ n b) := by
  apply Subtype.ext
  rw [mapHomogeneous_val, homogeneousLinearMul_val, homogeneousLinearMul_val, map_mul]
  rfl

end Generic

/-! ## The F rows over `A_p` -/

section FRows

open Q12 NativePolynomial.ConfigurationResiduals

/-- Every literal coordinate of the exact point lies in `A_p` (one kernel evaluation over the
`39 × 27` literal table). -/
theorem pointQ12_mem_pIntegral :
    ∀ i : Fin 39, ∀ k : Fin 27, FourSheets.PointQ12.pointQ12 i k ∈ PIntegral1048573 := by
  decide +kernel

/-- The exact point as a vector over `A_p`, in the consumer's 1053 variables. -/
def pointPIntegral : Fin 1053 → PIntegral1048573 := fun v =>
  ⟨FourSheets.PointQ12.pointQ12 (Fin.divNat (m := 39) (n := 27) v)
    (Fin.modNat (m := 39) (n := 27) v), pointQ12_mem_pIntegral _ _⟩

/-- The complex image of the `A_p` point is the consumer's point `PointBridge.P`. -/
theorem pIntegralToComplex_pointPIntegral :
    (fun v => pIntegralToComplex 1048573 (pointPIntegral v)) = FourSheets.PointBridge.P := by
  unfold FourSheets.PointBridge.P
  rw [FourSheets.PointQ12.P_literal]
  rfl

/-- The reduced point in `ZMod 1048573`. -/
def pointModP : Fin 1053 → ZMod 1048573 := fun v => reduceMod1048573 (pointPIntegral v)

/-- The translated F rows over `A_p`: `translate P (fRow (1/2) (1/3) r)`. -/
def translatedRowPIntegral (r : Fin 2184) : MvPolynomial (Fin 1053) PIntegral1048573 :=
  translate pointPIntegral (fRow halfPIntegral thirdPIntegral r)

/-- The consumer's row family over `ℂ`. -/
def translatedRowComplex (r : Fin 2184) : MvPolynomial (Fin 1053) ℂ :=
  translate FourSheets.PointBridge.P (fRow (1/2 : ℂ) (1/3 : ℂ) r)

/-- The same construction over `ZMod 1048573`, with constants `2⁻¹`, `3⁻¹`. -/
def translatedRowModP (r : Fin 2184) : MvPolynomial (Fin 1053) (ZMod 1048573) :=
  translate pointModP (fRow (2⁻¹ : ZMod 1048573) (3⁻¹ : ZMod 1048573) r)

/-- **`ℂ`-image.** The `A_p` rows map to the consumer's rows. -/
theorem map_translatedRowPIntegral_complex (r : Fin 2184) :
    map (pIntegralToComplex 1048573) (translatedRowPIntegral r) = translatedRowComplex r := by
  unfold translatedRowPIntegral translatedRowComplex
  rw [PolynomialJets.map_translate, FourSheets.PointBridge.Rows.map_fRow,
    pIntegralToComplex_half, pIntegralToComplex_third, pIntegralToComplex_pointPIntegral]

/-- **`ZMod p`-image.** The `A_p` rows map to the reduced rows. -/
theorem map_translatedRowPIntegral_modP (r : Fin 2184) :
    map reduceMod1048573 (translatedRowPIntegral r) = translatedRowModP r := by
  unfold translatedRowPIntegral translatedRowModP
  rw [PolynomialJets.map_translate, FourSheets.PointBridge.Rows.map_fRow,
    reduceMod1048573_half, reduceMod1048573_third]
  rfl

/-- The consumer's Jacobian entries are the complex images of the `A_p` Jacobian entries. -/
theorem equationLinearMatrix_complex_eq (r : Fin 2184) (j : Fin 1053) :
    equationLinearMatrix translatedRowComplex r j =
      pIntegralToComplex 1048573 (equationLinearMatrix translatedRowPIntegral r j) := by
  rw [map_equationLinearMatrix]
  simp only [map_translatedRowPIntegral_complex]

/-- The reduced Jacobian entries are the `ZMod p` images of the `A_p` Jacobian entries. -/
theorem equationLinearMatrix_modP_eq (r : Fin 2184) (j : Fin 1053) :
    equationLinearMatrix translatedRowModP r j =
      reduceMod1048573 (equationLinearMatrix translatedRowPIntegral r j) := by
  rw [map_equationLinearMatrix]
  simp only [map_translatedRowPIntegral_modP]

/-- The consumer's annihilator quadric with complexified `A_p` weights is the complex image of
the `A_p` quadric. -/
theorem equationAnnihilatorQuadric_complex_eq (w : Fin 2184 → PIntegral1048573) :
    equationAnnihilatorQuadric translatedRowComplex (fun r => pIntegralToComplex 1048573 (w r)) =
      map (pIntegralToComplex 1048573) (equationAnnihilatorQuadric translatedRowPIntegral w) := by
  rw [map_equationAnnihilatorQuadric]
  simp only [map_translatedRowPIntegral_complex]

/-- The reduced annihilator quadric is the `ZMod p` image of the `A_p` quadric. -/
theorem equationAnnihilatorQuadric_modP_eq (w : Fin 2184 → PIntegral1048573) :
    equationAnnihilatorQuadric translatedRowModP (fun r => reduceMod1048573 (w r)) =
      map reduceMod1048573 (equationAnnihilatorQuadric translatedRowPIntegral w) := by
  rw [map_equationAnnihilatorQuadric]
  simp only [map_translatedRowPIntegral_modP]

end FRows

end QuarticCertificate.PipelineNaturality

end

#print axioms QuarticCertificate.PipelineNaturality.map_homogeneousComponent
#print axioms QuarticCertificate.PipelineNaturality.map_equationLinearMatrix
#print axioms QuarticCertificate.PipelineNaturality.map_equationAnnihilatorQuadric
#print axioms QuarticCertificate.PipelineNaturality.map_aeval_substitution
#print axioms QuarticCertificate.PipelineNaturality.map_restrictAlongMatrix
#print axioms QuarticCertificate.PipelineNaturality.mapHomogeneous_homogeneousLinearMul
#print axioms QuarticCertificate.PipelineNaturality.pointQ12_mem_pIntegral
#print axioms QuarticCertificate.PipelineNaturality.pIntegralToComplex_pointPIntegral
#print axioms QuarticCertificate.PipelineNaturality.map_translatedRowPIntegral_complex
#print axioms QuarticCertificate.PipelineNaturality.map_translatedRowPIntegral_modP
#print axioms QuarticCertificate.PipelineNaturality.equationLinearMatrix_complex_eq
#print axioms QuarticCertificate.PipelineNaturality.equationLinearMatrix_modP_eq
#print axioms QuarticCertificate.PipelineNaturality.equationAnnihilatorQuadric_complex_eq
#print axioms QuarticCertificate.PipelineNaturality.equationAnnihilatorQuadric_modP_eq

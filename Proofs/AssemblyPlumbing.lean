module

/-
Four-branch algebraic assembly. AI-assisted first-party source (Fable). Pin: Lean v4.35.0-rc2,
Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. No sorry, no custom axioms.

Content: the ring-theoretic glue between the consumer's `I ≤ J` premise and the generic
vanishing theorem.  Nothing here is specific to the sheet maps: given four algebra maps
`ρ i : GermRing 1053 →ₐ[ℂ] GermRing 62` whose values on coordinates are `γ i k - P k`,
the containment `I ≤ J` follows from `aeval (γ i) (fRow r) = 0` for all `i r`.
-/
public import ConvergentResidualJetMap
public import PolynomialJetPrerequisitesModule
public import NativeConfigurationPolynomialResiduals

@[expose] public section

open MvPolynomial ConvergentResidualJets
open NativePolynomial.ConfigurationResiduals

namespace FourSheets.Plumbing

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Evaluating a translated polynomial is evaluating the original at the shifted point. -/
theorem aeval_translate {n : ℕ} (u : Fin n → A) (P : Fin n → ℂ) (q : MvPolynomial (Fin n) ℂ) :
    aeval u (PolynomialJets.translate P q) =
      aeval (fun k => u k + algebraMap ℂ A (P k)) q := by
  unfold PolynomialJets.translate
  rw [aeval_eq_eval₂Hom, eval₂_comp_left, aeval_def]
  congr 1
  · ext c
    simp
  · funext j
    simp

/-- An algebra map out of the germ ring, applied to a polynomial germ, is `aeval` of its
values on the coordinate germs. -/
theorem algHom_polynomialGerm {n : ℕ} (ρ : GermRing n →ₐ[ℂ] A) (q : Poly n) :
    ρ (polynomialGerm n q) = aeval (fun k => ρ (coordinate n k)) q := by
  have h := congrArg (fun φ : Poly n →ₐ[ℂ] A => φ q) (comp_aeval (f := coordinate n) ρ)
  simpa [polynomialGerm] using h

/-- The image of a generated ideal lies in a kernel iff every generator maps to zero. -/
theorem map_span_le_ker {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (f : ι → R) (h : ∀ r, ψ (φ (f r)) = 0) :
    Ideal.map φ (Ideal.span (Set.range f)) ≤ RingHom.ker ψ := by
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  simpa [Ideal.mem_comap, RingHom.mem_ker] using h r

/-- The consumer's containment premise, derived from coordinate values and generic vanishing. -/
theorem translated_fIdeal_le_iInf_ker {m : ℕ}
    (P : Fin 1053 → ℂ) (ρ : Fin 4 → GermRing 1053 →ₐ[ℂ] GermRing m)
    (γ : Fin 4 → Fin 1053 → GermRing m)
    (hρ : ∀ i k, ρ i (coordinate 1053 k) = γ i k - algebraMap ℂ (GermRing m) (P k))
    (hvan : ∀ i (r : Fin 2184), aeval (γ i) (fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0) :
    Ideal.map (polynomialGerm 1053).toRingHom
        (Ideal.span (Set.range fun r : Fin 2184 =>
          PolynomialJets.translate P (fRow (1/2 : ℂ) (1/3 : ℂ) r))) ≤
      ⨅ i, RingHom.ker (ρ i).toRingHom := by
  refine le_iInf fun i => ?_
  have key : ∀ r : Fin 2184,
      ρ i (polynomialGerm 1053 (PolynomialJets.translate P (fRow (1/2 : ℂ) (1/3 : ℂ) r))) = 0 := by
    intro r
    rw [algHom_polynomialGerm, aeval_translate]
    have hshift : (fun k => ρ i (coordinate 1053 k) + algebraMap ℂ (GermRing m) (P k)) = γ i := by
      funext k; rw [hρ]; ring
    rw [hshift]
    exact hvan i r
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
  rintro _ ⟨r, rfl⟩
  simpa [Ideal.mem_comap, RingHom.mem_ker] using key r

end FourSheets.Plumbing

#print axioms FourSheets.Plumbing.aeval_translate
#print axioms FourSheets.Plumbing.algHom_polynomialGerm
#print axioms FourSheets.Plumbing.map_span_le_ker
#print axioms FourSheets.Plumbing.translated_fIdeal_le_iInf_ker

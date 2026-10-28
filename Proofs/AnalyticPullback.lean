/-
Generic analytic pullback package for the convergent germ rings
`ConvergentResidualJets.GermRing n`: composition with an analytic map
fixing zero as a complex-algebra map, surjectivity from a first-order left
inverse (inverse function theorem), and tangent-range inclusion from kernel
inclusion. First-party composition over Mathlib and ConvergentResidualJetMap;
no upstream proof body copied. Pin: Lean v4.35.0-rc2, Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thank you to the Lean and Mathlib
contributors and to the author of the germ-ring carrier.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
module

public import ConvergentResidualJetMap
public import Mathlib.Analysis.Analytic.Inverse
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Analytic pullback on convergent germ rings

For `φ : (Fin m → ℂ) → (Fin n → ℂ)` analytic at `0` with `φ 0 = 0`, composition
with `φ` sends germs at `0` with an analytic representative to germs at `0`
with an analytic representative. This gives `pullback φ hφ h0 : GermRing n →ₐ[ℂ] GermRing m`.

* If `φ` has a derivative `A` at `0` with a continuous linear left inverse `L`
  (`L ∘ A = id`), the pullback is surjective: `ψ := L ∘ φ` is a local analytic
  diffeomorphism at `0`, and `g = (g ∘ ψ⁻¹ ∘ L) ∘ φ` near `0`.
* If the kernel of `pullback φ` is contained in the kernel of `pullback χ`
  (same source and target), then `χ = φ ∘ ψ⁻¹ ∘ L ∘ χ` near `0`, so the tangent
  range of `χ` lies in the tangent range of `φ`.
* Convenience forms: a covector separating the two tangent ranges refutes the
  kernel inclusion; a matrix minor with an explicit inverse supplies `L`.
-/

noncomputable section

open Filter Matrix ConvergentResidualJets
open scoped Topology

namespace AnalyticPullback

variable {m n : ℕ}

/-! ## The pullback algebra map -/

theorem tendsto_of_analyticAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) : Tendsto φ (𝓝 0) (𝓝 0) := by
  have h := hφ.continuousAt.tendsto
  rwa [h0] at h

/-- Composition with `φ` on all neighborhood germs, as a ring map. -/
def germComp (φ : (Fin m → ℂ) → (Fin n → ℂ))
    (hT : Tendsto φ (𝓝 (0 : Fin m → ℂ)) (𝓝 (0 : Fin n → ℂ))) :
    Germ (𝓝 (0 : Fin n → ℂ)) ℂ →+* Germ (𝓝 (0 : Fin m → ℂ)) ℂ where
  toFun g := g.compTendsto φ hT
  map_one' := rfl
  map_mul' a b := Germ.inductionOn₂ a b fun _ _ => rfl
  map_zero' := rfl
  map_add' a b := Germ.inductionOn₂ a b fun _ _ => rfl

theorem germComp_coe (φ : (Fin m → ℂ) → (Fin n → ℂ))
    (hT : Tendsto φ (𝓝 (0 : Fin m → ℂ)) (𝓝 (0 : Fin n → ℂ))) (f : (Fin n → ℂ) → ℂ) :
    germComp φ hT (f : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) =
      ((f ∘ φ : (Fin m → ℂ) → ℂ) : Germ (𝓝 (0 : Fin m → ℂ)) ℂ) := rfl

theorem germComp_mem (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    (g : Germ (𝓝 (0 : Fin n → ℂ)) ℂ) (hg : g ∈ analyticGermSubring n) :
    germComp φ (tendsto_of_analyticAt φ hφ h0) g ∈ analyticGermSubring m := by
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨f ∘ φ, hf.comp_of_eq hφ h0, rfl⟩

/-- Pullback of convergent germs along an analytic map fixing zero. -/
def pullback (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) :
    GermRing n →ₐ[ℂ] GermRing m where
  toRingHom := (germComp φ (tendsto_of_analyticAt φ hφ h0)).restrict
    (analyticGermSubring n) (analyticGermSubring m) (germComp_mem φ hφ h0)
  commutes' _ := rfl

theorem pullback_ofAnalyticAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    pullback φ hφ h0 (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ φ) (hf.comp_of_eq hφ h0) := rfl

theorem analyticAt_apply (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) (k : Fin n) : AnalyticAt ℂ (fun x => φ x k) 0 :=
  ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0).comp_of_eq hφ h0

/-- The germ of the `k`-th component of `φ`. -/
def componentGerm (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) (k : Fin n) : GermRing m :=
  ofAnalyticAt (fun x => φ x k) (analyticAt_apply φ hφ h0 k)

theorem pullback_coordinate (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) (k : Fin n) :
    pullback φ hφ h0 (coordinate n k) = componentGerm φ hφ h0 k := rfl

theorem pullback_comp_polynomialGerm (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) :
    (pullback φ hφ h0).comp (polynomialGerm n) = MvPolynomial.aeval (componentGerm φ hφ h0) :=
  MvPolynomial.comp_aeval (coordinate n) (pullback φ hφ h0)

theorem pullback_polynomialGerm (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) (q : Poly n) :
    pullback φ hφ h0 (polynomialGerm n q) = MvPolynomial.aeval (componentGerm φ hφ h0) q :=
  DFunLike.congr_fun (pullback_comp_polynomialGerm φ hφ h0) q

theorem ofAnalyticAt_eq_zero_iff {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    ofAnalyticAt f hf = 0 ↔ f =ᶠ[𝓝 0] (0 : (Fin n → ℂ) → ℂ) :=
  ofAnalyticAt_eq_iff hf analyticAt_const

/-! ## The local inverse of the retraction `L ∘ φ` -/

section Inverse

theorem retraction_analyticAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0)
    (L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)) :
    AnalyticAt ℂ (L ∘ φ) 0 :=
  (L.analyticAt (φ 0)).comp hφ

theorem retraction_hasStrictFDerivAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) :
    HasStrictFDerivAt (L ∘ φ)
      ((ContinuousLinearEquiv.refl ℂ (Fin m → ℂ) : (Fin m → ℂ) ≃L[ℂ] (Fin m → ℂ)) :
        (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) 0 := by
  have h1 : HasFDerivAt (L ∘ φ) (L.comp A) 0 := L.hasFDerivAt.comp 0 hA
  have h2 := (retraction_analyticAt φ hφ L).hasStrictFDerivAt
  rw [h1.fderiv, hL] at h2
  rw [ContinuousLinearEquiv.coe_refl]
  exact h2

/-- The local chart: `L ∘ φ` repackaged as an open partial homeomorphism near `0`. -/
def chart (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : OpenPartialHomeomorph (Fin m → ℂ) (Fin m → ℂ) :=
  (retraction_hasStrictFDerivAt φ hφ hA hL).toOpenPartialHomeomorph (L ∘ φ)

theorem chart_coe (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : (chart φ hφ hA hL : (Fin m → ℂ) → (Fin m → ℂ)) = L ∘ φ := rfl

theorem zero_mem_chart_source (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : (0 : Fin m → ℂ) ∈ (chart φ hφ hA hL).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

theorem chart_zero (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : chart φ hφ hA hL 0 = 0 := by
  change L (φ 0) = 0
  rw [h0, map_zero]

theorem chart_symm_zero (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : (chart φ hφ hA hL).symm 0 = 0 := by
  have h := (chart φ hφ hA hL).left_inv (zero_mem_chart_source φ hφ hA hL)
  rwa [chart_zero φ hφ h0 hA hL] at h

theorem chart_symm_analyticAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : AnalyticAt ℂ (chart φ hφ hA hL).symm 0 := by
  obtain ⟨p, hp⟩ := retraction_analyticAt φ hφ L
  have hp' : HasFPowerSeriesAt (chart φ hφ hA hL) p 0 := hp
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (Fin m → ℂ) (Fin m → ℂ)).symm
      (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ) : (Fin m → ℂ) ≃L[ℂ] (Fin m → ℂ)) := by
    have h := hp.hasFDerivAt.unique (retraction_hasStrictFDerivAt φ hφ hA hL).hasFDerivAt
    have h' := congrArg (continuousMultilinearCurryFin1 ℂ (Fin m → ℂ) (Fin m → ℂ)).symm h
    simpa using h'
  have h := (chart φ hφ hA hL).hasFPowerSeriesAt_symm (zero_mem_chart_source φ hφ hA hL) hp' hp1
  rw [chart_zero φ hφ h0 hA hL] at h
  exact h.analyticAt

theorem chartSymmComp_analyticAt (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : AnalyticAt ℂ ((chart φ hφ hA hL).symm ∘ L) 0 :=
  (chart_symm_analyticAt φ hφ h0 hA hL).comp_of_eq (L.analyticAt 0) (map_zero L)

theorem chartSymmComp_zero (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : ((chart φ hφ hA hL).symm ∘ L) 0 = 0 := by
  change (chart φ hφ hA hL).symm (L 0) = 0
  rw [map_zero, chart_symm_zero φ hφ h0 hA hL]

/-! ## Surjectivity -/

/-- A first-order left inverse of the derivative makes the pullback surjective. -/
theorem surjective_pullback (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ)) : Function.Surjective (pullback φ hφ h0) := by
  rintro ⟨_, g, hg, rfl⟩
  have hf : AnalyticAt ℂ (g ∘ (chart φ hφ hA hL).symm ∘ L) 0 :=
    hg.comp_of_eq (chartSymmComp_analyticAt φ hφ h0 hA hL) (chartSymmComp_zero φ hφ h0 hA hL)
  refine ⟨ofAnalyticAt _ hf, ?_⟩
  rw [pullback_ofAnalyticAt]
  change ofAnalyticAt _ _ = ofAnalyticAt g hg
  rw [ofAnalyticAt_eq_iff]
  filter_upwards [(chart φ hφ hA hL).eventually_left_inverse (zero_mem_chart_source φ hφ hA hL)]
    with x hx
  exact congrArg g hx

/-! ## Kernel inclusion gives tangent-range inclusion -/

theorem eventuallyEq_of_ker_le (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ))
    (χ : (Fin m → ℂ) → (Fin n → ℂ)) (hχ : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0)
    (hker : RingHom.ker (pullback φ hφ h0).toRingHom ≤ RingHom.ker (pullback χ hχ hχ0).toRingHom) :
    χ =ᶠ[𝓝 0] φ ∘ (chart φ hφ hA hL).symm ∘ L ∘ χ := by
  have key : ∀ k : Fin n, ∀ᶠ x in 𝓝 (0 : Fin m → ℂ),
      χ x k = φ (((chart φ hφ hA hL).symm ∘ L) (χ x)) k := by
    intro k
    have hk : AnalyticAt ℂ
        (fun y : Fin n → ℂ => y k - φ (((chart φ hφ hA hL).symm ∘ L) y) k) 0 := by
      apply AnalyticAt.sub
      · exact (ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0
      · exact (analyticAt_apply φ hφ h0 k).comp_of_eq (chartSymmComp_analyticAt φ hφ h0 hA hL)
          (chartSymmComp_zero φ hφ h0 hA hL)
    have hmem : ofAnalyticAt _ hk ∈ RingHom.ker (pullback φ hφ h0).toRingHom := by
      rw [RingHom.mem_ker]
      change pullback φ hφ h0 (ofAnalyticAt _ hk) = 0
      rw [pullback_ofAnalyticAt, ofAnalyticAt_eq_zero_iff]
      filter_upwards [(chart φ hφ hA hL).eventually_left_inverse
        (zero_mem_chart_source φ hφ hA hL)] with x hx
      change φ x k - φ ((chart φ hφ hA hL).symm (chart φ hφ hA hL x)) k = 0
      rw [hx, sub_self]
    have h := hker hmem
    rw [RingHom.mem_ker] at h
    change pullback χ hχ hχ0 (ofAnalyticAt _ hk) = 0 at h
    rw [pullback_ofAnalyticAt, ofAnalyticAt_eq_zero_iff] at h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp hx
  filter_upwards [Filter.eventually_all.mpr key] with x hx
  funext k
  exact hx k

/-- Kernel inclusion of the pullbacks forces inclusion of the tangent ranges. -/
theorem range_le_of_ker_le (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ))
    (χ : (Fin m → ℂ) → (Fin n → ℂ)) (hχ : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) {B : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hB : HasFDerivAt χ B 0)
    (hker : RingHom.ker (pullback φ hφ h0).toRingHom ≤ RingHom.ker (pullback χ hχ hχ0).toRingHom) :
    LinearMap.range (B : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≤
      LinearMap.range (A : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
  set D := fderiv ℂ ((chart φ hφ hA hL).symm : (Fin m → ℂ) → (Fin m → ℂ)) 0 with hDdef
  have hD : HasFDerivAt (chart φ hφ hA hL).symm D 0 :=
    (chart_symm_analyticAt φ hφ h0 hA hL).differentiableAt.hasFDerivAt
  have h1 : HasFDerivAt (L ∘ χ) (L.comp B) 0 := L.hasFDerivAt.comp 0 hB
  have h2 : HasFDerivAt ((chart φ hφ hA hL).symm ∘ L ∘ χ) (D.comp (L.comp B)) 0 := by
    refine HasFDerivAt.comp 0 ?_ h1
    have hz : (L ∘ χ) 0 = 0 := by
      change L (χ 0) = 0
      rw [hχ0, map_zero]
    rw [hz]
    exact hD
  have h3 : HasFDerivAt (φ ∘ (chart φ hφ hA hL).symm ∘ L ∘ χ) (A.comp (D.comp (L.comp B))) 0 := by
    refine HasFDerivAt.comp 0 ?_ h2
    have hz : ((chart φ hφ hA hL).symm ∘ L ∘ χ) 0 = 0 := by
      change (chart φ hφ hA hL).symm (L (χ 0)) = 0
      rw [hχ0, map_zero, chart_symm_zero φ hφ h0 hA hL]
    rw [hz]
    exact hA
  have hχ' : HasFDerivAt χ (A.comp (D.comp (L.comp B))) 0 :=
    h3.congr_of_eventuallyEq (eventuallyEq_of_ker_le φ hφ h0 hA hL χ hχ hχ0 hker)
  have hEq : B = A.comp (D.comp (L.comp B)) := hB.unique hχ'
  intro y hy
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hy
  refine LinearMap.mem_range.mpr ⟨D (L (B v)), ?_⟩
  have h := DFunLike.congr_fun hEq v
  simp only [ContinuousLinearMap.comp_apply] at h
  simp only [ContinuousLinearMap.coe_coe]
  exact h.symm

/-- A covector vanishing on the tangent range of `φ` but not of `χ` refutes kernel inclusion. -/
theorem not_ker_le_of_covector (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) {A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hA : HasFDerivAt φ A 0)
    {L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)} (hL : L.comp A = ContinuousLinearMap.id ℂ (Fin m → ℂ))
    (χ : (Fin m → ℂ) → (Fin n → ℂ)) (hχ : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) {B : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)} (hB : HasFDerivAt χ B 0)
    (w : Fin n → ℂ) (hw : ∀ v, ∑ k, w k * A v k = 0) (hw' : ∃ v, ∑ k, w k * B v k ≠ 0) :
    ¬ RingHom.ker (pullback φ hφ h0).toRingHom ≤ RingHom.ker (pullback χ hχ hχ0).toRingHom := by
  intro hker
  obtain ⟨v, hv⟩ := hw'
  have hr := range_le_of_ker_le φ hφ h0 hA hL χ hχ hχ0 hB hker
    (LinearMap.mem_range_self (B : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) v)
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hr
  simp only [ContinuousLinearMap.coe_coe] at hu
  apply hv
  rw [← hu]
  exact hw u

end Inverse

/-! ## Matrix forms -/

section MatrixForms

/-- The continuous linear map `v ↦ M *ᵥ v`. -/
def matrixCLM {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) : (Fin q → ℂ) →L[ℂ] (Fin p → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

theorem matrixCLM_apply {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ) (v : Fin q → ℂ) :
    matrixCLM M v = M *ᵥ v := by
  simp [matrixCLM, Matrix.toLin'_apply]

/-- The row-selection matrix `(selectionMatrix S) i j = if S i = j then 1 else 0`. -/
def selectionMatrix (S : Fin m → Fin n) : Matrix (Fin m) (Fin n) ℂ :=
  (1 : Matrix (Fin n) (Fin n) ℂ).submatrix S id

theorem selectionMatrix_mul (S : Fin m → Fin n) (M : Matrix (Fin n) (Fin m) ℂ) :
    selectionMatrix S * M = M.submatrix S id := by
  ext i k
  simp [selectionMatrix, Matrix.mul_apply, Matrix.one_apply]

/-- The left inverse `N * selectionMatrix S` of a tangent matrix with an invertible minor. -/
def leftInverseCLM (S : Fin m → Fin n) (N : Matrix (Fin m) (Fin m) ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) :=
  matrixCLM (N * selectionMatrix S)

theorem leftInverse_of_minor (M : Matrix (Fin n) (Fin m) ℂ) (S : Fin m → Fin n)
    (N : Matrix (Fin m) (Fin m) ℂ) (hN : N * M.submatrix S id = 1) :
    (leftInverseCLM S N).comp (matrixCLM M) = ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, leftInverseCLM,
    matrixCLM_apply, matrixCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    selectionMatrix_mul, hN, Matrix.one_mulVec]

/-- Surjectivity from a tangent matrix with an explicitly inverted `m × m` minor. -/
theorem surjective_pullback_of_minor (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0) (M : Matrix (Fin n) (Fin m) ℂ)
    (hA : HasFDerivAt φ (matrixCLM M) 0) (S : Fin m → Fin n) (N : Matrix (Fin m) (Fin m) ℂ)
    (hN : N * M.submatrix S id = 1) : Function.Surjective (pullback φ hφ h0) :=
  surjective_pullback φ hφ h0 hA (leftInverse_of_minor M S N hN)

theorem sum_mul_matrixCLM_apply (M : Matrix (Fin n) (Fin m) ℂ) (w : Fin n → ℂ) (v : Fin m → ℂ) :
    ∑ k, w k * matrixCLM M v k = (w ᵥ* M) ⬝ᵥ v := by
  rw [matrixCLM_apply]
  exact Matrix.dotProduct_mulVec w M v

/-- Matrix form: a row covector killing the tangent matrix of `φ` but not that of `χ`
refutes kernel inclusion. -/
theorem not_ker_le_of_vecMul (φ : (Fin m → ℂ) → (Fin n → ℂ)) (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    (χ : (Fin m → ℂ) → (Fin n → ℂ)) (hχ : AnalyticAt ℂ χ 0) (hχ0 : χ 0 = 0) (M M' : Matrix (Fin n) (Fin m) ℂ)
    (hA : HasFDerivAt φ (matrixCLM M) 0) (hB : HasFDerivAt χ (matrixCLM M') 0)
    (S : Fin m → Fin n) (N : Matrix (Fin m) (Fin m) ℂ) (hN : N * M.submatrix S id = 1)
    (w : Fin n → ℂ) (hw : w ᵥ* M = 0) (hw' : w ᵥ* M' ≠ 0) :
    ¬ RingHom.ker (pullback φ hφ h0).toRingHom ≤ RingHom.ker (pullback χ hχ hχ0).toRingHom := by
  refine not_ker_le_of_covector φ hφ h0 hA (leftInverse_of_minor M S N hN) χ hχ hχ0 hB w ?_ ?_
  · intro v
    rw [sum_mul_matrixCLM_apply, hw, zero_dotProduct]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hw'
    refine ⟨Pi.single j 1, ?_⟩
    rw [sum_mul_matrixCLM_apply, dotProduct_single_one]
    exact hj

end MatrixForms

end AnalyticPullback

end

#print axioms AnalyticPullback.pullback_ofAnalyticAt
#print axioms AnalyticPullback.pullback_coordinate
#print axioms AnalyticPullback.pullback_polynomialGerm
#print axioms AnalyticPullback.chart_symm_analyticAt
#print axioms AnalyticPullback.surjective_pullback
#print axioms AnalyticPullback.eventuallyEq_of_ker_le
#print axioms AnalyticPullback.range_le_of_ker_le
#print axioms AnalyticPullback.not_ker_le_of_covector
#print axioms AnalyticPullback.leftInverse_of_minor
#print axioms AnalyticPullback.surjective_pullback_of_minor
#print axioms AnalyticPullback.not_ker_le_of_vecMul

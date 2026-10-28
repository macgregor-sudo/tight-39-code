module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Algebra.Group.Even
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Germ
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.SmallInductiveDimension
public import GPCode
public import NativeComplementaryDictionary
public import SupportedStressCriterionV3
public import EFMain
@[expose] public section
set_option backward.proofsInPublic true
noncomputable section
open scoped BigOperators Quaternion
/-
The analytic-representative carrier, constant map and evaluation below adapt
SeveralComplexVariables/AnalyticGerm.lean, declarations analyticGermSubring,
AnalyticGerm.ofAnalyticAt, AnalyticGerm.const and AnalyticGerm.eval, from
https://github.com/bjbraams/lean-SCV at
50392764ae64d75779abbea1396fe93d80b677cc.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: Bastiaan J Braams
Modifications: specialize to complex germs at zero in finite coordinate spaces;
omit the local-ring, zero-set and Noetherian development; add the polynomial
residual quotient map. Adapted portions retain their upstream license.
Thank you to the author and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
/- Canonical native-v3 problem definitions only. Native declarations and literal membership are imported from genuine providers; no Challenge theorem is imported. -/
namespace Option2StatementCode
open Glennie CKM.NativeTightCode
set_option maxHeartbeats 1600000 in
def codeSetoid : Setoid tightLocus where
  r C D := ∃ g : Albert ≃ₗ[ℝ] Albert, (∀ x y, g (jordan x y) = jordan (g x) (g y)) ∧ ∃ e : Equiv.Perm (Fin 39), ∀ i, g (codePoint C.1 i) = codePoint D.1 (e i)
  iseqv := by
    constructor
    · intro C
      exact ⟨LinearEquiv.refl ℝ Albert, fun _ _ => rfl, Equiv.refl _, fun _ => rfl⟩
    · rintro C D ⟨g, hg, e, he⟩
      refine ⟨g.symm, ?_, e.symm, ?_⟩
      · intro x y
        apply g.injective; simp only [LinearEquiv.apply_symm_apply, hg]
      · intro i
        apply g.injective; simpa only [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] using
          (he (e.symm i)).symm
    · rintro C D E ⟨g, hg, e, he⟩ ⟨h, hh, f, hf⟩
      refine ⟨g.trans h, ?_, e.trans f, ?_⟩
      · intro x y
        change h (g (jordan x y)) = jordan (h (g x)) (h (g y)); rw [hg, hh]
      · intro i
        change h (g (codePoint C.1 i)) = codePoint E.1 (f (e i)); rw [he, hf]
abbrev CodeModuli := Quotient codeSetoid
def codeClass (C : CodeCoords) (hC : C ∈ tightLocus) : CodeModuli := Quotient.mk codeSetoid ⟨C, hC⟩
end Option2StatementCode
namespace Option2StatementCode
def phaseClass (u : CKM.NativeGoodPhase.PhaseTorus) : CodeModuli := codeClass (CKM.NativeFirstOrder.literalCfg u.1)
  (CKM.NativeUnlabelledSlice.literalCfg_mem_tightLocus u.1 u.2)
abbrev originalCode : CodeModuli := phaseClass CKM.NativeGoodPhase.onePhase
end Option2StatementCode
namespace Option2StatementCode
open CKM.NativeGoodPhase
open scoped Topology
end Option2StatementCode

namespace Option2StatementResidual
open scoped BigOperators
open ConfigurationResidualIndices NativePolynomial CKM.NativeTightCode
abbrev Configuration := Fin 39 → Fin 27 → ℝ
abbrev Residuals := Fin 2184 → ℝ
def framePointIndex (f : Fin 13) (a : Fin 3) : Fin 39 := ⟨3 * f.val + a.val, by omega⟩
def originalValue (C : Configuration) : FLabel → ℝ
  | .inl (i, k) => upperCoordinates (Glennie.jordan (codePoint C i) (codePoint C i)) k - C i k | .inr (.inl i) => (C i 0 + C i 1 + C i 2) - 1
  | .inr (.inr (.inl (f, k))) => (∑ a : Fin 3, C (framePointIndex f a) k) - (if k.val < 3 then 1 else 0)
  | .inr (.inr (.inr ij)) => (∑ k : Fin 27, (if k.val < 3 then (1 : ℝ) else 2) * C ij.val.1 k * C ij.val.2 k) -
        (if ij.val.1.val / 3 = ij.val.2.val / 3 then 0 else 1 / 3)
def originalF (C : Configuration) : Residuals := fun r => originalValue C (fNumber.symm r)
end Option2StatementResidual
namespace Option2StatementA1
open CompactAlbert UnitaryErrorBases.ComplexQuartet
def LiteralReadouts (x : Glennie.Albert) : Prop := (∀ t : Fin 3, Glennie.trace (Glennie.jordan x (literalNativeCoordinatePoint t)) = (1/3 : ℝ)) ∧ (∀ s t : PhaseIndex,
  Glennie.trace (Glennie.jordan x (literalNativePhasePoint s t)) = (1/3 : ℝ))
abbrev State := {x : Glennie.Albert // Glennie.jordan x x = x ∧ LiteralReadouts x}
abbrev SU3 := {U : TitsComplexMatrix // U * U.conjTranspose = 1 ∧ U.det = 1}
def matrixPair (x : Glennie.Albert) : TitsComplexMatrix × TitsComplexMatrix := (hermitianMatrix (toTitsCoordinates x), (toTitsCoordinates x).2.2)
def FixesQuartet (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) : Prop := (∀ t : Fin 3, f (literalNativeCoordinatePoint t) = literalNativeCoordinatePoint t) ∧ (∀ s t :
  PhaseIndex, f (literalNativePhasePoint s t) = literalNativePhasePoint s t)
open CompactAlbert
end Option2StatementA1
namespace Option2StatementCode
end Option2StatementCode
namespace Option2StatementA3
open CKM.NativeFirstOrder
open scoped BigOperators
noncomputable def resonanceCount (ξ : Fin 4 → ℂ) (H : Fin 4) : ℕ := by classical exact Fintype.card {j : UnitaryErrorBases.Index // anchorPhases ξ H j ^ 3 = 1}
open CKM.NativeFirstOrder
open scoped BigOperators
end Option2StatementA3
namespace Option2StatementA1
open CompactAlbert
end Option2StatementA1
open scoped BigOperators Matrix.Norms.Elementwise
namespace Option2StatementA3Matrix
abbrev Index := ZMod 3
abbrev Mat := Matrix Index Index ℂ
abbrev Label := Index × Index
abbrev Family := Label → Mat
abbrev Residual := (Label → Mat) × (Label → ℂ) × (Label → Label → ℂ)
def omega : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2
def shift : Mat := fun i j => if i = j + 1 then 1 else 0
def clock : Mat := Matrix.diagonal (fun j => omega ^ j.val)
abbrev PhaseTriple := {d : Index → ℂ // (∀ j, Complex.normSq (d j) = 1) ∧ ∏ j, d j = 1}
def phaseMatrix (d : PhaseTriple) (b : Index) : Mat := Matrix.diagonal (fun j => if b = 2 then d.val j else 1)
def monomialFamily (d : PhaseTriple) : Family := fun p => shift ^ p.2.val * phaseMatrix d p.2 * clock ^ p.1.val
def residual (U : Family) : Residual := (fun p => (U p).conjTranspose * U p - 1, fun p => (U p).det - 1, fun p q => if p = q then 0 else Matrix.trace ((U
  p).conjTranspose * U q))
def firstOrderSpace (U : Family) : Submodule ℝ Family := (fderiv ℝ residual U).toLinearMap.ker
def SatisfiesFirstOrder (U V : Family) : Prop := (∀ p, (U p).conjTranspose * V p + (V p).conjTranspose * U p = 0) ∧ (∀ p, Matrix.trace ((U p).conjTranspose * V p) =
  0) ∧ (∀ p q, p ≠ q → Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q) = 0)
abbrev ResonantIndex (d : PhaseTriple) := {j : Index // d.val j ^ 3 = 1}
def resonanceCount (d : PhaseTriple) : ℕ := by classical exact Fintype.card (ResonantIndex d)
abbrev NormalForm (d : PhaseTriple) := (Fin 6 → ℝ) × (Fin 6 → ℂ) × (ResonantIndex d → ℂ)
abbrev Coordinates := Index → Index → Index → ℂ
def character (r : Index) : ℂ := omega ^ r.val
def inverse (z : Coordinates) (a b k : Index) : ℂ := ∑ mu, z b k mu * character (mu * a)
def reconstruct (d : PhaseTriple) (a : Index → Index → ℂ) : Coordinates := fun b k mu => if b = 0 then a k mu else if b = 1 then a (k + mu + 1) mu else d.val (k + mu
  + 1) / d.val k * a (k + mu + 1 + mu + 1) mu
def sixIndex : (Index × Fin 2) ≃ Fin 6 := (((ZMod.finEquiv 3).toEquiv.symm).prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv
def normalFormDiagonal {d : PhaseTriple} (x : NormalForm d) : Index → Fin 2 → ℝ := fun b t => x.1 (sixIndex (b, t))
def normalFormSeed (d : PhaseTriple) (x : NormalForm d) : Index → Index → ℂ := by classical exact
  (fun k mu => if mu = 1 then (if h : d.val (k + 1) ^ 3 = 1 then x.2.2 ⟨k + 1, h⟩ else 0)
    else if mu = 0 then x.2.1 (sixIndex (k, 0)) else x.2.1 (sixIndex (k, 1)))
def tracelessDiagonal (s : Fin 2 → ℝ) (k : Index) : ℝ := if k = 0 then s 0 else if k = 1 then s 1 else -s 0 - s 1
def parameterMatrix (s : Index → Fin 2 → ℝ) (y : Coordinates) : Family := fun p i j => if i = j then Complex.I * (tracelessDiagonal (s p.2) i : ℂ) else if j = i + 1
  then y p.1 p.2 i else -star (y p.1 p.2 j)
def fromCoordinates (d : PhaseTriple) (M : Family) : Family := fun p => (shift ^ p.2.val * phaseMatrix d p.2) * M p * clock ^ p.1.val
def tangentOfNormalForm (d : PhaseTriple) (x : NormalForm d) : Family := fromCoordinates d (parameterMatrix (normalFormDiagonal x) (inverse (reconstruct d
  (normalFormSeed d x))))
end Option2StatementA3Matrix
open scoped BigOperators Matrix.Norms.Elementwise Manifold ContDiff Topology
namespace Option2StatementA2
open Option2StatementA3Matrix CompactAlbert NativePolynomial
abbrev SU3 := Matrix.specialUnitaryGroup Index ℂ
abbrev PSU3 := SU3 ⧸ Subgroup.center SU3
abbrev Parameter := PSU3 × PhaseTriple
abbrev Cfg := Fin 39 → Fin 27 → ℝ
attribute [local instance 1001] Complex.instFiniteDimensionalReal
def differential : Mat →L[ℝ] Mat × ℝ := (((starL' ℝ : Mat ≃L[ℝ] Mat) : Mat →L[ℝ] Mat) + ContinuousLinearMap.id ℝ Mat).prod (Complex.imCLM.comp (Matrix.traceLinearMap
  Index ℝ ℂ).toContinuousLinearMap)
abbrev Tangent := LinearMap.ker differential.toLinearMap
abbrev Model := Tangent × (ℝ × ℝ)
def recovery (A : Mat) : Mat :=
  let B := A-1
  B - ((1/2:ℝ) • (B.conjTranspose+B) + (Complex.I*((Matrix.trace B).im/3:ℝ)) • (1:Mat))
def phaseValues (a b : ℂ) : Index → ℂ := fun j => if j=0 then a else if j=1 then b else (a*b)⁻¹
def phaseExpValues (d : PhaseTriple) (x : ℝ×ℝ) : Index → ℂ :=
  phaseValues (d.val 0 * (Circle.exp x.1:ℂ)) (d.val 1 * (Circle.exp x.2:ℂ))
def nativeArray (Q : Mat) (d : PhaseTriple) (r : Fin 9) : TitsComplexMatrix :=
  let e := (ZMod.finEquiv 3).toEquiv
  let l := ((e.symm.prodCongr e.symm).trans finProdFinEquiv).symm r
  fun i j => (Q * monomialFamily d l * Q.conjTranspose) (e i) (e j)
def packCfg (y : Cfg) : Fin 1053 → ℝ := fun i => y (Fin.divNat (m:=39) (n:=27) i) (Fin.modNat (m:=39) (n:=27) i)
structure Charts where
  (su : SU3 → OpenPartialHomeomorph SU3 Tangent) (lift : SU3 → OpenPartialHomeomorph PSU3 SU3) (phase : PhaseTriple → OpenPartialHomeomorph (ℝ×ℝ) PhaseTriple)
  (representative : PSU3 → SU3) (quotientAtlas : ChartedSpace Tangent PSU3) (phaseAtlas : ChartedSpace (ℝ×ℝ) PhaseTriple)
@[instance_reducible] def Charts.productAtlas (a : Charts) : @ChartedSpace Model (inferInstance : NormedAddCommGroup Model).toUniformSpace.toTopologicalSpace Parameter inferInstance :=
  @prodChartedSpace Tangent _ PSU3 _ a.quotientAtlas (ℝ×ℝ) _ PhaseTriple _ a.phaseAtlas
structure ChartsPinned (a : Charts) : Prop where
  (su_source : ∀ Q, Q ∈ (a.su Q).source) (su_coordinates : ∀ Q R, (a.su Q R).val = recovery (Q.val.conjTranspose * R.val))
  (su_inverse_analytic : ∀ Q, AnalyticOnNhd ℝ (fun k => ((a.su Q).symm k).val) (a.su Q).target)
  (lift_inverse : ∀ Q R, (a.lift Q).symm R = (QuotientGroup.mk R : PSU3)) (lift_self : ∀ Q, a.lift Q (QuotientGroup.mk Q) = Q)
  (lift_source : ∀ Q, (QuotientGroup.mk Q : PSU3) ∈ (a.lift Q).source) (phase_zero : ∀ d, (0:ℝ×ℝ) ∈ (a.phase d).source)
  (phase_formula : ∀ d x, (a.phase d x).val = phaseExpValues d x) (representative_mk : ∀ q, (QuotientGroup.mk (a.representative q) : PSU3) = q)
  (quotient_atlas : a.quotientAtlas.atlas = Set.range (fun Q => (a.lift Q).trans (a.su Q)))
  (quotient_chart : ∀ q, a.quotientAtlas.chartAt q = (a.lift (a.representative q)).trans (a.su (a.representative q)))
  (phase_atlas : a.phaseAtlas.atlas = Set.range (fun d => (a.phase d).symm)) (phase_chart : ∀ d, a.phaseAtlas.chartAt d = (a.phase d).symm)
structure Maps where
  (torus : PhaseTriple ≃ₜ Circle×Circle) (array : Parameter → Fin 9 → TitsComplexMatrix) (configuration : Parameter → Cfg)
def Maps.projectiveHomeomorph (f : Maps) : Parameter ≃ₜ PSU3×(Circle×Circle) := (Homeomorph.refl PSU3).prodCongr f.torus
structure MapsPinned (f : Maps) : Prop where
  torus_forward : ∀ d, ((f.torus d).1:ℂ) = d.val 0 ∧ ((f.torus d).2:ℂ) = d.val 1
  torus_inverse : ∀ z, (f.torus.symm z).val = phaseValues (z.1:ℂ) (z.2:ℂ)
  array_formula : ∀ Q:SU3, ∀ d, f.array (QuotientGroup.mk Q,d) = nativeArray Q.val d
  anchors : ∀ p i, i.val<12 → f.configuration p i = CKM.NativeFirstOrder.literalCfg (fun _=>1) i
  hidden : ∀ p r k, f.configuration p ⟨12+3*r.val+k.val, by omega⟩ = upperCoordinates (nativeCentralTriple (f.array p r) k)
def Conclusions (a : Charts) (f : Maps) : Prop :=
  letI : @ChartedSpace Model (inferInstance : NormedAddCommGroup Model).toUniformSpace.toTopologicalSpace Parameter inferInstance := a.productAtlas
  IsManifold 𝓘(ℝ,Model) ω Parameter ∧ Module.finrank ℝ Model = 10 ∧ (Topology.IsClosedEmbedding f.configuration ∧ ContMDiff 𝓘(ℝ,Model) 𝓘(ℝ,Cfg) ω f.configuration ∧
    Manifold.IsImmersion 𝓘(ℝ,Model) 𝓘(ℝ,Cfg) ω f.configuration) ∧ (Topology.IsClosedEmbedding (packCfg ∘ f.configuration) ∧ ContMDiff 𝓘(ℝ,Model) 𝓘(ℝ,Fin 1053→ℝ) ω
    (packCfg ∘ f.configuration) ∧ Manifold.IsImmersion 𝓘(ℝ,Model) 𝓘(ℝ,Fin 1053→ℝ) ω (packCfg ∘ f.configuration)) ∧ (∀ p, f.array p 0 = 1 ∧ (∀ r, f.array p r *
    (f.array p 0).conjTranspose = f.array p r) ∧ ∀ R:TitsComplexMatrix, (R*R.conjTranspose=1 ∧ R.det=1) → ∀ r, (f.array p r*R)*(f.array p 0*R).conjTranspose = f.array
    p r) ∧ ∀ p, Option2StatementResidual.originalF (f.configuration p) = 0
def FullA2 : Prop := ∃ a:Charts, ChartsPinned a ∧ ∃ f:Maps, MapsPinned f ∧ Conclusions a f
end Option2StatementA2
namespace Option2StatementA5
open Glennie NativePolynomial CKM.NativeTightCode
abbrev Automorphism := {g : Albert ≃ₗ[ℝ] Albert // ∀ x y, g (jordan x y) = jordan (g x) (g y)}
def act (g : Automorphism) (C : CodeCoords) : CodeCoords := fun i => upperCoordinates (g.1 (codePoint C i))
def saturation (S : Set CodeCoords) : Set CodeCoords := ⋃ g : Automorphism, (act g) '' S
def nativeOrbit (ξ : Fin 4 → ℂ) : Set CodeCoords := saturation {CKM.NativeFirstOrder.literalCfg ξ}
def commonPhase (ξ₀ : Fin 4 → ℂ) (θ : Fin 4 → ℝ) : Fin 4 → ℂ := fun a => ξ₀ a * Complex.exp ((θ a : ℂ) * Complex.I)
open Complex Filter Topology
open scoped Matrix BigOperators
def gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ := ![!![0, I, 0; I, 0, 0; 0, 0, 0], !![0, 1, 0; -1, 0, 0; 0, 0, 0], !![I, 0, 0; 0, -I, 0; 0, 0, 0], !![0, 0, I; 0, 0,
  0; I, 0, 0], !![0, 0, 1; 0, 0, 0; -1, 0, 0], !![0, 0, 0; 0, 0, I; 0, I, 0], !![0, 0, 0; 0, 0, 1; 0, -1, 0], !![I, 0, 0; 0, I, 0; 0, 0, -2 * I]]
def suMat (k : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := ∑ j, ((k j : ℝ) : ℂ) • gellMann j
def suExp (k : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := NormedSpace.exp (suMat k)
def IsGermImage {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] (S : Set X) (x : X) (f : P → X) (p : P) : Prop := ∃ U₀ ∈ 𝓝 p, ∀ U ∈ 𝓝 p, U ⊆ U₀ → f '' U =ᶠ[𝓝
  x] S
def IsGermSubset {P Q X : Type*} [TopologicalSpace P] [TopologicalSpace Q] (f : P → X) (p : P) (g : Q → X) (q : Q) : Prop := ∀ V ∈ 𝓝 q, ∃ U ∈ 𝓝 p, f '' U ⊆ g '' V
def commonBlock (ι Pc U R : Type*) [Zero U] [Zero R] : Set (Pc × (ι → U) × R) := {z | z.2.1 = 0 ∧ z.2.2 = 0}
def familyBlock {ι : Type*} (Pc U R : Type*) [Zero U] [Zero R] (i : ι) : Set (Pc × (ι → U) × R) := {z | (∀ j, j ≠ i → z.2.1 j = 0) ∧ z.2.2 = 0}
abbrev SliceModel := (Fin 4 → ℝ) × (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)
abbrev RawModel := (Fin 56 → ℝ) × (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)
end Option2StatementA5
namespace Option2StatementA5Anchor
open Glennie NativePolynomial CompactAlbert UnitaryErrorBases.ComplexQuartet
open scoped Matrix
abbrev Index := ZMod 3
abbrev Label := Index × Index
abbrev Mat := Matrix Index Index ℂ
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character
def T1_perm : List ℕ := [0, 1, 2, 5, 6, 3, 4, 9, 10, 7, 8, 15, 16, 17, 18, 11, 12, 13, 14, 25, 26, 23, 24, 21, 22, 19, 20]
def T1_sign : List ℤ := [1, 1, 1, (-1), 1, 1, 1, 1, 1, (-1), 1, (-1), (-1), (-1), 1, 1, (-1), 1, 1, (-1), (-1), 1, (-1), 1, 1, (-1), 1]
def T1_inv_perm : List ℕ := [0, 1, 2, 5, 6, 3, 4, 9, 10, 7, 8, 15, 16, 17, 18, 11, 12, 13, 14, 25, 26, 23, 24, 21, 22, 19, 20]
def T1_inv_sign : List ℤ := [1, 1, 1, 1, 1, (-1), 1, (-1), 1, 1, 1, 1, (-1), 1, 1, (-1), (-1), (-1), 1, (-1), 1, 1, 1, 1, (-1), (-1), (-1)]
def T2_perm : List ℕ := [0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 17, 18, 15, 16, 13, 14, 11, 12, 21, 22, 19, 20, 25, 26, 23, 24]
def T2_sign : List ℤ := [1, 1, 1, 1, 1, 1, 1, (-1), 1, (-1), 1, 1, 1, (-1), (-1), 1, (-1), (-1), 1, (-1), (-1), (-1), 1, 1, (-1), 1, 1]
def T2_inv_perm : List ℕ := [0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 17, 18, 15, 16, 13, 14, 11, 12, 21, 22, 19, 20, 25, 26, 23, 24]
def T2_inv_sign : List ℤ := [1, 1, 1, (-1), 1, (-1), 1, 1, 1, 1, 1, (-1), 1, 1, (-1), (-1), (-1), 1, 1, (-1), 1, (-1), (-1), 1, 1, 1, (-1)]
def T3_perm : List ℕ := [0, 1, 2, 9, 10, 7, 8, 5, 6, 3, 4, 13, 14, 11, 12, 17, 18, 15, 16, 23, 24, 25, 26, 19, 20, 21, 22]
def T3_sign : List ℤ := [1, 1, 1, 1, 1, (-1), 1, 1, 1, (-1), 1, (-1), (-1), 1, (-1), 1, 1, (-1), 1, 1, (-1), (-1), 1, 1, 1, (-1), (-1)]
def T3_inv_perm : List ℕ := [0, 1, 2, 9, 10, 7, 8, 5, 6, 3, 4, 13, 14, 11, 12, 17, 18, 15, 16, 23, 24, 25, 26, 19, 20, 21, 22]
def T3_inv_sign : List ℤ := [1, 1, 1, (-1), 1, 1, 1, (-1), 1, 1, 1, 1, (-1), (-1), (-1), (-1), 1, 1, 1, 1, 1, (-1), (-1), 1, (-1), (-1), 1]
def permOfList (l : List ℕ) (k : Fin 27) : Fin 27 := ⟨l.getD k.val 0 % 27, Nat.mod_lt _ (Nat.zero_lt_succ 26)⟩
def sgnOfList (l : List ℤ) (k : Fin 27) : ℤ := l.getD k.val 0
def T1p : Fin 27 → Fin 27 := permOfList T1_perm
def T1pinv : Fin 27 → Fin 27 := permOfList T1_inv_perm
def T1s : Fin 27 → ℤ := sgnOfList T1_sign
def T1si : Fin 27 → ℤ := sgnOfList T1_inv_sign
def T2p : Fin 27 → Fin 27 := permOfList T2_perm
def T2pinv : Fin 27 → Fin 27 := permOfList T2_inv_perm
def T2s : Fin 27 → ℤ := sgnOfList T2_sign
def T2si : Fin 27 → ℤ := sgnOfList T2_inv_sign
def T3p : Fin 27 → Fin 27 := permOfList T3_perm
def T3pinv : Fin 27 → Fin 27 := permOfList T3_inv_perm
def T3s : Fin 27 → ℤ := sgnOfList T3_sign
def T3si : Fin 27 → ℤ := sgnOfList T3_inv_sign
def signedTransport (perm : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) : Glennie.Albert →ₗ[ℝ] Glennie.Albert := upperCoordinateEquiv.symm.toLinearMap ∘ₗ (LinearMap.pi fun k
  => ((sgn k : ℝ)) • LinearMap.proj (perm k)) ∘ₗ upperCoordinateEquiv.toLinearMap
def transportT : Fin 3 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => signedTransport T1p T1s | 1 => signedTransport T2p T2s | 2 => signedTransport T3p T3s
def transportTinv : Fin 3 → Glennie.Albert →ₗ[ℝ] Glennie.Albert
  | 0 => signedTransport T1pinv T1si | 1 => signedTransport T2pinv T2si | 2 => signedTransport T3pinv T3si
def pointRelabel (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 39) := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm.trans
  ((Equiv.prodShear fperm τ).trans (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39))
namespace Anchor0
def anchor0τ (f : Fin 13) : Equiv.Perm (Fin 3) := if f.val < 4 then Equiv.refl _ else Equiv.neg (Fin 3)
def gaugeL (ξ : Fin 4 → ℂ) : Mat := Matrix.of fun i j => if i + j = 2 then (if j = 0 then 1 else if j = 1 then -(ξ 3)⁻¹ else ξ 2) else 0
def gaugeR (ξ : Fin 4 → ℂ) : Mat := Matrix.diagonal fun j => if j = 0 then 1 else if j = 1 then ξ 3 else (ξ 2)⁻¹
def gaugeC (l : Label) : ℂ := χ (l.1 * l.2)
def gaugeσ : Label ≃ Label where
  toFun l := (-l.2, -l.1); invFun l := (-l.2, -l.1); left_inv l := (by simp); right_inv l := by simp
end Anchor0
namespace Anchor1
def asMat (M : TitsComplexMatrix) : Mat := M
def fperm1 : Equiv.Perm (Fin 13) := Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 3 6
def tau1 (F : Fin 13) : Equiv.Perm (Fin 3) := if F.val = 0 then Equiv.refl _ else if F.val < 7 then Equiv.neg PhaseIndex
  else if F.val < 10 then Equiv.subRight (((F.val - 7 : ℕ)) : PhaseIndex) else Equiv.subLeft (((F.val - 10 : ℕ)) : PhaseIndex)
def Lg (ξ : Fin 4 → ℂ) : TitsComplexMatrix := !![0, 0, -(ξ 0)⁻¹; 0, ξ 1, 0; -1, 0, 0]
def Rg (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal ![-1, -(ξ 1)⁻¹, -(ξ 0)]
def sigma1 : Label ≃ Label where
  toFun p := if p.1 = 2 then (-p.2, 2) else (p.2, p.1); invFun p := if p.2 = 2 then (2, -p.1) else (p.2, p.1); left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide
end Anchor1
namespace Anchor2
def fperm2 : Equiv.Perm (Fin 13) where
  toFun := ![0, 7, 9, 8, 1, 10, 4, 3, 12, 5, 2, 11, 6]; invFun := ![0, 4, 10, 7, 6, 9, 12, 1, 3, 2, 5, 11, 8]; left_inv := (by decide); right_inv := by decide
def τ2 (f : Fin 13) : Equiv.Perm (Fin 3) := if f.val = 5 ∨ f.val = 8 ∨ f.val = 11 then Equiv.neg (Fin 3) else Equiv.refl _
def gaugeLv (ξ : Fin 4 → ℂ) (j : Index) : ℂ := if j = 0 then 1 else if j = 1 then -(ξ 2)⁻¹ else (ξ 2 * ξ 3)⁻¹
def gaugeL (ξ : Fin 4 → ℂ) : Mat := Matrix.of fun i j => if i + j = 0 then -gaugeLv ξ j else 0
def gaugeRv (ξ : Fin 4 → ℂ) (j : Index) : ℂ := if j = 0 then -1 else if j = 1 then -ξ 2 else -(ξ 2 * ξ 3)
def gaugeR (ξ : Fin 4 → ℂ) : Mat := Matrix.diagonal (gaugeRv ξ)
def gaugeC (l : Label) : ℂ := χ (l.1 * l.2 - l.1)
end Anchor2
namespace Anchor3
def fperm3 : Equiv.Perm (Fin 13) where
  toFun := ![0, 10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8, 9]; invFun := ![0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 2, 3]; left_inv := by intro f; revert f; decide
  right_inv := by intro f; revert f; decide
def τ3 (f : Fin 13) : Equiv.Perm (Fin 3) := if f.val = 0 ∨ (7 ≤ f.val ∧ f.val ≤ 9) then Equiv.refl _ else Equiv.neg (Fin 3)
def gaugeL3 : Mat := Matrix.of fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 2) then -1 else 0
def gaugeC3 (l : Label) : ℂ := if l.1 = 0 then χ l.2 else if l.1 = 1 then χ (-l.2) else 1
def gaugeσ3 : Label ≃ Label where
  toFun l := (if l.1 = 2 then -l.2 else l.2, l.1); invFun m := (m.2, if m.2 = 2 then -m.1 else m.1); left_inv := by intro l; revert l; decide
  right_inv := by intro m; revert m; decide
end Anchor3
def anchorΨ : Fin 4 → Glennie.Albert →ₗ[ℝ] Glennie.Albert := CKM.NativeFirstOrder.selectFour (LinearMap.id) (transportTinv 0) (transportTinv 1) (transportTinv 2)
def anchorΨinv : Fin 4 → Glennie.Albert →ₗ[ℝ] Glennie.Albert := CKM.NativeFirstOrder.selectFour (LinearMap.id) (transportT 0) (transportT 1) (transportT 2)
def anchorRelabel : Fin 4 → Equiv.Perm (Fin 39) := CKM.NativeFirstOrder.selectFour (pointRelabel (Equiv.refl _) Anchor0.anchor0τ) (pointRelabel Anchor1.fperm1 Anchor1.tau1) (pointRelabel Anchor2.fperm2 Anchor2.τ2) (pointRelabel Anchor3.fperm3 Anchor3.τ3)
def gaugeLeft (ξ : Fin 4 → ℂ) : Fin 4 → Mat := CKM.NativeFirstOrder.selectFour (Anchor0.gaugeL ξ) (Anchor1.asMat (Anchor1.Lg ξ)) (Anchor2.gaugeL ξ) (Anchor3.gaugeL3)
def gaugeRight (ξ : Fin 4 → ℂ) : Fin 4 → Mat := CKM.NativeFirstOrder.selectFour (Anchor0.gaugeR ξ) (Anchor1.asMat (Anchor1.Rg ξ)) (Anchor2.gaugeR ξ) (1)
def gaugeScalar : Fin 4 → Label → ℂ := CKM.NativeFirstOrder.selectFour (Anchor0.gaugeC) (fun _ => 1) (Anchor2.gaugeC) (Anchor3.gaugeC3)
def gaugeLabel : Fin 4 → Label ≃ Label := CKM.NativeFirstOrder.selectFour (Anchor0.gaugeσ) (Anchor1.sigma1) (Equiv.refl _) (Anchor3.gaugeσ3)
open Glennie NativePolynomial CompactAlbert UnitaryErrorBases.ComplexQuartet
open scoped Matrix
abbrev Family := Label → Mat
abbrev PhaseTriple := Option2StatementA3Matrix.PhaseTriple
local notation "character" => UnitaryErrorBases.ThreeCycleFourier.character
abbrev ComplexMatrix3 := TitsComplexMatrix
abbrev HermitianTitsPair := {a : TitsComplexMatrix // a.IsHermitian} × TitsComplexMatrix
def fromHermitianPair (p : HermitianTitsPair) : TitsCoordinates := (![(p.1.val 0 0).re, (p.1.val 1 1).re, (p.1.val 2 2).re], ![p.1.val 1 2, p.1.val 2 0, p.1.val 0 1],
  p.2)
def includeHermitianMatrix (P : {a : TitsComplexMatrix // a.IsHermitian}) : Glennie.Albert := fromTitsCoordinates (fromHermitianPair (P, 0))
def coordinateProjector (t : Fin 3) : ComplexMatrix3 := Matrix.diagonal (fun j => if j = t then 1 else 0)
def phaseRay (s t : PhaseIndex) : Fin 3 → ℂ := ![1, character t, character (s - t)]
def phaseProjector (s t : PhaseIndex) : ComplexMatrix3 := (1 / 3 : ℂ) • Matrix.vecMulVec (phaseRay s t) (star (phaseRay s t))
theorem coordinateProjector_isHermitian (t : Fin 3) : (coordinateProjector t).IsHermitian := by
  apply Matrix.IsHermitian.ext; intro row column; fin_cases t <;> fin_cases row <;> fin_cases column <;>
    norm_num [coordinateProjector, Matrix.diagonal_apply]
theorem phaseProjector_isHermitian (s t : PhaseIndex) : (phaseProjector s t).IsHermitian := by
  change (phaseProjector s t).conjTranspose = phaseProjector s t; simp [phaseProjector, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
def stdQuartet : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}
  | 0, t => ⟨coordinateProjector t, coordinateProjector_isHermitian t⟩
  | ⟨k + 1, _⟩, t => ⟨phaseProjector (k : PhaseIndex) (t : PhaseIndex), phaseProjector_isHermitian _ _⟩
namespace Anchor1
def gQ : TitsComplexMatrix := Matrix.diagonal ![1, -1, -1]
def q1 (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} := ⟨gQ * (stdQuartet k t).val * gQ.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose
  gQ (stdQuartet k t).property⟩
end Anchor1
namespace Anchor2
def g2 (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal ![1, ξ 0, (ξ 1)⁻¹]
def q2 (ξ : Fin 4 → ℂ) (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} := ⟨g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose,
  Matrix.isHermitian_mul_mul_conjTranspose _ (stdQuartet k t).property⟩
end Anchor2
namespace Anchor3
def gD (ξ : Fin 4 → ℂ) : Fin 3 → ℂ := ![1, (ξ 2)⁻¹, -ξ 3]
def g3 (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal (gD ξ)
def q3 (ξ : Fin 4 → ℂ) (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} := ⟨g3 ξ * (stdQuartet k t).val * (g3 ξ).conjTranspose,
  Matrix.isHermitian_mul_mul_conjTranspose _ (stdQuartet k t).property⟩
end Anchor3
def anchorQuartet (ξ : Fin 4 → ℂ) : Fin 4 → Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian} := CKM.NativeFirstOrder.selectFour (stdQuartet) (Anchor1.q1) (Anchor2.q2 ξ) (Anchor3.q3 ξ)
def quartetConj (ξ : Fin 4 → ℂ) : Fin 4 → TitsComplexMatrix := CKM.NativeFirstOrder.selectFour (1) (Anchor1.gQ) (Anchor2.g2 ξ) (Anchor3.g3 ξ)
def hiddenFrameEquiv : Label ≃ Fin 9 := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9)
def stdAnchored (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}) (W : Family) (i : Fin 39) : Glennie.Albert := if h : i.val < 12 then
    includeHermitianMatrix (q ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩) else nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (i.val % 3)) •
        W (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩))
def hidFamily (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) : Family := fun l => gaugeScalar H l • (g * gaugeLeft ξ₀ H *
  Option2StatementA3Matrix.monomialFamily d (gaugeLabel H l) * gaugeRight ξ₀ H * hᴴ)
def prePoint (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) (i : Fin 39) : Glennie.Albert := anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀
  H g h d) ((anchorRelabel H).symm i))
def preCfg (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) : CKM.NativeTightCode.CodeCoords := fun i => NativePolynomial.upperCoordinates (prePoint ξ₀ H g
  h d i)
open CKM.NativeFirstOrder Option2StatementA5
open scoped BigOperators
def anchorPhases_isPhaseTriple (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (∀ j, Complex.normSq (anchorPhases ξ H j) = 1) ∧ ∏ j, anchorPhases ξ H j = 1 := by
  have h0 : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have h1 : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have h2 : ξ 2 ≠ 0 := fun h => by simpa [h] using hξ 2
  have h3 : ξ 3 ≠ 0 := fun h => by simpa [h] using hξ 3
  have n0 := hξ 0; have n1 := hξ 1; have n2 := hξ 2; have n3 := hξ 3
  have hprod : ∀ d : UnitaryErrorBases.Index → ℂ, ∏ j, d j = d 0 * d 1 * d 2 := fun d =>
    Fin.prod_univ_three d
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases H <;> fin_cases j <;>
      simp [anchorPhases, map_mul, map_div₀, map_inv₀, Complex.normSq_neg, n0, n1, n2, n3]
  · rw [hprod]
    fin_cases H <;> simp [anchorPhases] <;> field_simp
def anchorTriple (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) : PhaseTriple := ⟨anchorPhases ξ H, anchorPhases_isPhaseTriple ξ hξ H⟩
def torusAngles (e : Fin 2 → ℝ) : Index → ℝ := ![e 0, e 1, -(e 0) - e 1]
def torusPhase (d₀ : PhaseTriple) (e : Fin 2 → ℝ) : PhaseTriple := ⟨fun j => d₀.val j * Complex.exp ((torusAngles e j : ℂ) * Complex.I), by
    refine ⟨fun j => ?_, ?_⟩
    · rw [map_mul, d₀.2.1 j, one_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I,
        one_pow]
    · rw [Finset.prod_mul_distrib, d₀.2.2, one_mul, ← Complex.exp_sum, ← Finset.sum_mul]
      have : ∑ j : Index, (torusAngles e j : ℂ) = 0 := by exact (Fin.sum_univ_three (fun j : Fin 3 => (torusAngles e j : ℂ))).trans (by simp [torusAngles])
      rw [this, zero_mul, Complex.exp_zero]⟩
abbrev PreParam := (Fin 8 → ℝ) × (Fin 8 → ℝ) × (Fin 2 → ℝ)
def preMap (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) : CKM.NativeTightCode.CodeCoords := preCfg ξ₀ H (suExp p.1) (suExp p.2.1) (torusPhase
  (anchorTriple ξ₀ hξ₀ H) p.2.2)
end Option2StatementA5Anchor
namespace Option2StatementA5Raw
open Glennie NativePolynomial CKM.NativeFirstOrder Option2StatementA5Anchor Option2StatementA5 ContinuousLinearMap
abbrev Coord := Fin 27 → ℝ
abbrev Cfg := CKM.NativeTightCode.CodeCoords
abbrev CEnd := Coord →L[ℝ] Coord
abbrev Product := Coord →L[ℝ] Coord →L[ℝ] Coord
def NativeProduct (m : Product) : Prop := ∀ x y, m x y = upperCoordinates (jordan (fromUpperCoordinates x) (fromUpperCoordinates y))
def IsDerivationOf (m : Product) (D : CEnd) : Prop := ∀ a b, D (m a b) = m (D a) b + m a (D b)
def derOf (m : Coord →L[ℝ] Coord →L[ℝ] Coord) : Submodule ℝ (Coord →L[ℝ] Coord) where
  carrier := {D | IsDerivationOf m D}; add_mem' := by
    intro D E hD hE a b; have h1 : D (m a b) = m (D a) b + m a (D b) := hD a b; have h2 : E (m a b) = m (E a) b + m a (E b) := hE a b
    simp only [add_apply, h1, h2, map_add]; abel
  zero_mem' := by intro a b; simp
  smul_mem' := by intro c D hD a b; have h1 : D (m a b) = m (D a) b + m a (D b) := hD a b; simp only [smul_apply, h1, map_smul, smul_add]
def groupChart (m : Product) (D : derOf m) : CEnd := NormedSpace.exp (D : CEnd)
def act (A : CEnd) (C : Cfg) : Cfg := fun i => A (C i)
abbrev RawParam (m : Product) := ↥(derOf m) × PreParam
abbrev RawParam62 (m : Product) := ↥(derOf m) × (Fin 8 → ℝ) × (Fin 2 → ℝ)
abbrev CommonParam (m : Product) := ↥(derOf m) × (Fin 4 → ℝ)
def rawMap (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (p : RawParam m) : Cfg := act (groupChart m p.1) (preMap ξ hξ H p.2)
def rawMap62 (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (p : RawParam62 m) : Cfg := rawMap m ξ hξ H (p.1, p.2.1, 0, p.2.2)
def commonMap (m : Product) (ξ : Fin 4 → ℂ) (p : CommonParam m) : Cfg := act (groupChart m p.1) (CKM.NativeFirstOrder.literalCfg (commonPhase ξ p.2))
end Option2StatementA5Raw
namespace Option2StatementA5Slice
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5
open scoped BigOperators
def orbitMap (ξ : Fin 4 → ℂ) : CEnd →ₗ[ℝ] Cfg where
  toFun A := fun i => A (literalCfg ξ i); map_add' _ _ := rfl; map_smul' _ _ := rfl
def orbit (m : Product) (ξ : Fin 4 → ℂ) : Submodule ℝ Cfg := (derOf m).map (orbitMap ξ)
def coordinateWeight (k : Fin 27) : ℤ := if k.val < 3 then 1 else 2
def cfgPairing (C D : Cfg) : ℝ := ∑ i, ∑ k, (coordinateWeight k : ℝ) * C i k * D i k
def normal (m : Product) (ξ : Fin 4 → ℂ) : Submodule ℝ Cfg where
  carrier := {n | ∀ u ∈ orbit m ξ, cfgPairing u n = 0}; zero_mem' := (by intro u _; simp [cfgPairing]); add_mem' := by
    intro a b ha hb u hu; simp only [cfgPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib] at *; rw [ha u hu, hb u hu, add_zero]
  smul_mem' := by
    intro c a ha u hu; change (∑ i, ∑ k, (coordinateWeight k : ℝ) * u i k * (c * a i k)) = 0; simp_rw [show ∀ i k, (coordinateWeight k : ℝ) * u i k * (c * a i k) =
      c * ((coordinateWeight k : ℝ) * u i k * a i k) by intros; ring]
    simp_rw [← Finset.mul_sum]; exact mul_eq_zero_of_right c (ha u hu)
def sliceChart (m : Product) (ξ : Fin 4 → ℂ) (p : derOf m × normal m ξ) : Cfg := Option2StatementA5Raw.act (groupChart m p.1) (literalCfg ξ + p.2)
abbrev SliceParam := (Fin 8 → ℝ) × (Fin 2 → ℝ)
def sliceRep {m : Product} {ξ : Fin 4 → ℂ} (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) (y : Cfg) : normal m ξ := (σ.symm y).2
def sliceFam {m : Product} {ξ : Fin 4 → ℂ} (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) (hξ : IsUnitPhase ξ) (H : Fin 4) (p : SliceParam) : normal m ξ :=
  sliceRep σ (preMap ξ hξ H (p.1, 0, p.2))
def sliceCommon {m : Product} {ξ : Fin 4 → ℂ} (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) (θ : Fin 4 → ℝ) : normal m ξ := sliceRep σ (literalCfg
  (commonPhase ξ θ))
def sliceUnion {m : Product} {ξ : Fin 4 → ℂ} (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) (hξ : IsUnitPhase ξ) (V : Fin 4 → Set SliceParam) : Set Cfg := ⋃
  i, (fun p => literalCfg ξ + (sliceFam σ hξ i p : Cfg)) '' V i
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5 Filter Topology
def Simultaneous (m : Product) (ξ₀ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ₀) (σ : OpenPartialHomeomorph (derOf m × normal m ξ₀) Cfg) : Prop := (∃ Φ : OpenPartialHomeomorph
  SliceModel ↥(normal m ξ₀), (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧ AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧ IsGermImage (Φ '' (Φ.source ∩
  commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))) 0 (sliceCommon σ) 0 ∧ (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 →
  ℝ) H)) 0 (sliceFam σ hξ H) 0) ∧ (∀ H H', H ≠ H' → Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩ Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ)
  (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))) ∧ (∃ Φ : OpenPartialHomeomorph RawModel Cfg, (0 : RawModel) ∈ Φ.source ∧ Φ 0 =
            literalCfg ξ₀ ∧ AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧ IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ)
            (Fin 973 → ℝ))) (literalCfg ξ₀) (commonMap m ξ₀) 0 ∧ (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
            (literalCfg ξ₀) (rawMap62 m ξ₀ hξ H) 0) ∧ (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H)) (literalCfg ξ₀)
            (rawMap m ξ₀ hξ H) 0) ∧ (∀ H H', H ≠ H' → Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩ Φ '' (Φ.source ∩ familyBlock (Fin 56 →
            ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') = Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))))
def GermCut (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) : Prop := (∃ V₀ ∈ 𝓝 (0 : CommonParam m), ∀ U₀ ∈
  𝓝 (0 : CommonParam m), U₀ ⊆ V₀ → IsGermImage (commonMap m ξ '' U₀ ∩ {y | y - literalCfg ξ ∈ normal m ξ}) (literalCfg ξ) (fun θ => literalCfg ξ + ↑(sliceCommon σ θ))
  0) ∧ ∀ H, ∃ V₀ ∈ 𝓝 (0 : RawParam62 m), ∀ U₀ ∈ 𝓝 (0 : RawParam62 m), U₀ ⊆ V₀ → IsGermImage (rawMap62 m ξ hξ H '' U₀ ∩ {y | y - literalCfg ξ ∈ normal m ξ})
  (literalCfg ξ) (fun p => literalCfg ξ + ↑(sliceFam σ hξ H p)) 0
def GermDescent (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) : Prop := (∃ U₀ ∈ 𝓝 (0 : CommonParam m), ∃
  V₀ ∈ 𝓝 (0 : Fin 4 → ℝ), ∀ᶠ y in 𝓝 (literalCfg ξ), y ∈ commonMap m ξ '' U₀ ↔ y ∈ saturation ((fun θ => literalCfg ξ + ↑(sliceCommon σ θ)) '' V₀)) ∧ ∀ H, ∃ U₀ ∈ 𝓝 (0
  : RawParam62 m), ∃ V₀ ∈ 𝓝 (0 : SliceParam), ∀ᶠ y in 𝓝 (literalCfg ξ), y ∈ rawMap62 m ξ hξ H '' U₀ ↔ y ∈ saturation ((fun p => literalCfg ξ + ↑(sliceFam σ hξ H p))
  '' V₀)
def LabelledSlice (m : Product) (ξ : Fin 4 → ℂ) : Prop := ∃ r : Setoid {C : Cfg // Option2StatementResidual.originalF C = 0}, (∀ C D, r C D ↔ D.val ∈ saturation
  {C.val}) ∧ ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ Topology.IsOpenEmbedding (fun C : {C : {C : Cfg // Option2StatementResidual.originalF C = 0} // C.val ∈ W ∧
  C.val - literalCfg ξ ∈ normal m ξ} => Quotient.mk r C.val)
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5 Filter Topology
end Option2StatementA5Slice
open scoped BigOperators
namespace Option2StatementA4
abbrev PosRoot := {p : Fin 4 × Fin 4 × Bool // p.1 < p.2.1}
namespace PosRoot
abbrev r (α : PosRoot) : Fin 4 := α.1.1
abbrev s (α : PosRoot) : Fin 4 := α.1.2.1
abbrev plus (α : PosRoot) : Bool := α.1.2.2
def weight (α : PosRoot) : Fin 4 → ℤ := fun q => (if q = α.r then 1 else 0) + (if q = α.s then (if α.plus then 1 else -1) else 0)
end PosRoot
def betaWeight : Fin 4 → Fin 4 → ℤ := ![![0, -1, 0, 1], ![1, 1, 0, 0], ![1, 0, -1, 0], ![0, 0, 1, -1]]
def rootLattice : AddSubgroup (Fin 4 → ℤ) where
  carrier := {v | Even (∑ i, v i)}; zero_mem' := (by simp); add_mem' := by
    intro a b ha hb; simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *; exact ha.add hb
  neg_mem' := by intro a ha; simp only [Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib] at *; exact ha.neg
def betaCoord (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  let h := (∑ i, v i) / 2
  ![h - v 1, h, h - v 1 - v 2 - v 3, h - v 1 - v 3]
def betaValue (ξ : Fin 4 → ℂ) : Fin 4 → ℂ := ![-(ξ 0 ^ 3), -(ξ 1 ^ 3), ξ 2 ^ 3, -(ξ 3 ^ 3)]
def adjointTorus (ξ : Fin 4 → ℂ) (v : Fin 4 → ℤ) : ℂ := ∏ i, betaValue ξ i ^ betaCoord v i
def rowRoot : Fin 4 → Fin 3 → PosRoot × Bool := ![![(⟨(2, 3, true), by decide⟩, false), (⟨(1, 2, false), by decide⟩, false), (⟨(1, 3, true), by decide⟩, true)],
    ![(⟨(0, 1, false), by decide⟩, false), (⟨(1, 2, true), by decide⟩, false), (⟨(0, 2, true), by decide⟩, true)],
    ![(⟨(0, 3, false), by decide⟩, false), (⟨(0, 2, false), by decide⟩, true), (⟨(2, 3, false), by decide⟩, true)],
    ![(⟨(1, 3, false), by decide⟩, false), (⟨(0, 1, true), by decide⟩, true), (⟨(0, 3, true), by decide⟩, false)]]
def rowWeight (H : Fin 4) (j : Fin 3) : Fin 4 → ℤ := if (rowRoot H j).2 then -(rowRoot H j).1.weight else (rowRoot H j).1.weight
def kChar : Fin 4 → ZMod 3 × ZMod 3 := ![(0, 2), (1, 0), (2, 1), (1, 1)]
end Option2StatementA4
set_option backward.isDefEq.respectTransparency false
namespace Option2StatementA4
open Glennie NativePolynomial CompactAlbert CKM.NativeFirstOrder
open scoped BigOperators
abbrev End := Module.End ℝ Albert
abbrev OEnd := Module.End ℝ Octonion
abbrev Cfg := Fin 39 → Fin 27 → ℝ
def dot (x y : Octonion) : ℝ := octRe (octMul x (octConj y))
def basis (j : Fin 8) : Octonion :=
  let v : Fin 8 → ℝ := Pi.single j 1
  (⟨v 0,v 1,v 2,v 3⟩,⟨v 4,v 5,v 6,v 7⟩)
def pf (r : Fin 4) : Fin 8 := ⟨2*r.val, by omega⟩
def ps (r : Fin 4) : Fin 8 := ⟨2*r.val+1, by omega⟩
def wedgeFn (u v x : Octonion) : Octonion := dot v x • u - dot u x • v
def rootXFn (α : PosRoot) (x : Octonion) : Octonion := if α.plus then wedgeFn (basis (pf α.r)) (basis (pf α.s)) x - wedgeFn (basis (ps α.r)) (basis (ps α.s)) x else
  wedgeFn (basis (pf α.r)) (basis (pf α.s)) x + wedgeFn (basis (ps α.r)) (basis (ps α.s)) x
def rootYFn (α : PosRoot) (x : Octonion) : Octonion := if α.plus then wedgeFn (basis (pf α.r)) (basis (ps α.s)) x + wedgeFn (basis (ps α.r)) (basis (pf α.s)) x else
  wedgeFn (basis (ps α.r)) (basis (pf α.s)) x - wedgeFn (basis (pf α.r)) (basis (ps α.s)) x
def slot (a : Octonion) : Albert := ⟨0,0,0,0,0,a⟩
def rootEvaluation (α : PosRoot) (D : End) : ℝ := ∑ q, (α.weight q : ℝ) * dot (basis (ps q)) (D (slot (basis (pf q)))).o12
def rotate (z : Fin 4 → ℂ) (x : Octonion) : Octonion := (⟨(z 0).re*x.1.re-(z 0).im*x.1.imI, (z 0).im*x.1.re+(z 0).re*x.1.imI, (z 1).re*x.1.imJ-(z 1).im*x.1.imK, (z
  1).im*x.1.imJ+(z 1).re*x.1.imK⟩, ⟨(z 2).re*x.2.re-(z 2).im*x.2.imI, (z 2).im*x.2.re+(z 2).re*x.2.imI, (z 3).re*x.2.imJ-(z 3).im*x.2.imK, (z 3).im*x.2.imJ+(z
  3).re*x.2.imK⟩)
def liftSq (ξ : Fin 4 → ℂ) : ℂ := -((ξ 0*ξ 1*ξ 2*ξ 3)^3)
def liftEig (ξ : Fin 4 → ℂ) (l : ℂ) : Fin 4 → ℂ := ![l, -(ξ 1^3)/l, l/ξ 2^3, -l/(ξ 2^3*ξ 3^3)]
def subgroupGen (a b : End) : Fin 4 → End := ![a,b,a^2*b^2,a^2*b]
def shift (g : Fin 2) (f : Fin 13) : Fin 3 := if g=0 then (if f.val<4 then 0 else 1) else if f.val=0 then 0 else if f.val<4 then 1 else if f.val<7 then 0 else if
  f.val<10 then 2 else 1
def shifted (g : Fin 2) (i : Fin 39) : Fin 39 :=
  let f : Fin 13 := ⟨i.val/3, by omega⟩
  let k : Fin 3 := ⟨i.val%3, Nat.mod_lt _ (by decide)⟩
  ⟨3*f.val+(k+shift g f).val, by have := (k+shift g f).isLt; omega⟩
def fixed {V : Type*} [AddCommMonoid V] [Module ℝ V] (g : Module.End ℝ V) : Submodule ℝ V := LinearMap.eqLocus g 1
def gen {V : Type*} [AddCommMonoid V] [Module ℝ V] (a b : Module.End ℝ V) : Fin 4 → Module.End ℝ V := ![a,b,a^2*b^2,a^2*b]
def eqv {V W : Type*} [AddCommMonoid V] [Module ℝ V] [AddCommMonoid W] [Module ℝ W] (a b : Module.End ℝ V) (c d : Module.End ℝ W) : Prop := ∃ e : V ≃ₗ[ℝ] W, (∀v,e (a
  v)=c (e v)) ∧ (∀v,e (b v)=d (e v))
abbrev Std (m : ℕ) (n : Fin 4 → ℕ) := (Fin m → ℝ) × ((H : Fin 4) → Fin (n H) → ℂ)
def stdGen (g : Fin 2) (m : ℕ) (n : Fin 4 → ℕ) : Module.End ℝ (Std m n) := LinearMap.prodMap LinearMap.id (LinearMap.pi fun H => LinearMap.pi fun i =>
  LinearMap.mulLeft ℝ (UnitaryErrorBases.ThreeCycleFourier.omega ^ (if g=0 then (kChar H).1.val else (kChar H).2.val)) ∘ₗ (LinearMap.proj i ∘ₗ LinearMap.proj (φ:=fun
  H=>Fin (n H)→ℂ) H))
def hexagon (H : Fin 4) : Set PosRoot := {α | ∃j,(rowRoot H j).1=α}
def peirceChar : Fin 4 → ZMod 3 × ZMod 3 := ![(0,1),(2,1),(2,2),(1,0)]
def weightChar (w : Fin 4 → ℤ) : ZMod 3 × ZMod 3 := ∑q,w q • peirceChar q
def h0Weight : Fin 3 → Fin 4 → ℤ := ![![0,1,0,0],![0,0,1,0],![0,0,0,-1]]
def resonance (ξ : Fin 4 → ℂ) (H : Fin 4) : ℕ := by classical exact Fintype.card {j : UnitaryErrorBases.Index // anchorPhases ξ H j ^3=1}
structure Data where
  (der : Submodule ℝ End) (s : Submodule ℝ End) (t : Submodule ℝ End) (skew : Submodule ℝ OEnd) (r0 : End) (r1 : End) (ψ : s ≃ₗ[ℝ] skew) (x : PosRoot → s)
  (y : PosRoot → s) (pointwise : Fin 4 → Submodule ℝ End) (s0 : Module.End ℝ s) (s1 : Module.End ℝ s) (tin : Submodule ℝ s) (sq0 : Module.End ℝ (s ⧸ tin))
  (sq1 : Module.End ℝ (s ⧸ tin))
structure Pinned (d : Data) : Prop where
  r0_jordan : ∀ x y, d.r0 (jordan x y) = jordan (d.r0 x) (d.r0 y)
  r1_jordan : ∀ x y, d.r1 (jordan x y) = jordan (d.r1 x) (d.r1 y)
  r0_trace : ∀ x, trace (d.r0 x) = trace x
  r1_trace : ∀ x, trace (d.r1 x) = trace x
  r0_cube : d.r0 ^ 3 = 1
  r1_cube : d.r1 ^ 3 = 1
  commute : d.r0 * d.r1 = d.r1 * d.r0
  (der : ∀D,D∈d.der ↔ ∀x y,D (jordan x y)=jordan (D x) y+jordan x (D y)) (s : ∀D,D∈d.s ↔ D∈d.der ∧ ∀i:Fin 3,D (literalNativeCoordinatePoint i)=0)
  (t : ∀D,D∈d.t ↔ D∈d.der ∧ d.r0*D=D*d.r0 ∧ d.r1*D=D*d.r1) (skew : ∀A,A∈d.skew ↔ ∀x y,dot (A x) y + dot x (A y)=0)
  (r0 : ∀x, (hermitianMatrix (toTitsCoordinates (d.r0 x)),(toTitsCoordinates (d.r0 x)).2.2)= (hermitianMatrix (toTitsCoordinates x),(toTitsCoordinates x).2.2 * (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix))))
  (r1 : d.r1=Option2StatementA5Anchor.transportT 0 ∘ₗ d.r0 ∘ₗ Option2StatementA5Anchor.transportTinv 0)
  (psi : ∀D a, ((d.ψ D : d.skew) : OEnd) a = (((D:d.s):End) (slot a)).o12) (rootsX : ∀α a, ((d.ψ (d.x α):d.skew):OEnd) a=rootXFn α a)
  (rootsY : ∀α a, ((d.ψ (d.y α):d.skew):OEnd) a=rootYFn α a) (pointwise : ∀H D,D∈d.pointwise H ↔ D∈d.der ∧ ∀x,subgroupGen d.r0 d.r1 H x=x → D x=0)
  (s0 : ∀D, (d.s0 D:End)=d.r0*(D:End)*d.r0^2) (s1 : ∀D, (d.s1 D:End)=d.r1*(D:End)*d.r1^2) (tin : ∀D,D∈d.tin ↔ (D:End)∈d.t)
  (sq0 : ∀D,d.sq0 (Submodule.Quotient.mk D)=Submodule.Quotient.mk (d.s0 D)) (sq1 : ∀D,d.sq1 (Submodule.Quotient.mk D)=Submodule.Quotient.mk (d.s1 D))
structure PhaseData (d : Data) (ξ : Fin 4 → ℂ) where
  (tangent : Submodule ℝ Cfg) (orbit : Submodule ℝ Cfg) (ev : End →ₗ[ℝ] Cfg) (orbitIn : Submodule ℝ tangent) (a0 : Module.End ℝ tangent) (a1 : Module.End ℝ tangent)
  (o0 : Module.End ℝ orbitIn) (o1 : Module.End ℝ orbitIn) (q0 : Module.End ℝ (tangent ⧸ orbitIn)) (q1 : Module.End ℝ (tangent ⧸ orbitIn)) (ad : d.s ≃ₗ[ℝ] d.s)
  (z : Submodule ℝ d.s) (z0 : Module.End ℝ z) (z1 : Module.End ℝ z)
structure PhasePinned (d : Data) (ξ : Fin 4 → ℂ) (p : PhaseData d ξ) : Prop where
  base_zero : Option2StatementResidual.originalF (literalCfg ξ) = 0
  base0 : ∀ i, d.r0 (literalPoint ξ (shifted 0 i)) = literalPoint ξ i
  base1 : ∀ i, d.r1 (literalPoint ξ (shifted 1 i)) = literalPoint ξ i
  (tangent : p.tangent=LinearMap.ker (fderiv ℝ Option2StatementResidual.originalF (literalCfg ξ)).toLinearMap)
  (ev : ∀D i,p.ev D i=upperCoordinates (D (literalPoint ξ i))) (orbit : p.orbit=d.der.map p.ev) (orbitIn : ∀v,v∈p.orbitIn ↔ (v:Cfg)∈p.orbit)
  (a0 : ∀v i,(p.a0 v:Cfg) i=upperCoordinates (d.r0 (fromUpperCoordinates ((v:Cfg) (shifted 0 i)))))
  (a1 : ∀v i,(p.a1 v:Cfg) i=upperCoordinates (d.r1 (fromUpperCoordinates ((v:Cfg) (shifted 1 i))))) (o0 : ∀v,(p.o0 v:p.tangent)=p.a0 (v:p.tangent))
  (o1 : ∀v,(p.o1 v:p.tangent)=p.a1 (v:p.tangent)) (q0 : ∀v,p.q0 (Submodule.Quotient.mk v)=Submodule.Quotient.mk (p.a0 v))
  (q1 : ∀v,p.q1 (Submodule.Quotient.mk v)=Submodule.Quotient.mk (p.a1 v))
  (ad : ∀l,l^2=liftSq ξ → ∀D a, ((d.ψ (p.ad D):d.skew):OEnd) a= rotate (liftEig ξ l) (((d.ψ D:d.skew):OEnd) (rotate (star (liftEig ξ l)) a)))
  (z : ∀D,D∈p.z ↔ p.ad D=D) (z0 : ∀D,(p.z0 D:d.s)=d.s0 (D:d.s)) (z1 : ∀D,(p.z1 D:d.s)=d.s1 (D:d.s))
structure Conclusions (d : Data) (ξ : Fin 4 → ℂ) (p : PhaseData d ξ) : Prop where
  main : eqv (W := (d.s ⧸ d.tin) × p.z) p.q0 p.q1 (LinearMap.prodMap d.sq0 p.z0) (LinearMap.prodMap d.sq1 p.z1)
  tangentModel : eqv p.q0 p.q1 (stdGen 0 4 (fun H=>3+resonance ξ H)) (stdGen 1 4 (fun H=>3+resonance ξ H))
  quotientModel : eqv d.sq0 d.sq1 (stdGen 0 0 (fun _=>3)) (stdGen 1 0 (fun _=>3))
  centralizerModel : eqv p.z0 p.z1 (stdGen 0 4 (resonance ξ)) (stdGen 1 4 (resonance ξ))
  orbit_le : p.orbit≤p.tangent
  ev_injective : Function.Injective p.ev
  orbit_dim : Module.finrank ℝ p.orbit=52
  orbit_H : ∀H,Module.finrank ℝ (fixed (gen p.o0 p.o1 H))=16
  orbit_K : Module.finrank ℝ ↥(fixed p.o0 ⊓ fixed p.o1)=4
  cartan_le : d.t≤d.s
  cartan_abelian : ∀D∈d.t,∀E∈d.t,D*E=E*D
  cartan_selfCentralizing : ∀D∈d.s,(∀E∈d.t,D*E=E*D)→D∈d.t
  cartan_dim : Module.finrank ℝ d.t=4
  bracketX : ∀α,∀h∈d.t,h*(d.x α:End)-(d.x α:End)*h=rootEvaluation α h • (d.y α:End)
  bracketY : ∀α,∀h∈d.t,h*(d.y α:End)-(d.y α:End)*h= -(rootEvaluation α h • (d.x α:End))
  liftIndependent : ∀l l',l^2=liftSq ξ → l'^2=liftSq ξ → ∀B:OEnd,∀a, rotate (liftEig ξ l) (B (rotate (star (liftEig ξ l)) a))=rotate (liftEig ξ l') (B (rotate (star
    (liftEig ξ l')) a))
  rootAction : ∀α,p.ad (d.x α)=(adjointTorus ξ α.weight).re • d.x α+(adjointTorus ξ α.weight).im • d.y α
  beta : ∀i,adjointTorus ξ (betaWeight i)=betaValue ξ i
  rows : ∀H j,adjointTorus ξ (rowWeight H j)=anchorPhases ξ H j ^3
  characters : ∀H j,weightChar (rowWeight H j)=kChar H
  cover : ∀α,∃H,α∈hexagon H
  disjoint : ∀H H',H≠H'→∀α,¬(α∈hexagon H ∧ α∈hexagon H')
  centralizerRoots : ∀α,(d.x α∈p.z ∧ d.y α∈p.z)↔adjointTorus ξ α.weight=1
  centralizerCartan : d.tin≤p.z
  factorRoots : ∀H α,α∈hexagon H → (d.x α:End)∈d.pointwise H ∧ (d.y α:End)∈d.pointwise H
  factorOther : ∀H α,α∉hexagon H→∀a b:ℝ,a • (d.x α:End)+b • (d.y α:End)∈d.pointwise H→a=0∧b=0
  factorDim : ∀H,Module.finrank ℝ (d.pointwise H)=8
  factorTransport : ∀(i:Fin 3) D,D∈d.pointwise i.succ ↔ Option2StatementA5Anchor.transportTinv i * D * Option2StatementA5Anchor.transportT i ∈d.pointwise 0
  factorZero : ∀α,α∈hexagon 0↔∃a b:Fin 3,a≠b∧α.weight=h0Weight a-h0Weight b
def FullA4 : Prop := ∃d:Data,Pinned d ∧ ∀ξ:Fin 4→ℂ,IsUnitPhase ξ → ∃p:PhaseData d ξ,PhasePinned d ξ p ∧ Conclusions d ξ p
end Option2StatementA4
namespace Option2StatementA6
def rowSelPacked : ℕ :=
  0x68067d63c62d62c62162061a77a7796f76f66cc7626e16e07c17b87ce7bb79577f6db6da7026e676564b79878382464562382662964063f6e37647ba64785b83d62685d61e61d7be79277c7c364d6ce80769e73a67f7e87c77c57c97c47db7da7c07bd7d87d783f6f56d96ef6ed6f06ec6e87046e57f77df70b70970c70878177e78878678a7856ad68e68b69669369569261c65f62562b62863363063262f7e37e57ac7a96aa71a73c74073e74273d7f97fe7fb7fd7fa81876876d7af76a84f84c84e84b66982b82882a8277e271c81d81a81c81976766b33233133032f32e32d24124023d23c23b23a19f1681661630ac07507307220a1ef1b719c2051e92041170fc1b31981c70c40a986286185f85e84484384184077276f77176e6766736756721140f81131ee0fb0c20a70ca7b47b36d36d27b17b06d06cf2e32e22df2de2dd2dc29229128e28d28c28b1ed19e1620fa0ab07117216a08507b1f11a21040b136834d2fe2ad27725c1f717d1a608c1000af2081b91150c636736636536436339839637c37b36132b34234136032a87186f34635d35c3458823ba8833a339738437d4403b134c34b34a3493482fd2fa2f92f82f726e23824d24c26d23780280125326826725228f2a482f52d28883a2c583b4372be2ac2a92a82a72a62762a327327228a28927127025b2582572562552241d518418318218117e1310e220b20909109008f1ba08e1b808d43f43e43d43c43b4364354341181164334320c50c722521f1d21ce13212e60e60c60b6095e95e85e75e65ec5eb0df6056036026005e05df5de5dd5e35e25c55c15c45c05c75c60dd5bc5b85bb5b75be5bd54154753c53d53a53b52652c52152251f5204b94c44bc4b74b34b446847946f4664644652231d42261302200e11d31cf3cd3d93e73cc13312f2da2ea2f42d90e00de8853e93ce8462f62db17b19417a16017974974515f7290a60be0d00a40a20a308809b08706d63907006e63a06c1961b01951ae1a44d14db42a4b142b5b142d4cb42c7a27a14b01454bf4cc1b15ae5fa5d55d95f75d75db5af5b45b55b346a4235cd4224604215cb5d05a845f5d10525ca5cf5ab5a65ac5aa5a557b57756a56956056c56b55f55c56856756656556456356256155b55d55e55a55955755554f55854e55654654554454053453352b52a52952552e5241cb1e451751651b51a51951851351251551450950851151050f50e50d50c50b50a5065045074da5054fe4fd4fc4fb4f94f84f74f44fa4f34f14f04ef4ee4f24ed4e94e34e24e14ea4e04de4dd4dc4d94df4d84d64d54d44d34d24d74ce4cf4d03ef3d43ee3d34ca4c94c84c74c64c54c34c24c14c04be4bd4bb4ba4b84b54724624784af4ae4ad4ac4ab4aa4a74a64a54a44a34a249f49e49d49c49b49a49449349249149048f48c48b48a48948848748448348248148047f47747647547447147347046e46d46c46946746b3ec3d13ed3d23eb3d03ea3cf39e38339d38239b38039c38139a37f39937e1e82011e61ec21120247c47b48547d4866b70f510f0f40f712210e58a5895885395385374e749559259140240c40b4434e84e649749647a47e0db6b90d80eb3b33b21e70f353f53e31032132030f2c02bf3193143122c82c33182c115314614405c05305131531314d14b14705a0580562c72c42c21db1cc0da0d914e14c14a14805b05905705549849912a13412959f59558558454c5485325311cd59a59959759359058f58d58b57f57e57c57857557457257055054a54253552f5274f54eb4e44a848d4ec21d22b21c59859458e58c57d57957357155154b5435365305285004e54a148e22c13545d45c45b45a45945745645545345245144f44e44d44c44b44944745e45845445044a4485a25a15a059e59d59c59b59658758658358258158054d5494ff4f64a94a040a4094084074064054043b93b83b73b63b53b431121e12b04003f03e03d03c03b03a03903803703602d02c02b02a02902802702601d01c01b01a019018017016015014013002001000
def colSelPacked : ℕ :=
  0xe70e037a37937336f1d91d819218819018f0f02322312813723712d62d532732613e13b13a13018218137635b35a35735e36b22d09d09c09928028627835635f08e3751de1d32231dd1dc2270980ef2850aa15c0a92261f01ef2131ed2342182331ee20e20f2841421330fd0fc1230fa13f1240fb26a2721361251371261c71c219e19c19f19d0d30d20ce0ed0ab0ee0ac09f09527006a06806606906706330c22e1c51c60cf2bb15b15915715a15226926026525f26636730b36336518b3023073013082ba2b12b62b02b722413127b27c27a27618c08f35034c35834a35434826125b25d25726b2551e014f1511550e906206005e20c2171c31be2122191e91271201c11c81980cc0d531d31c31e3182cc2cb2cd2c718419118718309109e09409011b11c0f82291400ca0cb0a71d51d40e20e11e21e30e50e63032fd2ff2f930d2f72b22ac2ae2a82bc2a622a1e11561410ea05f14c14e05b0592161bd11f0d436834d2fe2ad27725c1ea17d19908c0f90a82141bb11d0d636c3663743643703ae3a03ad38936e36d37837736a36935c35335235d34f34e32a3a43853a339f3843883453b235134b3593493553042fa3002f830e27f27e28328227527426726426326825a2592ab2b92b52b42b823729a2902522bf2b32a92af2a72bd27d2aa27327929928f27128726225825e25626c22f1d618518618d18e17e1380f120d2150a00a10961bc0971c408d39837b36034732b2a528826d12811e2542380cd0d722521f1d21ce13212e3b337d36232c39737c36134604e04d0df2c028a26f2392a428926e25304c04b3b10443960430250240dd2be0482a30470230222e32e92de2df2dc2dd29229828d28e28b28c16817316b16616216307508607c0730710722301d72281392200f21df1cf3e83e73e93f114312f2f52f42f62fc0e80de3f03fe3f42fb30930518a19418018917919316f16517f0c80c10d00a50c90d109309b08b09a09208a0800780701ca1c91c019a1bf19b1a516116017c17a1b21b01951961b514414516e1cd1b604519717b0501461b104f15f0460200210770a40be08908806e06d04a0bd08706c05305204904104205101f01e3bf3bb34234133834434333733434033f33e33d33c33b33a33933333533633233132f32d2f13302f032e2e82e72e62e22a029f2972962952912d02c61cb1cc24d24c25125024f24e24924824b24a23f23e24724624524424324224124023c23a23d1a423b1fe1fd1fc1fb1f91f81f71f41fa1f31f120b20a2091f22082041ad1ac1ab2051aa1a81a71a61a31a91a21a01ba1b91b81b71a11b31b41d03ee3ef3f23f315e17817717617517417217117015416d16c16a16916716407f06f08510d10c10b10a1091081051041031021011001181171161151141130bc0bb0ba0b90b80b70b40b30b20b10b00af0c70c60c50c40c30c208408308208107e06507d07b07a07907607405d3f93ec3f83ed3ea3eb3f63f739d39e3a13a23a839b3a739c39939a3a53a61e82011eb2101e72070bf0a30ad0c00ae0da0f510f0f61210f31123ce3cd3cc2db2da2d920210e3d63d540340c40b4022031e61100f40a20a60db0e30d80d93be3ba21b11a2e12e031030f3173162cf2c53193143122c82c331f2c115d15314906405c05431531314d14b14705a0580562ce2c42c21db1d10e40dc15015814a14806b0610570551110f712a12912c3e33d93933922ee2ea29e29d1da3de3dd3db3d73d43d33d13cf38d38c38a38638338238037e2f22ec2e42a129b2931f52061ae1060b51ec21d21c2213dc3d83d23d038b38738137f2f32ed2e52a229c2942001af0ff0b622212d03403303203103002e01201100f00e00d00b00a00900800700500303502f01000c0060043e63e53e43e23e13e03df3da39539439139038f38e2ef2eb1ff1f61070fe40a4094084074064054043b93b83b73b63b53b431121e12b04003f03e03d03c03b03a03903803703602d02c02b02a02902802702601d01c01b01a019018017016015014013002001000
def tab (w x i : ℕ) : ℕ := (x >>> (w * i)) % 2 ^ w
def rowSelN (a : ℕ) : ℕ := tab 12 rowSelPacked a
def colSelN (b : ℕ) : ℕ := tab 12 colSelPacked b
def rowSelF (a : Fin 973) : Fin 2184 := ⟨rowSelN a.val % 2184, Nat.mod_lt _ (by decide)⟩
def colSelF (b : Fin 973) : Fin 1053 := ⟨colSelN b.val % 1053, Nat.mod_lt _ (by decide)⟩
def selectedMinor {R : Type*} (M : Matrix (Fin 2184) (Fin 1053) R) :
    Matrix (Fin 973) (Fin 973) R := M.submatrix rowSelF colSelF
end Option2StatementA6
open Filter
open scoped Topology
namespace Option2StatementA6
def analyticGermSubring (n : ℕ) :
    Subring (Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) where
  carrier := {φ | ∃ f : (Fin n → ℂ) → ℂ,
    AnalyticAt ℂ f 0 ∧ (f : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by rintro _ ⟨f, hf, rfl⟩; exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩; exact ⟨f * g, hf.mul hg, rfl⟩
abbrev GermRing (n : ℕ) := ↥(analyticGermSubring n)
open CKM.NativeFirstOrder
open CKM.NativeFourFamily (IsGoodPhase)
open Option2StatementA5Raw Option2StatementA5Slice Filter Polynomial
open scoped Topology
def ofAnalyticAt {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) : GermRing n := ⟨f, f, hf, rfl⟩
def constant (n : ℕ) : ℂ →+* GermRing n where
  toFun c := ofAnalyticAt (fun _ => c) analyticAt_const; map_zero' := rfl; map_one' := rfl; map_add' _ _ := rfl; map_mul' _ _ := rfl
instance (n : ℕ) : Algebra ℂ (GermRing n) := (constant n).toAlgebra
def evalAtZero (n : ℕ) : GermRing n →+* ℂ := Filter.Germ.valueRingHom.comp (analyticGermSubring n).subtype
def vanishingIdeal (n : ℕ) : Ideal (GermRing n) := RingHom.ker (evalAtZero n)
def coordinate (n : ℕ) (i : Fin n) : GermRing n := ofAnalyticAt (fun z => z i) ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0)
def polynomialGerm (n : ℕ) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] GermRing n := MvPolynomial.aeval (coordinate n)
def rowIdeal (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ) : Ideal (GermRing 1053) := Ideal.map (polynomialGerm 1053).toRingHom (Ideal.span (Set.range rows))
def jetLength (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ) (N : ℕ) : ℕ∞ := Module.length (GermRing 1053) (GermRing 1053 ⧸ (rowIdeal rows ⊔ vanishingIdeal 1053 ^
  (N+1)))
def pack (C : Cfg) : Fin 1053 → ℝ := fun k => C ((finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).symm k).1 ((finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).symm k).2
def packC (C : Cfg) : Fin 1053 → ℂ := fun k => (pack C k : ℂ)
def displaced (ξ : Fin 4 → ℂ) (x : Fin 1053 → ℝ) : Cfg := fun i j => literalCfg ξ i j + x (finProdFinEquiv (i,j))
abbrev SliceModel := (Fin 4 → ℝ) × (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)
def replacementLocus (rows : (Fin 4 → ℂ) → Fin 2184 → MvPolynomial (Fin 1053) ℂ) :
    Set CKM.NativeGoodPhase.PhaseTorus := {u | IsGoodPhase u.1 ∧ (selectedMinor (fun r j => (rows u.1 r).coeff (Finsupp.single j 1))).det ≠ 0}
structure A6Output (m : Product) (u : CKM.NativeGoodPhase.PhaseTorus) (σ : OpenPartialHomeomorph (derOf m × normal m u.1) Cfg) (rows : Fin 2184 → MvPolynomial (Fin
  1053) ℂ) (B : Fin 4 → (Fin 62 → ℂ) → (Fin 1053 → ℂ)) (ρ : Fin 4 → GermRing 1053 →ₐ[ℂ] GermRing 62)
    (P : Fin 4 → PrimeSpectrum (GermRing 1053)) (e : (Fin 62 → ℝ) ≃ₗ[ℝ] RawParam62 m) : Prop where
  primeBinding : ∀ H, (P H).asIdeal = RingHom.ker (ρ H).toRingHom
  dimension : ringKrullDim (GermRing 1053 ⧸ rowIdeal rows) = (62 : WithBot ℕ∞)
  ordinaryPolynomial : ∃! q : ℚ[X], (∀ᶠ N : ℕ in atTop, ((jetLength rows N).toNat : ℚ) = q.eval (N : ℚ)) ∧ q.degree = (62 : WithBot ℕ) ∧ (Nat.factorial 62 : ℚ) *
    q.leadingCoeff = 4
  distinctPrimes : Function.Injective (P)
  topPrimes : {p : Ideal (GermRing 1053) | (rowIdeal rows).IsMinimalPrime p ∧ ringKrullDim (GermRing 1053 ⧸ p) = (62 : WithBot ℕ∞)} = Set.range (fun H => RingHom.ker
    (ρ H).toRingHom)
  localizedIdeal : ∀ H : Fin 4, Ideal.map (algebraMap (GermRing 1053) (Localization.AtPrime (P H).asIdeal)) (rowIdeal rows) = Ideal.map (algebraMap (GermRing 1053)
    (Localization.AtPrime (P H).asIdeal)) (RingHom.ker (ρ H).toRingHom)
  branchAlgebras : ∀ H : Fin 4, Nonempty ((GermRing 1053 ⧸ RingHom.ker (ρ H).toRingHom) ≃ₐ[ℂ] GermRing 62)
  localizedField : ∀ H : Fin 4, IsField (Localization.AtPrime (P H).asIdeal ⧸ Ideal.map (algebraMap (GermRing 1053) (Localization.AtPrime (P H).asIdeal)) (rowIdeal
    rows))
  localizedReduced : ∀ H : Fin 4, IsReduced (Localization.AtPrime (P H).asIdeal ⧸ Ideal.map (algebraMap (GermRing 1053) (Localization.AtPrime (P H).asIdeal))
    (rowIdeal rows))
  realBranchLocus : ∀ H : Fin 4, ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧ (B H '' U) ∩ {y : Fin 1053 → ℂ | ∀ k, (y k).im = 0} = (fun x : Fin 62 → ℝ => (fun k => ((pack
    (rawMap62 m u.1 u.2 H (e x)) k : ℝ) : ℂ)) - packC (literalCfg u.1)) '' {x : Fin 62 → ℝ | (fun j => (x j : ℂ)) ∈ U}
  realSliceNormalForm : ∃ Φ : OpenPartialHomeomorph SliceModel (normal m u.1), ∃ V₀ : Fin 4 → Set SliceParam, (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧ (∀ H, V₀ H ∈ 𝓝 (0 : SliceParam)) ∧ ∀ V : Fin 4 → Set SliceParam, (∀ H, V H ∈ 𝓝 (0 : SliceParam))
        → (∀ H, V H ⊆ V₀ H) → ∀ᶠ n : normal m u.1 in 𝓝 0, n ∈ Φ.target ∧ (n ∈ ⋃ H : Fin 4, (sliceFam σ u.2 H) '' V H ↔ ∃ H : Fin 4, (∀ j : Fin 4, j ≠ H → (Φ.symm
        n).2.1 j = 0) ∧ (Φ.symm n).2.2 = 0)
end Option2StatementA6
namespace Option2StatementCode
open Option2StatementA6
end Option2StatementCode
namespace Option2StatementR
open CKM.NativeFirstOrder CKM.NativeTightCode CKM.NativeExactFrameEnergy Option2StatementA5Raw Option2StatementA5Slice Option2StatementA5
open scoped BigOperators Topology
def rawUnion (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (U : Fin 4 → Set (RawParam62 m)) : Set Cfg := ⋃ i, rawMap62 m ξ hξ i '' U i
def traceLength (x : Cfg) : ℝ := Real.sqrt (cfgPairing x x)
def traceDistance (x y : Cfg) : ℝ := traceLength (x-y)
def traceInfDist (x : Cfg) (S : Set Cfg) : ℝ := sInf ((traceDistance x) '' S)
def literalLabel : Fin 39 ≃ Fin 13 × Fin 3 where
  toFun i := (⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩); invFun x := Option2StatementResidual.framePointIndex x.1 x.2
  left_inv i := by apply Fin.ext; simp [Option2StatementResidual.framePointIndex]; omega
  right_inv x := by rcases x with ⟨f,a⟩; ext <;> simp [Option2StatementResidual.framePointIndex] <;> omega
def ExactFrames (y : Cfg) : Prop := ∀ h, Glennie.Frame (framesOf literalLabel (codePoint y) h)
abbrev Triple := EuclideanSpace ℂ (Fin 3)
abbrev Blocks := Fin 4 → Triple
def NormalForm (m : Product) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg) : Prop := ∃ C : Submodule ℝ Cfg, C =
  (LinearMap.range (fderiv ℝ (sliceCommon σ) 0).toLinearMap).map (normal m ξ).subtype ∧ Module.finrank ℝ C = 4 ∧ ∃ E : Submodule ℝ (Fin 2184 → ℝ), E = LinearMap.range
  ((fderiv ℝ Option2StatementResidual.originalF (literalCfg ξ)).comp (normal m ξ).subtypeL).toLinearMap ∧ Module.finrank ℝ E = 973 ∧ ∃ ψ : OpenPartialHomeomorph ((C ×
  Blocks) × E) (normal m ξ), ψ 0 = 0 ∧ (∃ θ : Fin 4 → (C × Triple) → SliceParam, (∀ i, θ i 0 = 0) ∧ (∀ i, ContDiffAt ℝ 2 (θ i) 0) ∧ ∀ i, (fun p : C × Triple => ψ
  ((p.1,Pi.single i p.2),0)) =ᶠ[𝓝 0] (fun p => sliceFam σ hξ i (θ i p))) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ V : Set (normal m ξ), IsOpen V → (0 : normal m ξ) ∈ V → V ⊆ Metric.ball
  0 δ →
        IsOpen (ψ.source ∩ ψ ⁻¹' V) ∧ (0 : (C × Blocks) × E) ∈ (ψ.source ∩ ψ ⁻¹' V) ∧ (ψ.source ∩ ψ ⁻¹' V) ⊆ ψ.source ∧ ψ '' (ψ.source ∩ ψ ⁻¹' V) = V ∧ ∃ e :
          ↥((ψ.source ∩ ψ ⁻¹' V) ∩ {q | q.2=0 ∧ ∃ i : Fin 4, ∀ j, j≠i → q.1.2 j=0}) ≃ₜ ↥(V ∩ {n | Option2StatementResidual.originalF (literalCfg ξ+(n : Cfg))=0}), (∀
          q, (e q : normal m ξ) = ψ q.1) ∧ (∀ n, (e.symm n : (C × Blocks) × E) = ψ.symm n.1)
open CKM.NativeFirstOrder CKM.NativeTightCode CKM.NativeExactFrameEnergy Option2StatementA5Raw Option2StatementA5Slice Option2StatementA5 Filter Topology
end Option2StatementR

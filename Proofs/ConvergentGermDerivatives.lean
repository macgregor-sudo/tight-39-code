module

public import ConvergentResidualJetMap
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# Directional derivatives of the actual analytic germ ring

First-party isolated proof, 2026-10-23. No outgoing project license is selected.
This uses the existing neighborhood-germ carrier and the actual Frechet derivative.
It introduces neither a formal-series replacement nor a jet-equivalence assumption.
The derivative, neighborhood congruence and analytic-derivative APIs are from
Mathlib, Apache-2.0, commit 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2. No upstream proof body is copied.
Thank you to the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

open Filter
open scoped Topology

namespace ConvergentGermDerivatives

open ConvergentResidualJets

private theorem exists_rep {n : ℕ} (u : GermRing n) :
    ∃ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0), ofAnalyticAt f hf = u := by
  obtain ⟨f, hf, heq⟩ := u.property
  exact ⟨f, hf, Subtype.ext heq⟩

theorem analyticAt_directionalDerivative {n : ℕ}
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (v : Fin n → ℂ) :
    AnalyticAt ℂ (fun x => fderiv ℂ f x v) 0 :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv

/-- Differentiate a representative in a fixed direction. Neighborhood equality
of representatives implies neighborhood equality of their derivatives. -/
def directionalDerivative {n : ℕ} (v : Fin n → ℂ) (u : GermRing n) : GermRing n :=
  ⟨u.val.liftOn
      (fun f => ((fun x => fderiv ℂ f x v) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ))
      (by
        intro f g h
        apply Filter.Germ.coe_eq.mpr
        exact (h.fderiv (𝕜 := ℂ)).mono fun x hx =>
          congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v) hx), by
    obtain ⟨f, hf, heq⟩ := u.property
    refine ⟨fun x => fderiv ℂ f x v, analyticAt_directionalDerivative hf v, ?_⟩
    rw [← heq]
    rfl⟩

theorem directionalDerivative_ofAnalyticAt {n : ℕ} (v : Fin n → ℂ)
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    directionalDerivative v (ofAnalyticAt f hf) =
      ofAnalyticAt (fun x => fderiv ℂ f x v) (analyticAt_directionalDerivative hf v) := rfl

theorem directionalDerivative_add {n : ℕ} (v : Fin n → ℂ) (u w : GermRing n) :
    directionalDerivative v (u + w) = directionalDerivative v u + directionalDerivative v w := by
  obtain ⟨f, hf, rfl⟩ := exists_rep u
  obtain ⟨g, hg, rfl⟩ := exists_rep w
  apply Subtype.ext
  change ((fun x => fderiv ℂ (f + g) x v) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) =
    ((fun x => fderiv ℂ f x v + fderiv ℂ g x v) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with x hfx hgx
  change fderiv ℂ (f + g) x v = fderiv ℂ f x v + fderiv ℂ g x v
  rw [fderiv_add hfx.differentiableAt hgx.differentiableAt]
  rfl

theorem directionalDerivative_mul {n : ℕ} (v : Fin n → ℂ) (u w : GermRing n) :
    directionalDerivative v (u * w) =
      directionalDerivative v u * w + u * directionalDerivative v w := by
  obtain ⟨f, hf, rfl⟩ := exists_rep u
  obtain ⟨g, hg, rfl⟩ := exists_rep w
  apply Subtype.ext
  change ((fun x => fderiv ℂ (f * g) x v) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) =
    ((fun x => fderiv ℂ f x v * g x + f x * fderiv ℂ g x v) :
      Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ)
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with x hfx hgx
  change fderiv ℂ (f * g) x v = fderiv ℂ f x v * g x + f x * fderiv ℂ g x v
  rw [fderiv_mul hfx.differentiableAt hgx.differentiableAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem directionalDerivative_constant {n : ℕ} (v : Fin n → ℂ) (c : ℂ) :
    directionalDerivative v (constant n c) = 0 := by
  apply Subtype.ext
  change ((fun x => fderiv ℂ (fun _ : Fin n → ℂ => c) x v) :
      Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) =
    ((fun _ : Fin n → ℂ => (0 : ℂ)) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x => by
    change fderiv ℂ (fun _ : Fin n → ℂ => c) x v = 0
    simp

theorem directionalDerivative_coordinate {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    directionalDerivative v (coordinate n i) = constant n (v i) := by
  apply Subtype.ext
  change ((fun x => fderiv ℂ (fun z : Fin n → ℂ => z i) x v) :
      Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) =
    ((fun _ : Fin n → ℂ => v i) : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ)
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x => by
    change fderiv ℂ (fun z : Fin n → ℂ => z i) x v = v i
    change fderiv ℂ (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ) x v = v i
    rw [ContinuousLinearMap.fderiv]
    rfl

/-- Leibniz lowers an arbitrary ideal power by one; no Noetherian hypothesis. -/
theorem directionalDerivative_mem_pow {n : ℕ} (v : Fin n → ℂ)
    (I : Ideal (GermRing n)) (d : ℕ) {u : GermRing n} (hu : u ∈ I ^ (d + 1)) :
    directionalDerivative v u ∈ I ^ d := by
  induction d generalizing u with
  | zero => simp
  | succ d ih =>
    rw [pow_succ] at hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro r hr s hs
      rw [directionalDerivative_mul]
      apply (I ^ (d + 1)).add_mem
      · simpa only [pow_succ] using Ideal.mul_mem_mul (ih hr) hs
      · exact (I ^ (d + 1)).mul_mem_right _ hr
    · intro r s hr hs
      rw [directionalDerivative_add]
      exact (I ^ (d + 1)).add_mem hr hs

end ConvergentGermDerivatives

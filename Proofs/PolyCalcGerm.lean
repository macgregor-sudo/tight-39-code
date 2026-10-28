module

public import ConvergentResidualJetMap
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Polynomial calculus, germ part (Brief B, items 4 and 1)

First-party proofs against Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55
(Lean v4.35.0-rc2) and the project's `ConvergentResidualJets.GermRing`.

* `analyticAtZero m`: the ℂ-subalgebra of functions `(Fin m → ℂ) → ℂ` analytic at `0`.
* `toGerm m : analyticAtZero m →ₐ[ℂ] GermRing m`, `toGerm f = ofAnalyticAt f`.
* `toGerm_coord`, `toGerm_invCoord_mul` (inverse coordinate is the inverse of `1 + coordinate`).
* `analyticAt_aeval` (item 1) and `ofAnalyticAt_aeval` (item 4 consequence).
-/

@[expose] public section

noncomputable section

namespace PolyCalc

open ConvergentResidualJets MvPolynomial Filter
open scoped Topology

/-- Functions on `Fin m → ℂ` analytic at the origin, as a ℂ-subalgebra. -/
def analyticAtZero (m : ℕ) : Subalgebra ℂ ((Fin m → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' := fun ha hb => ha.mul hb
  add_mem' := fun ha hb => ha.add hb
  algebraMap_mem' := fun _ => analyticAt_const

/-- Germ at the origin, as an algebra hom. -/
def toGerm (m : ℕ) : analyticAtZero m →ₐ[ℂ] GermRing m where
  toFun f := ofAnalyticAt f.1 f.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Packaging a function analytic at zero. -/
def analyticElt (m : ℕ) (f : (Fin m → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) : analyticAtZero m :=
  ⟨f, hf⟩

theorem toGerm_analyticElt {m : ℕ} (f : (Fin m → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    toGerm m (analyticElt m f hf) = ofAnalyticAt f hf := rfl

theorem toGerm_apply {m : ℕ} (f : analyticAtZero m) : toGerm m f = ofAnalyticAt f.1 f.2 := rfl

theorem analyticAt_coord (m : ℕ) (j : Fin m) : AnalyticAt ℂ (fun x : Fin m → ℂ => x j) 0 :=
  (ContinuousLinearMap.proj j : (Fin m → ℂ) →L[ℂ] ℂ).analyticAt 0

theorem toGerm_coord (m : ℕ) (j : Fin m) :
    toGerm m (analyticElt m (fun x => x j) (analyticAt_coord m j)) = coordinate m j := rfl

/-- The inverse coordinate `x ↦ (1 + x j)⁻¹`. -/
def invCoord (m : ℕ) (j : Fin m) : (Fin m → ℂ) → ℂ := fun x => (1 + x j)⁻¹

theorem analyticAt_invCoord (m : ℕ) (j : Fin m) : AnalyticAt ℂ (invCoord m j) 0 :=
  (analyticAt_const.add (analyticAt_coord m j)).inv (by simp)

/-- Germ of the inverse coordinate. -/
def invCoordGerm (m : ℕ) (j : Fin m) : GermRing m :=
  toGerm m (analyticElt m (invCoord m j) (analyticAt_invCoord m j))

theorem invCoordGerm_mul (m : ℕ) (j : Fin m) :
    invCoordGerm m j * (1 + coordinate m j) = 1 := by
  have h1 : (1 + coordinate m j : GermRing m) =
      toGerm m (analyticElt m (fun x => 1 + x j) (analyticAt_const.add (analyticAt_coord m j))) := rfl
  rw [h1, invCoordGerm, ← map_mul, ← map_one (toGerm m)]
  apply Subtype.ext
  have hc : ContinuousAt (fun x : Fin m → ℂ => 1 + x j) 0 :=
    (continuous_const.add (continuous_apply j)).continuousAt
  refine (Filter.Germ.coe_eq (l := 𝓝 (0 : Fin m → ℂ))
    (f := fun x => invCoord m j x * (1 + x j)) (g := fun _ => (1 : ℂ))).mpr ?_
  have h0 : (fun x : Fin m → ℂ => 1 + x j) 0 ≠ 0 := by simp
  filter_upwards [hc.eventually_ne h0] with x hx
  exact inv_mul_cancel₀ hx

theorem mul_invCoordGerm (m : ℕ) (j : Fin m) :
    (1 + coordinate m j) * invCoordGerm m j = 1 := by
  rw [mul_comm, invCoordGerm_mul]

theorem isUnit_one_add_coordinate (m : ℕ) (j : Fin m) :
    IsUnit (1 + coordinate m j : GermRing m) :=
  IsUnit.of_mul_eq_one _ (mul_invCoordGerm m j)

/-- Pointwise evaluation of analytic functions, as an algebra hom. -/
def evalAt {m : ℕ} (x : Fin m → ℂ) : analyticAtZero m →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ => ℂ) x).comp (analyticAtZero m).val

/-- The function `x ↦ aeval (c · x) p` is the subalgebra element `aeval c p`. -/
theorem coe_aeval_analytic {m N : ℕ} (c : Fin N → (Fin m → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (p : MvPolynomial (Fin N) ℂ) :
    ((aeval (fun j => analyticElt m (c j) (hc j)) p : analyticAtZero m) :
        (Fin m → ℂ) → ℂ) = fun x => aeval (fun j => c j x) p := by
  funext x
  exact comp_aeval_apply (f := fun j => analyticElt m (c j) (hc j)) (evalAt x) p

/-- Item 1: analyticity of polynomial evaluation along analytic inputs. -/
theorem analyticAt_aeval {m N : ℕ} (c : Fin N → (Fin m → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (p : MvPolynomial (Fin N) ℂ) :
    AnalyticAt ℂ (fun x => aeval (fun j => c j x) p) 0 := by
  rw [← coe_aeval_analytic c hc p]
  exact (aeval (fun j => analyticElt m (c j) (hc j)) p).2

/-- Item 4 consequence: germ of a polynomial evaluation = polynomial evaluation of germs. -/
theorem ofAnalyticAt_aeval {m N : ℕ} (c : Fin N → (Fin m → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) 0) (p : MvPolynomial (Fin N) ℂ)
    (h : AnalyticAt ℂ (fun x => aeval (fun j => c j x) p) 0) :
    ofAnalyticAt (fun x => aeval (fun j => c j x) p) h =
      aeval (fun j => toGerm m (analyticElt m (c j) (hc j))) p := by
  rw [← comp_aeval_apply (f := fun j => analyticElt m (c j) (hc j)) (toGerm m), toGerm_apply]
  congr 1
  exact (coe_aeval_analytic c hc p).symm

end PolyCalc

end

#print axioms PolyCalc.toGerm_coord
#print axioms PolyCalc.invCoordGerm_mul
#print axioms PolyCalc.isUnit_one_add_coordinate
#print axioms PolyCalc.analyticAt_aeval
#print axioms PolyCalc.ofAnalyticAt_aeval

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
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Germ
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

/-!
# The canonical polynomial-residual map into convergent-germ jets

Equality of germs means agreement on a neighborhood of zero. The target uses
the image of the same residual ideal and the (N+1)-st power of the ideal of
germs vanishing at zero. Only well-definedness and the representative rule
are proved here. No finite-Taylor comparison, injectivity or surjectivity is
assumed or asserted. Mathlib pin: 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section

open Filter
open scoped Topology

namespace ConvergentResidualJets

/-- Actual neighborhood germs having a representative analytic at zero. -/
def analyticGermSubring (n : ℕ) :
    Subring (Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) where
  carrier := {φ | ∃ f : (Fin n → ℂ) → ℂ,
    AnalyticAt ℂ f 0 ∧ (f : Filter.Germ (𝓝 (0 : Fin n → ℂ)) ℂ) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩

abbrev GermRing (n : ℕ) := ↥(analyticGermSubring n)
abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ

def ofAnalyticAt {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) : GermRing n := ⟨f, f, hf, rfl⟩

theorem ofAnalyticAt_eq_iff {n : ℕ} {f g : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    ofAnalyticAt f hf = ofAnalyticAt g hg ↔ f =ᶠ[𝓝 0] g := by
  rw [Subtype.ext_iff]
  exact Filter.Germ.coe_eq

def constant (n : ℕ) : ℂ →+* GermRing n where
  toFun c := ofAnalyticAt (fun _ => c) analyticAt_const
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance (n : ℕ) : Algebra ℂ (GermRing n) := (constant n).toAlgebra

def evalAtZero (n : ℕ) : GermRing n →+* ℂ :=
  Filter.Germ.valueRingHom.comp (analyticGermSubring n).subtype

/-- The ideal of actual convergent germs vanishing at zero. -/
def vanishingIdeal (n : ℕ) : Ideal (GermRing n) := RingHom.ker (evalAtZero n)

theorem vanishingIdeal_isMaximal (n : ℕ) : (vanishingIdeal n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evalAtZero n) (fun c => ⟨constant n c, rfl⟩)

def coordinate (n : ℕ) (i : Fin n) : GermRing n :=
  ofAnalyticAt (fun z => z i)
    ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0)

def polynomialGerm (n : ℕ) : Poly n →ₐ[ℂ] GermRing n :=
  MvPolynomial.aeval (coordinate n)

def variableIdeal (n : ℕ) : Ideal (Poly n) :=
  Ideal.span (Set.range (MvPolynomial.X : Fin n → Poly n))

def polynomialJetIdeal {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) : Ideal (Poly n) :=
  Q ⊔ variableIdeal n ^ (N+1)

def analyticJetIdeal {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) : Ideal (GermRing n) :=
  Ideal.map (polynomialGerm n).toRingHom Q ⊔ vanishingIdeal n ^ (N+1)

theorem map_variableIdeal_le (n : ℕ) :
    Ideal.map (polynomialGerm n).toRingHom (variableIdeal n) ≤ vanishingIdeal n := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change evalAtZero n (polynomialGerm n (MvPolynomial.X i)) = 0
  rw [polynomialGerm, MvPolynomial.aeval_X]
  rfl

theorem map_polynomialJetIdeal_le {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Ideal.map (polynomialGerm n).toRingHom (polynomialJetIdeal Q N) ≤
      analyticJetIdeal Q N := by
  unfold polynomialJetIdeal analyticJetIdeal
  rw [Ideal.map_sup, Ideal.map_pow]
  exact sup_le_sup le_rfl (pow_le_pow_left' (map_variableIdeal_le n) (N+1))

/-- The unquotiented polynomial representative map into the actual germ jet. -/
def representativeMap {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Poly n →ₐ[ℂ] (GermRing n ⧸ analyticJetIdeal Q N) :=
  (Ideal.Quotient.mkₐ ℂ (analyticJetIdeal Q N)).comp (polynomialGerm n)

/-- The canonical map retains exactly the given residual ideal, without taking its radical. -/
def jetMap {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    (Poly n ⧸ polynomialJetIdeal Q N) →ₐ[ℂ]
      (GermRing n ⧸ analyticJetIdeal Q N) :=
  Ideal.quotientMapₐ (analyticJetIdeal Q N) (polynomialGerm n)
    (Ideal.map_le_iff_le_comap.mp (map_polynomialJetIdeal_le Q N))

theorem jetMap_mk {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) (p : Poly n) :
    jetMap Q N (Ideal.Quotient.mk (polynomialJetIdeal Q N) p) =
      Ideal.Quotient.mk (analyticJetIdeal Q N) (polynomialGerm n p) := rfl

end ConvergentResidualJets

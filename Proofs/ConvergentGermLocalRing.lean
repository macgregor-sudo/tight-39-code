/-
The unit criterion and local-ring instance below adapt
SeveralComplexVariables/AnalyticGerm.lean, declarations isUnit_iff and the
IsLocalRing instance, from https://github.com/bjbraams/lean-SCV at
50392764ae64d75779abbea1396fe93d80b677cc.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: Bastiaan J Braams
Modifications: use the existing finite-coordinate complex germ carrier at
zero and its unchanged evaluation map; avoid unrelated zero-set imports;
identify the existing vanishing ideal with the standard maximal ideal;
use Mathlib's algebra first-isomorphism theorem for a complex-algebra
residue equivalence and prove its germ-representative rule.
The adapted portions retain Apache-2.0; the unchanged license text is in
LICENSES/SCV-Apache-2.0.txt.
Thank you to the author and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
module

public import ConvergentResidualJetMap
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

/-!
# The local-ring and complex residue-field binding for convergent germs

The carrier and polynomial map are unchanged. A germ is a unit exactly when
its value at zero is nonzero. Thus the existing vanishing ideal is the
standard unique maximal ideal, and its quotient is canonically the complex
numbers as a complex algebra. No Noetherianity or dimension theorem enters.
Mathlib pin: 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section

open Filter
open scoped Topology

namespace ConvergentGermLocalRing

open ConvergentResidualJets

/-- Evaluation at zero respects the existing complex algebra structure. -/
def evalAtZeroAlgHom (n : ℕ) : GermRing n →ₐ[ℂ] ℂ where
  __ := evalAtZero n
  commutes' _ := rfl

/-- A convergent germ is invertible precisely when its value is nonzero. -/
theorem isUnit_iff_eval_ne_zero {n : ℕ} (u : GermRing n) :
    IsUnit u ↔ evalAtZero n u ≠ 0 := by
  constructor
  · intro h
    exact (h.map (evalAtZero n)).ne_zero
  · obtain ⟨f, hf, heq⟩ := u.property
    have hu : u = ofAnalyticAt f hf := Subtype.ext heq.symm
    subst u
    intro h
    have hne : f 0 ≠ 0 := h
    let v := ofAnalyticAt (fun x => (f x)⁻¹) (hf.inv hne)
    have hmul : ofAnalyticAt f hf * v = 1 := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hne] with x hx
      exact mul_inv_cancel₀ hx
    exact ⟨⟨ofAnalyticAt f hf, v, hmul, by rwa [mul_comm]⟩, rfl⟩

instance germRing_isLocalRing (n : ℕ) : IsLocalRing (GermRing n) where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [isUnit_iff_eval_ne_zero, isUnit_iff_eval_ne_zero]
    by_cases ha : evalAtZero n a = 0
    · right
      have hv := congrArg (evalAtZero n) h
      have hb : evalAtZero n b = 1 := by simpa [ha] using hv
      rw [hb]
      exact one_ne_zero
    · exact Or.inl ha

/-- The maximal ideal in the local-ring interface is the existing vanishing ideal. -/
theorem maximalIdeal_eq_vanishingIdeal (n : ℕ) :
    IsLocalRing.maximalIdeal (GermRing n) = vanishingIdeal n := by
  ext u
  change ¬ IsUnit u ↔ evalAtZero n u = 0
  rw [isUnit_iff_eval_ne_zero, not_not]

/-- The quotient by the vanishing ideal is canonically the complex scalar algebra. -/
def quotientVanishingIdealEquiv (n : ℕ) :
    (GermRing n ⧸ vanishingIdeal n) ≃ₐ[ℂ] ℂ :=
  Ideal.quotientKerAlgEquivOfSurjective (f := evalAtZeroAlgHom n)
    (fun c => ⟨constant n c, rfl⟩)

theorem quotientVanishingIdealEquiv_mk (n : ℕ) (u : GermRing n) :
    quotientVanishingIdealEquiv n (Ideal.Quotient.mk (vanishingIdeal n) u) =
      evalAtZero n u := rfl

/-- The standard local-ring residue quotient is the complex scalar algebra. -/
def quotientMaximalIdealEquiv (n : ℕ) :
    (GermRing n ⧸ IsLocalRing.maximalIdeal (GermRing n)) ≃ₐ[ℂ] ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ (maximalIdeal_eq_vanishingIdeal n)).trans
    (quotientVanishingIdealEquiv n)

theorem quotientMaximalIdealEquiv_mk (n : ℕ) (u : GermRing n) :
    quotientMaximalIdealEquiv n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (GermRing n)) u) =
      evalAtZero n u := rfl

end ConvergentGermLocalRing

module

public import NativeExactCKMSharedFramesProbe

/-!
# Original CKM shared phase frames1–3

One Gram identity for the existing ordered complex phase rays proves all
same-frame projector products. The accepted native Jordan/Tits formula and
literal/included anchor equalities transfer those products, traces and sums
to the unchanged actual native points. Only finite scalar phase arithmetic
is expanded; no native point expansion, cross-frame equation, additional
configuration premise or all39 solution is introduced.

First-party proof; no third-party proof body copied. Imported source notices
remain in force: compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515 and mathlib at
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean4.35.0-rc2.
Thanks to the original CKM, native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace QuadraticCertificate.ExactCKMSharedFrames

open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier
open ExactCKMConfiguration

private theorem phase_cases (r : PhaseIndex) : r = 0 ∨ r = 1 ∨ r = 2 := by
  exact (by decide : ∀ r : PhaseIndex, r = 0 ∨ r = 1 ∨ r = 2) r

@[simp] private theorem phase_two_ne_zero : (2 : PhaseIndex) ≠ 0 := by decide
@[simp] private theorem phase_two_ne_one : (2 : PhaseIndex) ≠ 1 := by decide
@[simp] private theorem phase_neg_one : -(1 : PhaseIndex) = 2 := by decide
@[simp] private theorem phase_neg_two : -(2 : PhaseIndex) = 1 := by decide
private theorem phase_neg_one_ne_one : -(1 : PhaseIndex) ≠ 1 := by decide

private theorem phase_character_value (r : PhaseIndex) :
    character r = if r = 0 then 1 else if r = 1 then omega else -1 - omega := by
  rcases phase_cases r with rfl | rfl | rfl <;>
    norm_num [character, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod, omega_sq]

set_option maxHeartbeats 2000000 in
/-- The actual phase-ray Gram matrix is three times the identity, in outcome order. -/
theorem phaseRay_gram (s : PhaseIndex) (i j : Fin 3) :
    (∑ k : Fin 3, star (phaseRay s (i.val : PhaseIndex) k) *
      phaseRay s (j.val : PhaseIndex) k) = if i = j then (3 : ℂ) else 0 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rcases phase_cases s with rfl | rfl | rfl <;>
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [Fin.sum_univ_three, phaseRay, phase_character_value, omega,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;>
    (try simp only [if_neg phase_neg_one_ne_one, if_pos phase_neg_two]) <;>
    norm_num [omega, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply] <;> nlinarith [hs]

/-- Ordinary matrix products of the existing normalized projectors. -/
theorem phaseProjector_product (s : PhaseIndex) (i j : Fin 3) :
    phaseProjector s (i.val : PhaseIndex) * phaseProjector s (j.val : PhaseIndex) =
      if i = j then phaseProjector s (i.val : PhaseIndex) else 0 := by
  have hentry (r c : Fin 3) :
      (phaseProjector s (i.val : PhaseIndex) *
        phaseProjector s (j.val : PhaseIndex)) r c =
      (1/9 : ℂ) * phaseRay s (i.val : PhaseIndex) r *
        (∑ k : Fin 3, star (phaseRay s (i.val : PhaseIndex) k) *
          phaseRay s (j.val : PhaseIndex) k) *
        star (phaseRay s (j.val : PhaseIndex) c) := by
    calc
      _ = ∑ k : Fin 3, (1/9 : ℂ) * phaseRay s (i.val : PhaseIndex) r *
          (star (phaseRay s (i.val : PhaseIndex) k) *
            phaseRay s (j.val : PhaseIndex) k) *
          star (phaseRay s (j.val : PhaseIndex) c) := by
        simp only [Matrix.mul_apply, phaseProjector, Matrix.smul_apply,
          Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]
  ext r c
  rw [hentry, phaseRay_gram]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, phaseProjector, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    ring
  · simp [hij]

private theorem included_phase_pair (s : PhaseIndex) (i : Fin 3) :
    nativeTitsMatrixPair (includedPhasePoint s (i.val : PhaseIndex)) =
      (phaseProjector s (i.val : PhaseIndex), 0) :=
  includeHermitianMatrix_pair _

private theorem hidden_zero_product (A C : TitsComplexMatrix) :
    compactSecondTitsProduct (A, 0) (C, 0) =
      ((1/2 : ℂ) • (A*C + C*A), 0) := by
  simp [compactSecondTitsProduct, compactSecondTitsProductComplex,
    compactSecondTitsProductHidden, Matrix.adjugate_zero]

/-- The actual native Jordan products inherit the same diagonal outcome rule. -/
theorem includedPhasePoint_jordan (s : PhaseIndex) (i j : Fin 3) :
    Glennie.jordan (includedPhasePoint s (i.val : PhaseIndex))
      (includedPhasePoint s (j.val : PhaseIndex)) =
      if i = j then includedPhasePoint s (i.val : PhaseIndex) else 0 := by
  apply nativeTitsMatrixPair_injective
  have h := native_tits_product_pair (includedPhasePoint s (i.val : PhaseIndex))
    (includedPhasePoint s (j.val : PhaseIndex))
  change nativeTitsMatrixPair _ = compactSecondTitsProduct
    (nativeTitsMatrixPair _) (nativeTitsMatrixPair _) at h
  rw [included_phase_pair, included_phase_pair, hidden_zero_product,
    phaseProjector_product, phaseProjector_product] at h
  rw [h]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, included_phase_pair]
    apply Prod.ext
    · ext r c
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    · rfl
  · simp [hij, Ne.symm hij]

private theorem native_pair_unit :
    nativeTitsMatrixPair (1 : Glennie.Albert) = (1, 0) := by
  change toMatrixPair (toTitsCoordinates (1 : Glennie.Albert)) = (1, 0)
  have hu := compactTitsCoordinateEquiv_unit
  change toTitsCoordinates (1 : Glennie.Albert) = titsUnit at hu
  rw [hu]
  apply Prod.ext
  · ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [toMatrixPair, hermitianMatrix, titsUnit, Matrix.one_apply]
  · rfl

/-- The existing included phase projectors form one native ordered frame for every s. -/
theorem includedPhase_frame (s : PhaseIndex) :
    Glennie.Frame (fun i : Fin 3 => includedPhasePoint s (i.val : PhaseIndex)) := by
  constructor
  · intro i
    have hv : hermitianMatrix
        (toTitsCoordinates (includedPhasePoint s (i.val : PhaseIndex))) =
        phaseProjector s (i.val : PhaseIndex) :=
      congrArg (fun p : TitsMatrixPair => p.1) (included_phase_pair s i)
    have ht : (Glennie.trace (includedPhasePoint s (i.val : PhaseIndex)) : ℂ) = 1 := by
      calc
        _ = (hermitianMatrix
            (toTitsCoordinates (includedPhasePoint s (i.val : PhaseIndex)))).trace :=
          (hermitianMatrix_trace _).symm
        _ = 1 := by rw [hv, phaseProjector_trace]
    simpa using congrArg Complex.re ht
  · intro i
    simpa only [ite_true] using includedPhasePoint_jordan s i i
  · intro i j hij
    simpa only [if_neg hij] using includedPhasePoint_jordan s i j
  · apply nativeTitsMatrixPair_injective
    rw [map_add, map_add, included_phase_pair, included_phase_pair,
      included_phase_pair, native_pair_unit]
    have huniv : (Finset.univ : Finset PhaseIndex) = {0, 1, 2} := by decide
    have hsum : phaseProjector s 0 + phaseProjector s 1 + phaseProjector s 2 = 1 := by
      have h := phaseProjector_sum s
      rw [huniv,
        Finset.sum_insert (by decide : (0 : PhaseIndex) ∉ ({1, 2} : Finset PhaseIndex)),
        Finset.sum_insert (by decide : (1 : PhaseIndex) ∉ ({2} : Finset PhaseIndex)),
        Finset.sum_singleton] at h
      simpa only [add_assoc] using h
    apply Prod.ext
    · simpa using hsum
    · simp

/-- Literal native phase anchors inherit the proved frame in their original order. -/
theorem literalNativePhase_frame (s : PhaseIndex) :
    Glennie.Frame (fun i : Fin 3 => literalNativePhasePoint s (i.val : PhaseIndex)) := by
  simpa only [literalNativePhasePoint_eq_included] using includedPhase_frame s

/-- Original shared frames1,2,3, with all original outcome labels retained. -/
theorem nativePoint_phase_frames (s : Fin 3) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex (sharedPhaseFrameLabel s) t)) := by
  rw [nativePoint_phase_eq_literal]
  exact literalNativePhase_frame (s.val : PhaseIndex)


/-- Original shared frame labels0,1,2,3, without any permutation. -/
def sharedFrameLabel (f : Fin 4) : Fin 13 := ⟨f.val, by omega⟩

/-- The four actual shared CKM frames, using the accepted coordinate-frame endpoint. -/
theorem nativePoint_shared_frames (f : Fin 4) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex (sharedFrameLabel f) t)) := by
  fin_cases f
  · exact nativePoint_coordinate_frame
  · exact nativePoint_phase_frames (0 : Fin 3)
  · exact nativePoint_phase_frames (1 : Fin 3)
  · exact nativePoint_phase_frames (2 : Fin 3)

end QuadraticCertificate.ExactCKMSharedFrames

#print axioms QuadraticCertificate.ExactCKMSharedFrames.phaseRay_gram
#print axioms QuadraticCertificate.ExactCKMSharedFrames.phaseProjector_product
#print axioms QuadraticCertificate.ExactCKMSharedFrames.includedPhasePoint_jordan
#print axioms QuadraticCertificate.ExactCKMSharedFrames.nativePoint_phase_frames

#print axioms QuadraticCertificate.ExactCKMSharedFrames.nativePoint_shared_frames

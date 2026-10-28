module

public import NativePartialAction

@[expose] public section

/-!
Frame-preserving relabelling of the literal original native residuals.
The action is pullback: the new point (f,a) is the old point (σ f, τ f a).
The induced residual permutation retains all four original row blocks, including
every unordered point pair with its within-frame 0 / cross-frame t convention.
This proves no reconstruction of frame grouping, seed invariance or quotient claim.
First-party proof using existing project definitions and imported Mathlib APIs;
no upstream implementation is copied. Mathlib pin 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section
open scoped BigOperators

namespace NativeFrameRelabelling

open NativePolynomial NativePolynomial.CoordinateMaps
open NativePolynomial.ConfigurationResiduals NativePolynomial.PartialAction
open ConfigurationResidualIndices

variable (σ : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))

def frameOutcomePerm : Equiv.Perm (Fin 13 × Fin 3) where
  toFun p := (σ p.1, τ p.1 p.2)
  invFun p := (σ.symm p.1, (τ (σ.symm p.1)).symm p.2)
  left_inv := by rintro ⟨f, a⟩; simp
  right_inv := by rintro ⟨f, a⟩; simp

/-- The induced permutation of the actual 39 point labels. -/
def pointPerm : Equiv.Perm (Fin 39) :=
  finProdFinEquiv.symm.trans ((frameOutcomePerm σ τ).trans finProdFinEquiv)

private theorem framePointIndex_eq (f : Fin 13) (a : Fin 3) :
    framePointIndex f a = finProdFinEquiv (f, a) := by
  apply Fin.ext
  change 3 * f.val + a.val = a.val + 3 * f.val
  omega

theorem pointPerm_framePointIndex (f : Fin 13) (a : Fin 3) :
    pointPerm σ τ (framePointIndex f a) = framePointIndex (σ f) (τ f a) := by
  simp only [framePointIndex_eq, pointPerm, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  rfl

private theorem pointPerm_frame (p : Fin 39) :
    (pointPerm σ τ p).val / 3 =
      (σ ((finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm p).1).val := by
  let q := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm p
  change ((τ q.1 q.2).val + 3 * (σ q.1).val) / 3 = (σ q.1).val
  have h := (τ q.1 q.2).isLt
  omega

theorem pointPerm_same_frame (p q : Fin 39) :
    (pointPerm σ τ p).val / 3 = (pointPerm σ τ q).val / 3 ↔
      p.val / 3 = q.val / 3 := by
  rw [pointPerm_frame, pointPerm_frame]
  constructor
  · intro h
    have hh := σ.injective (Fin.ext h)
    exact congrArg Fin.val hh
  · intro h
    have hh : ((finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm p).1 =
      ((finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).symm q).1 := Fin.ext h
    rw [hh]

def pairMap (e : Equiv.Perm (Fin 39)) (p : Pair 39) : Pair 39 :=
  if h : e p.val.1 < e p.val.2 then ⟨(e p.val.1, e p.val.2), h⟩
  else ⟨(e p.val.2, e p.val.1), by
    have hne : e p.val.1 ≠ e p.val.2 :=
      fun he => (ne_of_lt p.property) (e.injective he)
    exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)⟩

theorem pairMap_inverse (e : Equiv.Perm (Fin 39)) (p : Pair 39) :
    pairMap e.symm (pairMap e p) = p := by
  by_cases h : e p.val.1 < e p.val.2
  · simp only [pairMap, h, ↓reduceDIte, Equiv.symm_apply_apply, p.property]
  · have hp : ¬ p.val.2 < p.val.1 := not_lt_of_gt p.property
    simp only [pairMap, h, ↓reduceDIte, Equiv.symm_apply_apply, hp]

def pairPerm (e : Equiv.Perm (Fin 39)) : Equiv.Perm (Pair 39) where
  toFun := pairMap e
  invFun := pairMap e.symm
  left_inv := pairMap_inverse e
  right_inv := pairMap_inverse e.symm

/-- Reindex the existing typed rows, sorting the two endpoints of each pair. -/
def labelPerm : Equiv.Perm FLabel :=
  Equiv.sumCongr (Equiv.prodCongr (pointPerm σ τ) (Equiv.refl _))
    (Equiv.sumCongr (pointPerm σ τ)
      (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl _)) (pairPerm (pointPerm σ τ))))

/-- The same permutation in the original 0..2183 row numbering. -/
def rowPerm : Equiv.Perm (Fin 2184) :=
  fNumber.symm.trans ((labelPerm σ τ).trans fNumber)

/-- Pull back a native configuration along the explicit 39-label permutation. -/
def relabel {S : Type*} (C : Configuration S) : Configuration S :=
  fun p => C (pointPerm σ τ p)

variable {S : Type*} [CommRing S]

private theorem pairing_swap (x y : NativeVector S) :
    coordinatePairing x y = coordinatePairing y x := by
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem pair_value (h t : S) (C : Configuration S) (p : Pair 39) :
    originalValue h t (relabel σ τ C) (fPair p) =
      originalValue h t C (fPair (pairMap (pointPerm σ τ) p)) := by
  have hframe := pointPerm_same_frame σ τ p.val.1 p.val.2
  by_cases hp : pointPerm σ τ p.val.1 < pointPerm σ τ p.val.2
  · simp only [pairMap, hp, ↓reduceDIte, originalValue, fPair, relabel]
    simp only [hframe]
  · simp only [pairMap, hp, ↓reduceDIte, originalValue, fPair, relabel]
    rw [pairing_swap (C (pointPerm σ τ p.val.1)) (C (pointPerm σ τ p.val.2))]
    have hframe' : (pointPerm σ τ p.val.2).val / 3 =
        (pointPerm σ τ p.val.1).val / 3 ↔ p.val.1.val / 3 = p.val.2.val / 3 :=
      eq_comm.trans hframe
    simp only [hframe']

/-- Off-shell equivariance of every existing typed residual, with no solution premise. -/
theorem originalValue_relabel (h t : S) (C : Configuration S) (q : FLabel) :
    originalValue h t (relabel σ τ C) q =
      originalValue h t C (labelPerm σ τ q) := by
  rcases q with ⟨p, k⟩ | p | ⟨f, k⟩ | p
  · rfl
  · rfl
  · change (∑ a : Fin 3, C (pointPerm σ τ (framePointIndex f a)) k) - _ =
      (∑ a : Fin 3, C (framePointIndex (σ f) a) k) - _
    simp_rw [pointPerm_framePointIndex]
    rw [Equiv.sum_comp (τ f) (fun a => C (framePointIndex (σ f) a) k)]
    rfl
  · exact pair_value σ τ h t C p

/-- Off-shell equivariance in the literal all-2184 polynomial row numbering. -/
theorem original_fRow_relabel (h t : S) (C : Configuration S) (r : Fin 2184) :
    MvPolynomial.eval (pack (relabel σ τ C)) (fRow h t r) =
      MvPolynomial.eval (pack C) (fRow h t (rowPerm σ τ r)) := by
  rw [eval_fRow, eval_fRow, originalValue_relabel]
  simp only [rowPerm, Equiv.trans_apply, fNumber.symm_apply_apply]

/-- Relabelling preserves and reflects the exact original solution set. -/
theorem all_original_F_iff (h t : S) (C : Configuration S) :
    (∀ r : Fin 2184, MvPolynomial.eval (pack (relabel σ τ C)) (fRow h t r) = 0) ↔
      ∀ r : Fin 2184, MvPolynomial.eval (pack C) (fRow h t r) = 0 := by
  simp_rw [original_fRow_relabel]
  constructor
  · intro hC r
    simpa only [Equiv.apply_symm_apply] using hC ((rowPerm σ τ).symm r)
  · intro hC r
    exact hC (rowPerm σ τ r)

end NativeFrameRelabelling

module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
First-party consequences of the supplied Book quartic identity.
The identity and axis vanishing remain explicit inputs; no native coefficients,
stress covectors, sheet maps or metric dictionaries are certified here.
All squared lengths of block families are explicit finite sums, not Pi norms.
The argument subtracts two identities and uses quadratic polarization; it does
not differentiate a coefficient expansion or classify exceptional ranks.
-/

noncomputable section

namespace Option2.NativeStress.FourBlock

open scoped BigOperators InnerProductSpace

variable {B V : Type*}
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A block family supported on one of the four coordinate axes. -/
def OnAxis (i : Fin 4) (u : Fin 4 → B) : Prop :=
  ∀ j, j ≠ i → u j = 0

/-- The sum of squared block lengths; no norm on the Pi type is used. -/
def totalSquaredLength (u : Fin 4 → B) : ℝ := ∑ i, ‖u i‖ ^ 2

/-- Each unordered pair of block energies is counted exactly once. -/
def crossEnergy (a : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then a i * a j else 0

def delta (u : Fin 4 → B) : ℝ := crossEnergy (fun i => ‖u i‖ ^ 2)

def blockPair (x y : Fin 4 → V) : ℝ := ∑ i, ⟪x i, y i⟫_ℝ

def sigmaBlocks (sigma : Fin 4 → QuadraticMap ℝ B V) (u : Fin 4 → B) :
    Fin 4 → V := fun i => sigma i (u i)

/-- The exact real identity, with the Book's coefficients one, one-half, three. -/
def QuarticIdentity (H T : QuadraticMap ℝ (Fin 4 → B) (Fin 4 → V))
    (sigma : Fin 4 → QuadraticMap ℝ B V) : Prop :=
  ∀ u, delta u = totalSquaredLength (H u) +
    (1 / 2 : ℝ) * totalSquaredLength (T u) +
    3 * blockPair (sigmaBlocks sigma u) (H u)

private theorem exists_block_ne_zero {u : Fin 4 → B} (hu : u ≠ 0) :
    ∃ i, u i ≠ 0 := by
  by_contra h
  apply hu
  funext i
  by_contra hi
  exact h ⟨i, hi⟩

private theorem totalSquaredLength_pos {u : Fin 4 → B} (hu : u ≠ 0) :
    0 < totalSquaredLength u := by
  obtain ⟨i, hi⟩ := exists_block_ne_zero hu
  have hle : ‖u i‖ ^ 2 ≤ totalSquaredLength u :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖u j‖) (Finset.mem_univ i)
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi)) hle

private theorem axis_component_ne_zero {i : Fin 4} {w : Fin 4 → B}
    (hw : OnAxis i w) (hw0 : w ≠ 0) : w i ≠ 0 := by
  intro hi
  apply hw0
  funext j
  by_cases hji : j = i
  · simpa [hji] using hi
  · exact hw j hji

private theorem delta_zero_implies_axis {u : Fin 4 → B} (hu : delta u = 0) :
    ∃ i, OnAxis i u := by
  change (∑ i : Fin 4, ∑ j : Fin 4,
    if i < j then ‖u i‖ ^ 2 * ‖u j‖ ^ 2 else 0) = 0 at hu
  have hnonneg : ∀ i j : Fin 4,
      0 ≤ (if i < j then ‖u i‖ ^ 2 * ‖u j‖ ^ 2 else 0 : ℝ) := by
    intro i j
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact le_rfl
  have hrows : ∀ i : Fin 4,
      (∑ j : Fin 4, if i < j then ‖u i‖ ^ 2 * ‖u j‖ ^ 2 else 0) = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hnonneg i j))).mp hu
    exact fun i => h i (Finset.mem_univ i)
  have hpairs : ∀ i j : Fin 4, i < j → ‖u i‖ ^ 2 * ‖u j‖ ^ 2 = 0 := by
    intro i j hij
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hnonneg i j)).mp (hrows i)
    simpa [hij] using h j (Finset.mem_univ j)
  by_cases hz : u = 0
  · refine ⟨0, ?_⟩
    intro j _
    simp [hz]
  · obtain ⟨i, hi⟩ := exists_block_ne_zero hz
    refine ⟨i, ?_⟩
    intro j hji
    by_contra hj
    have hiPos := sq_pos_of_pos (norm_pos_iff.mpr hi)
    have hjPos := sq_pos_of_pos (norm_pos_iff.mpr hj)
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hpos := mul_pos hjPos hiPos
      rw [hpairs j i hlt] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    · have hpos := mul_pos hiPos hjPos
      rw [hpairs i j hgt] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos

/-- The quartic identity and axis vanishing determine the entire real zero cone. -/
theorem zero_cone
    (H T : QuadraticMap ℝ (Fin 4 → B) (Fin 4 → V))
    (sigma : Fin 4 → QuadraticMap ℝ B V)
    (hidentity : QuarticIdentity H T sigma)
    (haxis : ∀ i u, OnAxis i u → H u = 0 ∧ T u = 0)
    (u : Fin 4 → B) :
    (H u = 0 ∧ T u = 0) ↔ ∃ i, OnAxis i u := by
  constructor
  · rintro ⟨hH, hT⟩
    apply delta_zero_implies_axis
    simpa [hH, hT, totalSquaredLength, blockPair] using hidentity u
  · rintro ⟨i, hi⟩
    exact haxis i u hi

private theorem crossEnergy_replace (a : Fin 4 → ℝ) (i : Fin 4) (t : ℝ)
    (hi : a i = 0) :
    crossEnergy (fun j => if j = i then t else a j) =
      crossEnergy a + t * (∑ j, a j) := by
  fin_cases i <;> simp_all [crossEnergy, Fin.sum_univ_succ] <;> ring

private theorem delta_add_axis {i : Fin 4} {w n : Fin 4 → B}
    (hw : OnAxis i w) (hn : n i = 0) :
    delta (w + n) = delta n + ‖w i‖ ^ 2 * totalSquaredLength n := by
  have hv : (fun j => ‖(w + n) j‖ ^ 2) =
      (fun j => if j = i then ‖w i‖ ^ 2 else ‖n j‖ ^ 2) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Pi.add_apply, hn]
    · simp [Pi.add_apply, hw j hji, hji]
  change crossEnergy (fun j => ‖(w + n) j‖ ^ 2) =
    crossEnergy (fun j => ‖n j‖ ^ 2) + ‖w i‖ ^ 2 * totalSquaredLength n
  rw [hv]
  simpa [totalSquaredLength] using
    crossEnergy_replace (fun j => ‖n j‖ ^ 2) i (‖w i‖ ^ 2) (by simp [hn])

private theorem sigmaBlocks_add_axis (sigma : Fin 4 → QuadraticMap ℝ B V)
    {i : Fin 4} {w n : Fin 4 → B} (hw : OnAxis i w) (hn : n i = 0) :
    sigmaBlocks sigma (w + n) = sigmaBlocks sigma w + sigmaBlocks sigma n := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [sigmaBlocks, Pi.add_apply, hn]
  · simp [sigmaBlocks, Pi.add_apply, hw j hji]

private theorem blockPair_add_left (x y z : Fin 4 → V) :
    blockPair (x + y) z = blockPair x z + blockPair y z := by
  simp only [blockPair, Pi.add_apply, inner_add_left, Finset.sum_add_distrib]

private theorem blockPair_sigma_axis (sigma : Fin 4 → QuadraticMap ℝ B V)
    {i : Fin 4} {w : Fin 4 → B} (hw : OnAxis i w) (y : Fin 4 → V) :
    blockPair (sigmaBlocks sigma w) y = ⟪sigma i (w i), y i⟫_ℝ := by
  change (∑ j, ⟪sigma j (w j), y j⟫_ℝ) = ⟪sigma i (w i), y i⟫_ℝ
  apply Finset.sum_eq_single i
  · intro j _ hji
    simp [hw j hji]
  · simp

/-- On the common polar kernel the stress value is exactly the product of
the axis length squared and the explicit total normal length squared. -/
theorem kernel_stress_identity
    (H T : QuadraticMap ℝ (Fin 4 → B) (Fin 4 → V))
    (sigma : Fin 4 → QuadraticMap ℝ B V)
    (hidentity : QuarticIdentity H T sigma)
    (haxis : ∀ i u, OnAxis i u → H u = 0 ∧ T u = 0)
    (i : Fin 4) (w n : Fin 4 → B)
    (hw : OnAxis i w) (hn : n i = 0)
    (hHpolar : QuadraticMap.polar H w n = 0)
    (hTpolar : QuadraticMap.polar T w n = 0) :
    3 * ⟪sigma i (w i), H n i⟫_ℝ = ‖w i‖ ^ 2 * totalSquaredLength n := by
  have hH : H (w + n) = H n := by
    rw [QuadraticMap.map_add H w n, (haxis i w hw).1, hHpolar, zero_add, add_zero]
  have hT : T (w + n) = T n := by
    rw [QuadraticMap.map_add T w n, (haxis i w hw).2, hTpolar, zero_add, add_zero]
  have hadd := hidentity (w + n)
  rw [hH, hT, sigmaBlocks_add_axis sigma hw hn, blockPair_add_left,
    blockPair_sigma_axis sigma hw (H n)] at hadd
  have hbase := hidentity n
  have hdelta := delta_add_axis hw hn
  linarith

/-- Nonzero normal vectors in the polar kernel have strictly positive stress. -/
theorem kernel_stress_pos
    (H T : QuadraticMap ℝ (Fin 4 → B) (Fin 4 → V))
    (sigma : Fin 4 → QuadraticMap ℝ B V)
    (hidentity : QuarticIdentity H T sigma)
    (haxis : ∀ i u, OnAxis i u → H u = 0 ∧ T u = 0)
    (i : Fin 4) (w n : Fin 4 → B)
    (hw : OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0) (hn0 : n ≠ 0)
    (hHpolar : QuadraticMap.polar H w n = 0)
    (hTpolar : QuadraticMap.polar T w n = 0) :
    0 < 3 * ⟪sigma i (w i), H n i⟫_ℝ := by
  rw [kernel_stress_identity H T sigma hidentity haxis i w n hw hn hHpolar hTpolar]
  exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (axis_component_ne_zero hw hw0)))
    (totalSquaredLength_pos hn0)

/-- When the sigma coefficient vanishes, the common normal polar kernel is zero. -/
theorem kernel_eq_zero_of_sigma_eq_zero
    (H T : QuadraticMap ℝ (Fin 4 → B) (Fin 4 → V))
    (sigma : Fin 4 → QuadraticMap ℝ B V)
    (hidentity : QuarticIdentity H T sigma)
    (haxis : ∀ i u, OnAxis i u → H u = 0 ∧ T u = 0)
    (i : Fin 4) (w n : Fin 4 → B)
    (hw : OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0)
    (hsigma : sigma i (w i) = 0)
    (hHpolar : QuadraticMap.polar H w n = 0)
    (hTpolar : QuadraticMap.polar T w n = 0) : n = 0 := by
  by_contra hn0
  have hpos := kernel_stress_pos H T sigma hidentity haxis i w n hw hn hw0 hn0
    hHpolar hTpolar
  simpa [hsigma] using hpos

end Option2.NativeStress.FourBlock

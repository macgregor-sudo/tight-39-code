module

public import NativeTrialityOctonion

/-!
# The skew endomorphisms of the native octonion space have dimension 28

`skewEnd` (skew-adjoint for the native pairing `octDot`) has dimension `8·7/2 = 28`: in the
orthonormal coordinate basis `octBasis`, a skew map is determined by its 28 strict upper-triangular
entries, and every choice of those entries occurs (elementary rotations `E_ij - E_ji`).
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Coordinates

Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`
(`octCoord`, `octonion_ext_coord`, `octDot_octBasis_left`, `octonion_eq_sum`), renamed. -/

/-- The real coordinates of a native octonion, in the order of `octOfCoord`. -/
def skewCoord (i : Fin 8) (x : Octonion) : ℝ :=
  ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK] i

theorem skewCoord_octBasis (i j : Fin 8) : skewCoord i (octBasis j) = if i = j then 1 else 0 := by
  have h : ∀ v : Fin 8 → ℝ, skewCoord i (octOfCoord v) = v i := by
    intro v; fin_cases i <;> rfl
  rw [octBasis, h, Pi.single_apply]

theorem skewCoord_add (i : Fin 8) (x y : Octonion) :
    skewCoord i (x + y) = skewCoord i x + skewCoord i y := by
  fin_cases i <;> rfl

theorem skewCoord_smul (i : Fin 8) (r : ℝ) (x : Octonion) :
    skewCoord i (r • x) = r * skewCoord i x := by
  fin_cases i <;> rfl

theorem skewCoord_ext {x y : Octonion} (h : ∀ i, skewCoord i x = skewCoord i y) : x = y := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  simp only [skewCoord] at h0 h1 h2 h3 h4 h5 h6 h7
  apply Prod.ext <;> apply Quaternion.ext <;> assumption

theorem octDot_octBasis_left_coord (j : Fin 8) (x : Octonion) :
    octDot (octBasis j) x = skewCoord j x := by
  rw [octDot_coordinates]
  fin_cases j <;> simp [octBasis, octOfCoord, skewCoord]

/-- Orthonormality of `octBasis`, re-derived here from the coordinate formula (same statement as the
frozen `octDot_octBasis`, proved locally so this file does not depend on the skeleton's body). -/
theorem octDot_octBasis_local (i j : Fin 8) :
    octDot (octBasis i) (octBasis j) = if i = j then 1 else 0 := by
  rw [octDot_octBasis_left_coord, skewCoord_octBasis]

/-- Every octonion is the combination of the basis with its `octDot` coordinates. -/
theorem octonion_eq_sum_octDot (x : Octonion) : x = ∑ j, octDot (octBasis j) x • octBasis j := by
  apply skewCoord_ext
  intro i
  have hsum : skewCoord i (∑ j, octDot (octBasis j) x • octBasis j) =
      ∑ j, skewCoord j x * skewCoord i (octBasis j) := by
    simp only [Fin.sum_univ_eight, skewCoord_add, skewCoord_smul, octDot_octBasis_left_coord]
  rw [hsum]
  simp [skewCoord_octBasis]

/-! ## Linearity of the pairing and the skewness condition -/

theorem octDot_lin_left (a b : ℝ) (u v y : Octonion) :
    octDot (a • u - b • v) y = a * octDot u y - b * octDot v y := by
  simp only [← octDotForm_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]

theorem octDot_sum_left {ι : Type*} (s : Finset ι) (f : ι → Octonion) (y : Octonion) :
    octDot (∑ p ∈ s, f p) y = ∑ p ∈ s, octDot (f p) y := by
  simp only [← octDotForm_apply, map_sum, LinearMap.sum_apply]

theorem mem_skewEnd_iff {T : Module.End ℝ Octonion} :
    T ∈ skewEnd ↔ ∀ x y, octDot (T x) y = -octDot x (T y) := by
  show T ∈ octDotForm.skewAdjointSubmodule ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  show octDotForm (T x) y = octDotForm x (-(T y)) ↔ _
  rw [map_neg]
  rfl

/-- A skew map whose strict upper-triangular entries vanish is zero. -/
theorem eq_zero_of_upper_entries {T : Module.End ℝ Octonion} (hT : T ∈ skewEnd)
    (h : ∀ a b : Fin 8, a < b → octDot (T (octBasis b)) (octBasis a) = 0) : T = 0 := by
  have hskew := mem_skewEnd_iff.1 hT
  have hall : ∀ a b : Fin 8, octDot (T (octBasis b)) (octBasis a) = 0 := by
    intro a b
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact h a b hab
    · have := hskew (octBasis a) (octBasis a)
      rw [octDot_comm (octBasis a) (T (octBasis a))] at this
      linarith
    · rw [hskew, octDot_comm, h b a hab, neg_zero]
  have hcol : ∀ j, T (octBasis j) = 0 := by
    intro j
    rw [octonion_eq_sum_octDot (T (octBasis j))]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [octDot_comm, hall, zero_smul]
  refine LinearMap.ext fun x => ?_
  rw [octonion_eq_sum_octDot x, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, hcol, smul_zero]

/-! ## Elementary rotations -/

/-- The elementary rotation `x ↦ ⟨e_j, x⟩ e_i - ⟨e_i, x⟩ e_j`. -/
def elemRot (i j : Fin 8) : Module.End ℝ Octonion :=
  (octDotForm (octBasis j)).smulRight (octBasis i) - (octDotForm (octBasis i)).smulRight (octBasis j)

theorem elemRot_apply (i j : Fin 8) (x : Octonion) :
    elemRot i j x = octDot (octBasis j) x • octBasis i - octDot (octBasis i) x • octBasis j := rfl

theorem elemRot_mem (i j : Fin 8) : elemRot i j ∈ skewEnd := by
  refine mem_skewEnd_iff.2 fun x y => ?_
  rw [elemRot_apply, elemRot_apply, octDot_lin_left, octDot_comm x, octDot_lin_left,
    octDot_comm (octBasis i) x, octDot_comm (octBasis j) x]
  ring

theorem elemRot_entry (i j a b : Fin 8) :
    octDot (elemRot i j (octBasis b)) (octBasis a) =
      (if j = b then (1 : ℝ) else 0) * (if i = a then 1 else 0) -
        (if i = b then (1 : ℝ) else 0) * (if j = a then 1 else 0) := by
  rw [elemRot_apply, octDot_lin_left, octDot_octBasis_local, octDot_octBasis_local,
    octDot_octBasis_local, octDot_octBasis_local]

/-! ## The coordinate isomorphism -/

/-- Strictly increasing index pairs `i < j` in `Fin 8`. -/
abbrev UpperPair := {p : Fin 8 × Fin 8 // p.1 < p.2}

/-- The strict upper-triangular entries `⟨T e_j, e_i⟩`, `i < j`, of a skew map. -/
def skewEntries : skewEnd →ₗ[ℝ] (UpperPair → ℝ) where
  toFun T p := octDot ((T : Module.End ℝ Octonion) (octBasis p.1.2)) (octBasis p.1.1)
  map_add' T S := by
    funext p
    exact octDot_add_left _ _ _
  map_smul' r T := by
    funext p
    exact octDot_smul_left _ _ _

theorem skewEntries_injective : Function.Injective skewEntries := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  apply Subtype.ext
  exact eq_zero_of_upper_entries T.2 fun a b hab => congrFun hT ⟨(a, b), hab⟩

theorem elemRot_entry_upper (p q : UpperPair) :
    octDot (elemRot p.1.1 p.1.2 (octBasis q.1.2)) (octBasis q.1.1) = if p = q then 1 else 0 := by
  rw [elemRot_entry]
  have hsecond : (if p.1.1 = q.1.2 then (1 : ℝ) else 0) * (if p.1.2 = q.1.1 then 1 else 0) = 0 := by
    by_cases h1 : p.1.1 = q.1.2
    · have h2 : p.1.2 ≠ q.1.1 := by
        intro h2
        have hp := p.2
        rw [h1, h2] at hp
        exact lt_asymm q.2 hp
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]
  rw [hsecond, sub_zero]
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [ite_eq_right hpq]
    by_cases h1 : p.1.2 = q.1.2
    · have h2 : p.1.1 ≠ q.1.1 := fun h2 => hpq (Subtype.ext (Prod.ext h2 h1))
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

theorem skewEntries_surjective : Function.Surjective skewEntries := by
  intro c
  have hT : (∑ p : UpperPair, c p • elemRot p.1.1 p.1.2) ∈ skewEnd :=
    Submodule.sum_mem octDotForm.skewAdjointSubmodule fun p _ =>
      Submodule.smul_mem octDotForm.skewAdjointSubmodule (c p) (elemRot_mem p.1.1 p.1.2)
  refine ⟨⟨_, hT⟩, ?_⟩
  funext q
  show octDot ((∑ p : UpperPair, c p • elemRot p.1.1 p.1.2) (octBasis q.1.2)) (octBasis q.1.1) = c q
  rw [LinearMap.sum_apply, octDot_sum_left]
  simp only [LinearMap.smul_apply, octDot_smul_left, elemRot_entry_upper, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem card_upperPair : Fintype.card UpperPair = 28 := by
  decide

/-- The skew endomorphisms of the native octonion space have dimension `28`. -/
theorem finrank_skewEnd : Module.finrank ℝ skewEnd = 28 := by
  rw [(LinearEquiv.ofBijective skewEntries
      ⟨skewEntries_injective, skewEntries_surjective⟩).finrank_eq,
    Module.finrank_fintype_fun_eq_card, card_upperPair]

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.finrank_skewEnd

module

public import A4KRep
public import NativeTrialityOctonion
public import NativeTrialitySkewDim
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section

/-!
# The `D₄` root system of the skew endomorphisms of the native octonions

Everything here lives in `Module.End ℝ Glennie.Octonion`, on the actual native octonions with the
native dot product `octDot`. The four coordinate planes `(1,i), (j,k), (ℓ,iℓ), (n,kℓ)` are the
coordinate pairs `(2r, 2r+1)` of `octOfCoord`, `r = 0,1,2,3` (Peirce weight `ε_{r+1}`).

* `wedge u v : x ↦ ⟨v,x⟩ u − ⟨u,x⟩ v` (the bivector map); `cartanGen r` rotates plane `r`.
* `PosRoot`: `ε_r − ε_s` (`plus = false`) and `ε_r + ε_s` (`plus = true`), `r < s`; root vectors
  `rootX α, rootY α` with `[J_q, X] = α_q Y`, `[J_q, Y] = −α_q X` (commutators, composition right to left).
  The complex eigenvectors are `X ∓ i Y`; the 24 roots `±ε_r ± ε_s` are the `±` of the 12 positive ones.
* The four Cartan generators and the 24 root vectors form a basis of `skewEnd` (`A4PlaneRot` adds
  the plane rotations and their conjugation action).

Bracket identities are stated as commutators `S * T - T * S` (Mathlib's commutator Lie bracket on
rings is only a local instance at this pin).
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality
open CKM.NativeFirstOrder (fixedSpace mem_fixedSpace)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Helper facts on the pairing -/

theorem rs_octDot_add_right (u x y : Octonion) : octDot u (x + y) = octDot u x + octDot u y := by
  rw [octDot_comm, octDot_add_left, octDot_comm x, octDot_comm y]

theorem rs_octDot_smul_right (r : ℝ) (u x : Octonion) : octDot u (r • x) = r * octDot u x := by
  rw [octDot_comm, octDot_smul_left, octDot_comm]

theorem rs_octDot_sub_right (u x y : Octonion) : octDot u (x - y) = octDot u x - octDot u y := by
  simp only [← octDotForm_apply, map_sub]

theorem rs_octDot_sub_left (x y z : Octonion) : octDot (x - y) z = octDot x z - octDot y z := by
  simp only [← octDotForm_apply, map_sub, LinearMap.sub_apply]

/-- First and second coordinate of plane `r`. -/
def planeFst (r : Fin 4) : Fin 8 := ⟨2 * r.val, by omega⟩
def planeSnd (r : Fin 4) : Fin 8 := ⟨2 * r.val + 1, by omega⟩

theorem planeFst_inj {q r : Fin 4} : planeFst q = planeFst r ↔ q = r := by
  constructor
  · intro h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 2 * q.val = 2 * r.val at h'
    omega
  · rintro rfl
    rfl

theorem planeSnd_inj {q r : Fin 4} : planeSnd q = planeSnd r ↔ q = r := by
  constructor
  · intro h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 2 * q.val + 1 = 2 * r.val + 1 at h'
    omega
  · rintro rfl
    rfl

theorem planeFst_ne_planeSnd (q r : Fin 4) : planeFst q ≠ planeSnd r := by
  intro h
  have h' := congrArg Fin.val h
  change 2 * q.val = 2 * r.val + 1 at h'
  omega

theorem exists_plane (i : Fin 8) : ∃ r : Fin 4, i = planeFst r ∨ i = planeSnd r := by
  refine ⟨⟨i.val / 2, by omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one i.val with h | h
  · left
    apply Fin.ext
    show i.val = 2 * (i.val / 2)
    omega
  · right
    apply Fin.ext
    show i.val = 2 * (i.val / 2) + 1
    omega

theorem dot_FF (q r : Fin 4) :
    octDot (octBasis (planeFst q)) (octBasis (planeFst r)) = if q = r then 1 else 0 := by
  rw [octDot_octBasis]
  simp only [planeFst_inj]

theorem dot_GG (q r : Fin 4) :
    octDot (octBasis (planeSnd q)) (octBasis (planeSnd r)) = if q = r then 1 else 0 := by
  rw [octDot_octBasis]
  simp only [planeSnd_inj]

theorem dot_FG (q r : Fin 4) : octDot (octBasis (planeFst q)) (octBasis (planeSnd r)) = 0 := by
  rw [octDot_octBasis, ite_eq_right (planeFst_ne_planeSnd q r)]

theorem dot_GF (q r : Fin 4) : octDot (octBasis (planeSnd q)) (octBasis (planeFst r)) = 0 := by
  rw [octDot_octBasis, ite_eq_right (planeFst_ne_planeSnd r q).symm]

/-- The bivector map `u ∧ v : x ↦ ⟨v, x⟩ u − ⟨u, x⟩ v`. -/
def wedge (u v : Octonion) : Module.End ℝ Octonion where
  toFun x := octDot v x • u - octDot u x • v
  map_add' x y := by
    simp only [rs_octDot_add_right]
    module
  map_smul' r x := by
    simp only [rs_octDot_smul_right, RingHom.id_apply]
    module

theorem wedge_apply (u v x : Octonion) : wedge u v x = octDot v x • u - octDot u x • v := rfl

theorem wedge_mem_skewEnd (u v : Octonion) : wedge u v ∈ skewEnd := by
  refine mem_skewEnd_iff.2 fun x y => ?_
  rw [wedge_apply, wedge_apply, octDot_lin_left, octDot_comm x, octDot_lin_left]
  ring

/-! ### Wedge algebra (helpers) -/

theorem wedge_swap (u v : Octonion) : wedge u v = -wedge v u := by
  apply LinearMap.ext
  intro x
  simp only [wedge_apply, LinearMap.neg_apply]
  abel

theorem wedge_self (u : Octonion) : wedge u u = 0 := by
  apply LinearMap.ext
  intro x
  simp only [wedge_apply, sub_self, LinearMap.zero_apply]

/-- The `so(8)` commutator of two bivector maps. -/
theorem wedge_mul_sub (u v w z : Octonion) :
    wedge u v * wedge w z - wedge w z * wedge u v =
      octDot v w • wedge u z - octDot u w • wedge v z - octDot v z • wedge u w +
        octDot u z • wedge v w := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    wedge_apply, rs_octDot_sub_right, rs_octDot_smul_right]
  rw [octDot_comm z u, octDot_comm z v, octDot_comm w u, octDot_comm w v]
  module

/-- The rotation generator of plane `r`: `e_{2r} ↦ e_{2r+1}`, `e_{2r+1} ↦ −e_{2r}`. -/
def cartanGen (r : Fin 4) : Module.End ℝ Octonion :=
  wedge (octBasis (planeSnd r)) (octBasis (planeFst r))

/-- Positive roots: `(r, s, plus)` with `r < s` is `ε_r + ε_s` if `plus`, else `ε_r − ε_s`. -/
abbrev PosRoot := {p : Fin 4 × Fin 4 × Bool // p.1 < p.2.1}

namespace PosRoot

abbrev r (α : PosRoot) : Fin 4 := α.1.1
abbrev s (α : PosRoot) : Fin 4 := α.1.2.1
abbrev plus (α : PosRoot) : Bool := α.1.2.2

/-- The weight vector of `α` in the orthonormal basis `ε₁, …, ε₄` (index `0, …, 3`). -/
def weight (α : PosRoot) : Fin 4 → ℤ := fun q =>
  (if q = α.r then 1 else 0) + (if q = α.s then (if α.plus then 1 else -1) else 0)

end PosRoot

/-- First root vector of the plane of `α`. -/
def rootX (α : PosRoot) : Module.End ℝ Octonion :=
  if α.plus then
    wedge (octBasis (planeFst α.r)) (octBasis (planeFst α.s)) -
      wedge (octBasis (planeSnd α.r)) (octBasis (planeSnd α.s))
  else
    wedge (octBasis (planeFst α.r)) (octBasis (planeFst α.s)) +
      wedge (octBasis (planeSnd α.r)) (octBasis (planeSnd α.s))

/-- Second root vector of the plane of `α`. -/
def rootY (α : PosRoot) : Module.End ℝ Octonion :=
  if α.plus then
    wedge (octBasis (planeFst α.r)) (octBasis (planeSnd α.s)) +
      wedge (octBasis (planeSnd α.r)) (octBasis (planeFst α.s))
  else
    wedge (octBasis (planeSnd α.r)) (octBasis (planeFst α.s)) -
      wedge (octBasis (planeFst α.r)) (octBasis (planeSnd α.s))

/-! ### Root-vector bookkeeping (helpers) -/

theorem rootX_of_minus {α : PosRoot} (h : α.plus = false) :
    rootX α = wedge (octBasis (planeFst α.r)) (octBasis (planeFst α.s))
      + wedge (octBasis (planeSnd α.r)) (octBasis (planeSnd α.s)) := by
  simp [rootX, h]

theorem rootX_of_plus {α : PosRoot} (h : α.plus = true) :
    rootX α = wedge (octBasis (planeFst α.r)) (octBasis (planeFst α.s))
      - wedge (octBasis (planeSnd α.r)) (octBasis (planeSnd α.s)) := by
  simp [rootX, h]

theorem rootY_of_minus {α : PosRoot} (h : α.plus = false) :
    rootY α = wedge (octBasis (planeSnd α.r)) (octBasis (planeFst α.s))
      - wedge (octBasis (planeFst α.r)) (octBasis (planeSnd α.s)) := by
  simp [rootY, h]

theorem rootY_of_plus {α : PosRoot} (h : α.plus = true) :
    rootY α = wedge (octBasis (planeFst α.r)) (octBasis (planeSnd α.s))
      + wedge (octBasis (planeSnd α.r)) (octBasis (planeFst α.s)) := by
  simp [rootY, h]

theorem weight_of_minus {α : PosRoot} (h : α.plus = false) (q : Fin 4) :
    ((α.weight q : ℤ) : ℝ) =
      (if q = α.r then (1 : ℝ) else 0) - (if q = α.s then (1 : ℝ) else 0) := by
  simp only [PosRoot.weight, h, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> norm_num

theorem weight_of_plus {α : PosRoot} (h : α.plus = true) (q : Fin 4) :
    ((α.weight q : ℤ) : ℝ) =
      (if q = α.r then (1 : ℝ) else 0) + (if q = α.s then (1 : ℝ) else 0) := by
  simp only [PosRoot.weight, h, ↓reduceIte]
  split_ifs <;> norm_num

theorem comm_add (J A B : Module.End ℝ Octonion) :
    J * (A + B) - (A + B) * J = (J * A - A * J) + (J * B - B * J) := by
  rw [mul_add, add_mul]
  abel

theorem comm_sub (J A B : Module.End ℝ Octonion) :
    J * (A - B) - (A - B) * J = (J * A - A * J) - (J * B - B * J) := by
  rw [mul_sub, sub_mul]
  abel

theorem cartan_FF (q r s : Fin 4) :
    cartanGen q * wedge (octBasis (planeFst r)) (octBasis (planeFst s))
      - wedge (octBasis (planeFst r)) (octBasis (planeFst s)) * cartanGen q =
      (if q = r then (1 : ℝ) else 0) • wedge (octBasis (planeSnd r)) (octBasis (planeFst s))
        - (if q = s then (1 : ℝ) else 0) • wedge (octBasis (planeSnd s)) (octBasis (planeFst r)) := by
  rw [cartanGen, wedge_mul_sub, dot_FF, dot_GF, dot_FF, dot_GF]
  rcases eq_or_ne q r with rfl | h1 <;> rcases eq_or_ne q s with rfl | h2 <;> simp [*]

theorem cartan_GG (q r s : Fin 4) :
    cartanGen q * wedge (octBasis (planeSnd r)) (octBasis (planeSnd s))
      - wedge (octBasis (planeSnd r)) (octBasis (planeSnd s)) * cartanGen q =
      -((if q = r then (1 : ℝ) else 0) • wedge (octBasis (planeFst r)) (octBasis (planeSnd s)))
        + (if q = s then (1 : ℝ) else 0) • wedge (octBasis (planeFst s)) (octBasis (planeSnd r)) := by
  rw [cartanGen, wedge_mul_sub, dot_FG, dot_GG, dot_FG, dot_GG]
  rcases eq_or_ne q r with rfl | h1 <;> rcases eq_or_ne q s with rfl | h2 <;> simp [*]

theorem cartan_GF (q r s : Fin 4) :
    cartanGen q * wedge (octBasis (planeSnd r)) (octBasis (planeFst s))
      - wedge (octBasis (planeSnd r)) (octBasis (planeFst s)) * cartanGen q =
      -((if q = r then (1 : ℝ) else 0) • wedge (octBasis (planeFst r)) (octBasis (planeFst s)))
        - (if q = s then (1 : ℝ) else 0) • wedge (octBasis (planeSnd s)) (octBasis (planeSnd r)) := by
  rw [cartanGen, wedge_mul_sub, dot_FG, dot_GG, dot_FF, dot_GF]
  rcases eq_or_ne q r with rfl | h1 <;> rcases eq_or_ne q s with rfl | h2 <;> simp [*]

theorem cartan_FG (q r s : Fin 4) :
    cartanGen q * wedge (octBasis (planeFst r)) (octBasis (planeSnd s))
      - wedge (octBasis (planeFst r)) (octBasis (planeSnd s)) * cartanGen q =
      (if q = r then (1 : ℝ) else 0) • wedge (octBasis (planeSnd r)) (octBasis (planeSnd s))
        + (if q = s then (1 : ℝ) else 0) • wedge (octBasis (planeFst s)) (octBasis (planeFst r)) := by
  rw [cartanGen, wedge_mul_sub, dot_FF, dot_GF, dot_FG, dot_GG]
  rcases eq_or_ne q r with rfl | h1 <;> rcases eq_or_ne q s with rfl | h2 <;> simp [*]

theorem cartanGen_mem (q : Fin 4) : cartanGen q ∈ skewEnd := wedge_mem_skewEnd _ _
theorem rootX_mem (α : PosRoot) : rootX α ∈ skewEnd := by
  unfold rootX
  split_ifs
  · exact sub_mem (wedge_mem_skewEnd _ _) (wedge_mem_skewEnd _ _)
  · exact add_mem (wedge_mem_skewEnd _ _) (wedge_mem_skewEnd _ _)
theorem rootY_mem (α : PosRoot) : rootY α ∈ skewEnd := by
  unfold rootY
  split_ifs
  · exact add_mem (wedge_mem_skewEnd _ _) (wedge_mem_skewEnd _ _)
  · exact sub_mem (wedge_mem_skewEnd _ _) (wedge_mem_skewEnd _ _)

theorem cartanGen_comm (q q' : Fin 4) : cartanGen q * cartanGen q' = cartanGen q' * cartanGen q := by
  rw [← sub_eq_zero]
  unfold cartanGen
  rw [wedge_mul_sub, dot_FG, dot_GG, dot_FF, dot_GF]
  rcases eq_or_ne q q' with rfl | h
  · simp [wedge_self]
  · simp [h]

/-- **Root relation, first vector**: `[J_q, X_α] = α_q Y_α`. -/
theorem cartan_rootX (q : Fin 4) (α : PosRoot) :
    cartanGen q * rootX α - rootX α * cartanGen q = ((α.weight q : ℤ) : ℝ) • rootY α := by
  cases hb : α.plus
  · rw [rootX_of_minus hb, rootY_of_minus hb, weight_of_minus hb, comm_add, cartan_FF, cartan_GG,
      wedge_swap (octBasis (planeSnd α.s)) (octBasis (planeFst α.r)),
      wedge_swap (octBasis (planeFst α.s)) (octBasis (planeSnd α.r))]
    module
  · rw [rootX_of_plus hb, rootY_of_plus hb, weight_of_plus hb, comm_sub, cartan_FF, cartan_GG,
      wedge_swap (octBasis (planeSnd α.s)) (octBasis (planeFst α.r)),
      wedge_swap (octBasis (planeFst α.s)) (octBasis (planeSnd α.r))]
    module

/-- **Root relation, second vector**: `[J_q, Y_α] = −α_q X_α`. -/
theorem cartan_rootY (q : Fin 4) (α : PosRoot) :
    cartanGen q * rootY α - rootY α * cartanGen q = -(((α.weight q : ℤ) : ℝ) • rootX α) := by
  cases hb : α.plus
  · rw [rootX_of_minus hb, rootY_of_minus hb, weight_of_minus hb, comm_sub, cartan_GF, cartan_FG,
      wedge_swap (octBasis (planeSnd α.s)) (octBasis (planeSnd α.r)),
      wedge_swap (octBasis (planeFst α.s)) (octBasis (planeFst α.r))]
    module
  · rw [rootX_of_plus hb, rootY_of_plus hb, weight_of_plus hb, comm_add, cartan_FG, cartan_GF,
      wedge_swap (octBasis (planeSnd α.s)) (octBasis (planeSnd α.r)),
      wedge_swap (octBasis (planeFst α.s)) (octBasis (planeFst α.r))]
    module

/-- Index of the 28-element root basis: four Cartan generators, then `X_α` (`false`), `Y_α` (`true`). -/
abbrev RootIndex := Fin 4 ⊕ (PosRoot × Bool)

def rootFamily : RootIndex → Module.End ℝ Octonion
  | .inl q => cartanGen q
  | .inr (α, false) => rootX α
  | .inr (α, true) => rootY α

/-! ### Spanning (helpers) -/

theorem cartanGen_mem_span (q : Fin 4) : cartanGen q ∈ Submodule.span ℝ (Set.range rootFamily) :=
  Submodule.subset_span ⟨.inl q, rfl⟩

theorem rootX_mem_span (α : PosRoot) : rootX α ∈ Submodule.span ℝ (Set.range rootFamily) :=
  Submodule.subset_span ⟨.inr (α, false), rfl⟩

theorem rootY_mem_span (α : PosRoot) : rootY α ∈ Submodule.span ℝ (Set.range rootFamily) :=
  Submodule.subset_span ⟨.inr (α, true), rfl⟩

theorem wedge_cross_mem_span {r s : Fin 4} (h : r < s) :
    wedge (octBasis (planeFst r)) (octBasis (planeFst s))
      ∈ Submodule.span ℝ (Set.range rootFamily) ∧
    wedge (octBasis (planeSnd r)) (octBasis (planeSnd s))
      ∈ Submodule.span ℝ (Set.range rootFamily) ∧
    wedge (octBasis (planeFst r)) (octBasis (planeSnd s))
      ∈ Submodule.span ℝ (Set.range rootFamily) ∧
    wedge (octBasis (planeSnd r)) (octBasis (planeFst s))
      ∈ Submodule.span ℝ (Set.range rootFamily) := by
  let am : PosRoot := ⟨(r, s, false), h⟩
  let ap : PosRoot := ⟨(r, s, true), h⟩
  have xm := rootX_of_minus (α := am) rfl
  have xp := rootX_of_plus (α := ap) rfl
  have ym := rootY_of_minus (α := am) rfl
  have yp := rootY_of_plus (α := ap) rfl
  have hX := add_mem (rootX_mem_span am) (rootX_mem_span ap)
  have hX' := sub_mem (rootX_mem_span am) (rootX_mem_span ap)
  have hY := add_mem (rootY_mem_span ap) (rootY_mem_span am)
  have hY' := sub_mem (rootY_mem_span ap) (rootY_mem_span am)
  rw [xm, xp] at hX hX'
  rw [ym, yp] at hY hY'
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) hX using 1
    module
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) hX' using 1
    module
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) hY' using 1
    module
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) hY using 1
    module

theorem wedge_octBasis_mem_span (i j : Fin 8) :
    wedge (octBasis i) (octBasis j) ∈ Submodule.span ℝ (Set.range rootFamily) := by
  obtain ⟨r, hr⟩ := exists_plane i
  obtain ⟨s, hs⟩ := exists_plane j
  rcases lt_trichotomy r s with h | rfl | h
  · obtain ⟨h1, h2, h3, h4⟩ := wedge_cross_mem_span h
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    exacts [h1, h3, h4, h2]
  · rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · rw [wedge_self]; exact Submodule.zero_mem _
    · rw [wedge_swap]; exact Submodule.neg_mem _ (cartanGen_mem_span r)
    · exact cartanGen_mem_span r
    · rw [wedge_self]; exact Submodule.zero_mem _
  · obtain ⟨h1, h2, h3, h4⟩ := wedge_cross_mem_span h
    rw [wedge_swap]
    refine Submodule.neg_mem _ ?_
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    exacts [h1, h4, h3, h2]

theorem elemRot_eq_wedge (i j : Fin 8) : elemRot i j = wedge (octBasis i) (octBasis j) :=
  LinearMap.ext fun _ => rfl

/-- A skew map is the combination of the elementary rotations with its upper entries. -/
theorem eq_sum_elemRot {T : Module.End ℝ Octonion} (hT : T ∈ skewEnd) :
    T = ∑ p : UpperPair, octDot (T (octBasis p.1.2)) (octBasis p.1.1) • elemRot p.1.1 p.1.2 := by
  set S := ∑ p : UpperPair, octDot (T (octBasis p.1.2)) (octBasis p.1.1) • elemRot p.1.1 p.1.2
    with hSdef
  have hS : S ∈ skewEnd :=
    Submodule.sum_mem octDotForm.skewAdjointSubmodule fun p _ =>
      Submodule.smul_mem octDotForm.skewAdjointSubmodule _ (elemRot_mem p.1.1 p.1.2)
  have hzero : T - S = 0 := by
    refine eq_zero_of_upper_entries (sub_mem hT hS) fun a b hab => ?_
    have key : ∀ q : UpperPair, octDot (S (octBasis q.1.2)) (octBasis q.1.1) =
        octDot (T (octBasis q.1.2)) (octBasis q.1.1) := by
      intro q
      rw [hSdef, LinearMap.sum_apply, octDot_sum_left]
      simp only [LinearMap.smul_apply, octDot_smul_left, elemRot_entry_upper, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [LinearMap.sub_apply, rs_octDot_sub_left, sub_eq_zero]
    exact (key ⟨(a, b), hab⟩).symm
  exact sub_eq_zero.1 hzero

theorem span_rootFamily_aux :
    Submodule.span ℝ (Set.range rootFamily) = skewEnd.toSubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases i with q | ⟨α, _ | _⟩
    · exact cartanGen_mem q
    · exact rootX_mem α
    · exact rootY_mem α
  · intro T hT
    rw [eq_sum_elemRot hT]
    refine Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_
    rw [elemRot_eq_wedge]
    exact wedge_octBasis_mem_span _ _

theorem card_rootIndex : Fintype.card RootIndex = 28 := by
  decide

theorem rootFamily_linearIndependent : LinearIndependent ℝ rootFamily := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, span_rootFamily_aux, card_rootIndex]
  exact finrank_skewEnd.symm

/-- The Cartan generators and root vectors span exactly the skew endomorphisms. -/
theorem span_rootFamily : Submodule.span ℝ (Set.range rootFamily) = skewEnd.toSubmodule := by
  exact span_rootFamily_aux

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.wedge
#print axioms CKM.NativeIntrinsicTriality.wedge_mem_skewEnd
#print axioms CKM.NativeIntrinsicTriality.cartanGen_mem
#print axioms CKM.NativeIntrinsicTriality.rootX_mem
#print axioms CKM.NativeIntrinsicTriality.rootY_mem
#print axioms CKM.NativeIntrinsicTriality.cartanGen_comm
#print axioms CKM.NativeIntrinsicTriality.cartan_rootX
#print axioms CKM.NativeIntrinsicTriality.cartan_rootY
#print axioms CKM.NativeIntrinsicTriality.rootFamily_linearIndependent
#print axioms CKM.NativeIntrinsicTriality.span_rootFamily

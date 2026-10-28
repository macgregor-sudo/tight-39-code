module

public import A4Torus

@[expose] public section

/-!
# The four pointwise factors and their hexagons

For each anchor subgroup `H`, `J^H` is the fixed algebra of its generator (A3's `anchorGenerator H`)
and `pointwiseFactor H` is the actual Lie algebra of native derivations vanishing on `J^H` (the
pointwise `su(3)` factor). It lies in `s`, is normalized by `t`, has dimension eight, meets `t` in
dimension two, and its root planes are exactly the labelled hexagon of `H`.

The factor of `H₀` is bound with weights `(ε₂, ε₃, −ε₄)`: on the three `R0`-moving planes of the
first cyclic slot `o12`, `R0` acts as `−1/2 − (√3/2) I` for the complex structure
`I = J₁ + J₂ − J₃`, and `t` acts there `I`-linearly with weights `(ε₂, ε₃, −ε₄)`; the hexagon of `H₀`
is the set of their differences. The other three factors are the transports of the first by A3's
signed transports `T₁, T₂, T₃` (`transportT 0, 1, 2`).

Intended route: explicit related triples for the 28 root-basis elements (their first and third
components are signed root vectors / half-sums of plane rotations; see the numeric notes), verified
on the octonion basis, give the `o01` and `o02` components of `sRootX α`, `sRootY α`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Helpers: the octonion basis, plane-killing, explicit related triples -/

theorem pwf_obF0 : octBasis (planeFst 0) = (⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩) := rfl
theorem pwf_obS0 : octBasis (planeSnd 0) = (⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩) := rfl
theorem pwf_obF1 : octBasis (planeFst 1) = (⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩) := rfl
theorem pwf_obS1 : octBasis (planeSnd 1) = (⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 0⟩) := rfl
theorem pwf_obF2 : octBasis (planeFst 2) = (⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩) := rfl
theorem pwf_obS2 : octBasis (planeSnd 2) = (⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩) := rfl
theorem pwf_obF3 : octBasis (planeFst 3) = (⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩) := rfl
theorem pwf_obS3 : octBasis (planeSnd 3) = (⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 1⟩) := rfl

theorem pwf_planeFst_inj {p q : Fin 4} : planeFst p = planeFst q ↔ p = q := by
  simp [planeFst, Fin.ext_iff]

theorem pwf_planeSnd_inj {p q : Fin 4} : planeSnd p = planeSnd q ↔ p = q := by
  simp [planeSnd, Fin.ext_iff]

theorem pwf_planeFst_ne_planeSnd (p q : Fin 4) : planeFst p ≠ planeSnd q := by
  simp only [planeFst, planeSnd, ne_eq, Fin.ext_iff]
  omega

theorem pwf_planeSnd_ne_planeFst (p q : Fin 4) : planeSnd p ≠ planeFst q := fun h =>
  pwf_planeFst_ne_planeSnd q p h.symm

theorem pwf_octDot_zero_right' (u : Octonion) : octDot u 0 = 0 := by
  rw [octDot_coordinates]; simp

theorem pwf_octBasis_ne_zero (k : Fin 8) : octBasis k ≠ 0 := by
  intro h
  have := octDot_octBasis k k
  rw [h, pwf_octDot_zero_right'] at this
  simp at this

theorem PosRoot.pwf_r_ne_s (β : PosRoot) : β.r ≠ β.s := ne_of_lt β.2

/-- `S` kills both basis vectors of the coordinate plane `p`. -/
def PwfKillsPlane (S : Module.End ℝ Octonion) (p : Fin 4) : Prop :=
  S (octBasis (planeFst p)) = 0 ∧ S (octBasis (planeSnd p)) = 0

theorem PwfKillsPlane.smul {S : Module.End ℝ Octonion} {p : Fin 4} (h : PwfKillsPlane S p) (c : ℝ) :
    PwfKillsPlane (c • S) p := by
  refine ⟨?_, ?_⟩ <;> simp [h.1, h.2]

theorem pwf_rootX_kills (β : PosRoot) (p : Fin 4) (hr : p ≠ β.r) (hs : p ≠ β.s) : PwfKillsPlane (rootX β) p := by
  have h1 : β.r ≠ p := Ne.symm hr
  have h2 : β.s ≠ p := Ne.symm hs
  unfold rootX
  split_ifs <;> refine ⟨?_, ?_⟩ <;>
    simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeFst_inj, pwf_planeSnd_inj, pwf_planeFst_ne_planeSnd,
      pwf_planeSnd_ne_planeFst, h1, h2]

theorem pwf_rootX_planeFst_r (β : PosRoot) :
    rootX β (octBasis (planeFst β.r)) = -octBasis (planeFst β.s) := by
  have h : β.s ≠ β.r := (PosRoot.pwf_r_ne_s β).symm
  unfold rootX
  split_ifs <;>
    simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeFst_inj, pwf_planeSnd_ne_planeFst, h]

theorem pwf_rootX_planeFst_s (β : PosRoot) :
    rootX β (octBasis (planeFst β.s)) = octBasis (planeFst β.r) := by
  have h : β.r ≠ β.s := PosRoot.pwf_r_ne_s β
  unfold rootX
  split_ifs <;>
    simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeFst_inj, pwf_planeSnd_ne_planeFst, h]

theorem pwf_rootX_not_kills (β : PosRoot) (p : Fin 4) (hp : p = β.r ∨ p = β.s) {c : ℝ} (hc : c ≠ 0) :
    ¬ PwfKillsPlane (c • rootX β) p := by
  rintro ⟨h1, -⟩
  rcases hp with rfl | rfl
  · rw [LinearMap.smul_apply, pwf_rootX_planeFst_r] at h1
    exact smul_ne_zero hc (neg_ne_zero.mpr (pwf_octBasis_ne_zero _)) h1
  · rw [LinearMap.smul_apply, pwf_rootX_planeFst_s] at h1
    exact smul_ne_zero hc (pwf_octBasis_ne_zero _) h1

theorem pwf_cartanGen_planeFst (q p : Fin 4) :
    cartanGen q (octBasis (planeFst p)) = if q = p then octBasis (planeSnd q) else 0 := by
  unfold cartanGen
  by_cases h : q = p
  · subst h; simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeSnd_ne_planeFst]
  · simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeSnd_ne_planeFst, pwf_planeFst_inj, h]

theorem pwf_cartanGen_planeSnd (q p : Fin 4) :
    cartanGen q (octBasis (planeSnd p)) = if q = p then -octBasis (planeFst q) else 0 := by
  unfold cartanGen
  by_cases h : q = p
  · subst h; simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeFst_ne_planeSnd]
  · simp [-octDot_self, wedge_apply, octDot_octBasis, pwf_planeFst_ne_planeSnd, pwf_planeSnd_inj, h]

theorem pwf_combo_planeFst (d : Fin 4 → ℝ) (p : Fin 4) :
    (∑ q, d q • cartanGen q) (octBasis (planeFst p)) = d p • octBasis (planeSnd p) := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, pwf_cartanGen_planeFst, smul_ite, smul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem pwf_combo_planeSnd (d : Fin 4 → ℝ) (p : Fin 4) :
    (∑ q, d q • cartanGen q) (octBasis (planeSnd p)) = -(d p • octBasis (planeFst p)) := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, pwf_cartanGen_planeSnd, smul_ite, smul_zero, smul_neg]
  rw [Finset.sum_ite_eq']
  simp

theorem pwf_killsPlane_combo (d : Fin 4 → ℝ) (p : Fin 4) :
    PwfKillsPlane (∑ q, d q • cartanGen q) p ↔ d p = 0 := by
  unfold PwfKillsPlane
  rw [pwf_combo_planeFst, pwf_combo_planeSnd]
  constructor
  · rintro ⟨h, -⟩
    by_contra hd
    exact smul_ne_zero hd (pwf_octBasis_ne_zero _) h
  · intro h
    simp [h]

/-! ### Tables of the related partners of the root vectors -/

/-- A positive root from its data. -/
abbrev pwf_pr (r s : Fin 4) (b : Bool) (h : r < s := by decide) : PosRoot := ⟨(r, s, b), h⟩

/-- Dummy entry for unused table slots. -/
def pwf_rawD : Fin 4 × Fin 4 × Bool := (0, 1, false)

/-- Root of the first partner `A` of `X_α` (`A = sgnA • X_{pwf_permA α}`). -/
def pwf_permARaw (r s : Fin 4) (b : Bool) : Fin 4 × Fin 4 × Bool :=
  if b then
    ![![pwf_rawD, (0, 1, false), (0, 2, false), (1, 2, true)], ![pwf_rawD, pwf_rawD, (0, 3, false), (1, 3, true)],
      ![pwf_rawD, pwf_rawD, pwf_rawD, (2, 3, true)], ![pwf_rawD, pwf_rawD, pwf_rawD, pwf_rawD]] r s
  else
    ![![pwf_rawD, (2, 3, false), (1, 3, false), (0, 3, true)], ![pwf_rawD, pwf_rawD, (1, 2, false), (0, 2, true)],
      ![pwf_rawD, pwf_rawD, pwf_rawD, (0, 1, true)], ![pwf_rawD, pwf_rawD, pwf_rawD, pwf_rawD]] r s

/-- Root of the third partner `C` of `X_α` (`C = sgnC • X_{pwf_permC α}`). -/
def pwf_permCRaw (r s : Fin 4) (b : Bool) : Fin 4 × Fin 4 × Bool :=
  if b then
    ![![pwf_rawD, (2, 3, false), (1, 3, false), (0, 3, true)], ![pwf_rawD, pwf_rawD, (0, 3, false), (1, 3, true)],
      ![pwf_rawD, pwf_rawD, pwf_rawD, (2, 3, true)], ![pwf_rawD, pwf_rawD, pwf_rawD, pwf_rawD]] r s
  else
    ![![pwf_rawD, (0, 1, false), (0, 2, false), (1, 2, true)], ![pwf_rawD, pwf_rawD, (1, 2, false), (0, 2, true)],
      ![pwf_rawD, pwf_rawD, pwf_rawD, (0, 1, true)], ![pwf_rawD, pwf_rawD, pwf_rawD, pwf_rawD]] r s

def pwf_sgnARaw (r s : Fin 4) (b : Bool) : ℤ :=
  if b then ![![0, -1, -1, 1], ![0, 0, -1, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]] r s
  else ![![0, 1, -1, -1], ![0, 0, 1, 1], ![0, 0, 0, -1], ![0, 0, 0, 0]] r s

def pwf_sgnCRaw (r s : Fin 4) (b : Bool) : ℤ :=
  if b then ![![0, -1, 1, 1], ![0, 0, -1, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]] r s
  else ![![0, 1, 1, -1], ![0, 0, 1, 1], ![0, 0, 0, -1], ![0, 0, 0, 0]] r s

theorem pwf_permA_lt : ∀ α : PosRoot, (pwf_permARaw α.r α.s α.plus).1 < (pwf_permARaw α.r α.s α.plus).2.1 := by
  decide

theorem pwf_permC_lt : ∀ α : PosRoot, (pwf_permCRaw α.r α.s α.plus).1 < (pwf_permCRaw α.r α.s α.plus).2.1 := by
  decide

theorem pwf_sgnA_ne_zero : ∀ α : PosRoot, pwf_sgnARaw α.r α.s α.plus ≠ 0 := by decide

theorem pwf_sgnC_ne_zero : ∀ α : PosRoot, pwf_sgnCRaw α.r α.s α.plus ≠ 0 := by decide

def pwf_permA (α : PosRoot) : PosRoot := ⟨pwf_permARaw α.r α.s α.plus, pwf_permA_lt α⟩
def pwf_permC (α : PosRoot) : PosRoot := ⟨pwf_permCRaw α.r α.s α.plus, pwf_permC_lt α⟩

/-- The `o01` partner of `X_α`. -/
def pwf_tripleXA (α : PosRoot) : Module.End ℝ Octonion := ((pwf_sgnARaw α.r α.s α.plus : ℤ) : ℝ) • rootX (pwf_permA α)
/-- The `o02` partner of `X_α`. -/
def pwf_tripleXC (α : PosRoot) : Module.End ℝ Octonion := ((pwf_sgnCRaw α.r α.s α.plus : ℤ) : ℝ) • rootX (pwf_permC α)

/-- Partner matrices of the Cartan generators: `J_q ↦ (Σ PwfMA q q' / 2 J_q', J_q, Σ PwfMC q q' / 2 J_q')`. -/
def PwfMA : Fin 4 → Fin 4 → ℝ := ![![-1, 1, 1, -1], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![1, 1, 1, 1]]
def PwfMC : Fin 4 → Fin 4 → ℝ := ![![1, -1, -1, 1], ![-1, 1, -1, 1], ![-1, -1, 1, 1], ![1, 1, 1, 1]]

def pwf_cartanA (q : Fin 4) : Module.End ℝ Octonion := ∑ q', (PwfMA q q' / 2) • cartanGen q'
def pwf_cartanC (q : Fin 4) : Module.End ℝ Octonion := ∑ q', (PwfMC q q' / 2) • cartanGen q'

/-- Componentwise verification of an octonion identity through the two quaternion halves. -/
macro "pwf_oct_ident" : tactic => `(tactic| (
  intro x y
  obtain ⟨⟨x0, x1, x2, x3⟩, ⟨x4, x5, x6, x7⟩⟩ := x
  obtain ⟨⟨y0, y1, y2, y3⟩, ⟨y4, y5, y6, y7⟩⟩ := y
  simp only [pwf_tripleXA, pwf_tripleXC, pwf_permA, pwf_permC, pwf_permARaw, pwf_permCRaw, pwf_sgnARaw, pwf_sgnCRaw, PosRoot.r, PosRoot.s,
    PosRoot.plus, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, rootX, rootY, cartanGen,
    pwf_cartanA, pwf_cartanC, PwfMA, PwfMC, Fin.sum_univ_four,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, wedge_apply,
    pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates, octMul]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, wedge_apply,
      pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates] <;> ring))

theorem pwf_tx01f : ∀ x y, pwf_tripleXC (pwf_pr 0 1 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 1 false) x) y + octMul x (rootX (pwf_pr 0 1 false) y) := by pwf_oct_ident
theorem pwf_tx01t : ∀ x y, pwf_tripleXC (pwf_pr 0 1 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 1 true) x) y + octMul x (rootX (pwf_pr 0 1 true) y) := by pwf_oct_ident
theorem pwf_tx02f : ∀ x y, pwf_tripleXC (pwf_pr 0 2 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 2 false) x) y + octMul x (rootX (pwf_pr 0 2 false) y) := by pwf_oct_ident
theorem pwf_tx02t : ∀ x y, pwf_tripleXC (pwf_pr 0 2 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 2 true) x) y + octMul x (rootX (pwf_pr 0 2 true) y) := by pwf_oct_ident
theorem pwf_tx03f : ∀ x y, pwf_tripleXC (pwf_pr 0 3 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 3 false) x) y + octMul x (rootX (pwf_pr 0 3 false) y) := by pwf_oct_ident
theorem pwf_tx03t : ∀ x y, pwf_tripleXC (pwf_pr 0 3 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 0 3 true) x) y + octMul x (rootX (pwf_pr 0 3 true) y) := by pwf_oct_ident
theorem pwf_tx12f : ∀ x y, pwf_tripleXC (pwf_pr 1 2 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 1 2 false) x) y + octMul x (rootX (pwf_pr 1 2 false) y) := by pwf_oct_ident
theorem pwf_tx12t : ∀ x y, pwf_tripleXC (pwf_pr 1 2 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 1 2 true) x) y + octMul x (rootX (pwf_pr 1 2 true) y) := by pwf_oct_ident
theorem pwf_tx13f : ∀ x y, pwf_tripleXC (pwf_pr 1 3 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 1 3 false) x) y + octMul x (rootX (pwf_pr 1 3 false) y) := by pwf_oct_ident
theorem pwf_tx13t : ∀ x y, pwf_tripleXC (pwf_pr 1 3 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 1 3 true) x) y + octMul x (rootX (pwf_pr 1 3 true) y) := by pwf_oct_ident
theorem pwf_tx23f : ∀ x y, pwf_tripleXC (pwf_pr 2 3 false) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 2 3 false) x) y + octMul x (rootX (pwf_pr 2 3 false) y) := by pwf_oct_ident
theorem pwf_tx23t : ∀ x y, pwf_tripleXC (pwf_pr 2 3 true) (octMul x y) =
    octMul (pwf_tripleXA (pwf_pr 2 3 true) x) y + octMul x (rootX (pwf_pr 2 3 true) y) := by pwf_oct_ident

theorem pwf_tc0 : ∀ x y, pwf_cartanC 0 (octMul x y) = octMul (pwf_cartanA 0 x) y + octMul x (cartanGen 0 y) := by
  pwf_oct_ident
theorem pwf_tc1 : ∀ x y, pwf_cartanC 1 (octMul x y) = octMul (pwf_cartanA 1 x) y + octMul x (cartanGen 1 y) := by
  pwf_oct_ident
theorem pwf_tc2 : ∀ x y, pwf_cartanC 2 (octMul x y) = octMul (pwf_cartanA 2 x) y + octMul x (cartanGen 2 y) := by
  pwf_oct_ident
theorem pwf_tc3 : ∀ x y, pwf_cartanC 3 (octMul x y) = octMul (pwf_cartanA 3 x) y + octMul x (cartanGen 3 y) := by
  pwf_oct_ident

theorem pwf_tripleX_ident (α : PosRoot) (x y : Octonion) :
    pwf_tripleXC α (octMul x y) = octMul (pwf_tripleXA α x) y + octMul x (rootX α y) := by
  obtain ⟨⟨r, s, b⟩, h⟩ := α
  fin_cases r <;> fin_cases s <;> cases b
  all_goals first | exact absurd h (by decide) | skip
  exacts [pwf_tx01f x y, pwf_tx01t x y, pwf_tx02f x y, pwf_tx02t x y, pwf_tx03f x y, pwf_tx03t x y, pwf_tx12f x y, pwf_tx12t x y,
    pwf_tx13f x y, pwf_tx13t x y, pwf_tx23f x y, pwf_tx23t x y]

theorem pwf_cartan_ident (q : Fin 4) (x y : Octonion) :
    pwf_cartanC q (octMul x y) = octMul (pwf_cartanA q x) y + octMul x (cartanGen q y) := by
  fin_cases q
  · exact pwf_tc0 x y
  · exact pwf_tc1 x y
  · exact pwf_tc2 x y
  · exact pwf_tc3 x y

/-- The related triple of the root vector `X_α` (order `(A, B, C)` on `(o01, o12, o02)`). -/
def pwf_tripleX (α : PosRoot) : EndTriple := (pwf_tripleXA α, rootX α, pwf_tripleXC α)

theorem pwf_tripleX_related (α : PosRoot) : IsRelatedTriple (pwf_tripleX α) :=
  ⟨skewEnd.smul_mem _ (rootX_mem _), rootX_mem α, skewEnd.smul_mem _ (rootX_mem _), pwf_tripleX_ident α⟩

theorem pwf_cartanCombo_mem (d : Fin 4 → ℝ) : ∑ q, d q • cartanGen q ∈ skewEnd :=
  skewEnd.toSubmodule.sum_mem fun q _ => skewEnd.smul_mem _ (cartanGen_mem q)

/-- The related triple of the Cartan generator `J_q`. -/
def pwf_cartanTriple (q : Fin 4) : EndTriple := (pwf_cartanA q, cartanGen q, pwf_cartanC q)

theorem pwf_cartanTriple_related (q : Fin 4) : IsRelatedTriple (pwf_cartanTriple q) :=
  ⟨pwf_cartanCombo_mem _, cartanGen_mem q, pwf_cartanCombo_mem _, pwf_cartan_ident q⟩

/-! ### From related triples to the actual diagonal fixer -/

theorem pwf_psi_symm_eq_extend {t : EndTriple} (ht : IsRelatedTriple t) :
    ((psi.symm ⟨t.2.1, ht.2.1⟩ : diagonalFixer) : Module.End ℝ Albert) = extendTriple t := by
  have hmem : extendTriple t ∈ diagonalFixer := extendTriple_mem ht
  have hpsi : psi ⟨extendTriple t, hmem⟩ = ⟨t.2.1, ht.2.1⟩ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    rw [psi_apply]
    rfl
  rw [← hpsi, LieEquiv.symm_apply_apply]

theorem pwf_sRootX_eq (α : PosRoot) : (sRootX α : Module.End ℝ Albert) = extendTriple (pwf_tripleX α) :=
  pwf_psi_symm_eq_extend (pwf_tripleX_related α)

/-- The Cartan element of `s` with `psi`-image `J_q`. -/
def pwf_hq (q : Fin 4) : diagonalFixer := psi.symm ⟨cartanGen q, cartanGen_mem q⟩

theorem pwf_hq_eq (q : Fin 4) : (pwf_hq q : Module.End ℝ Albert) = extendTriple (pwf_cartanTriple q) :=
  pwf_psi_symm_eq_extend (pwf_cartanTriple_related q)

theorem pwf_psi_hq (q : Fin 4) : ((psi (pwf_hq q) : skewEnd) : Module.End ℝ Octonion) = cartanGen q := by
  simp [pwf_hq]

theorem pwf_hq_mem (q : Fin 4) : (pwf_hq q : Module.End ℝ Albert) ∈ commonCartan := by
  rw [psi_mem_commonCartan_iff, pwf_psi_hq]
  exact Submodule.subset_span ⟨q, rfl⟩

theorem pwf_cartanWeight_apply' (r : Fin 4) (D : Module.End ℝ Albert) :
    cartanWeight r D = octDot (octBasis (planeSnd r)) (D (slot12 (octBasis (planeFst r)))).o12 := rfl

theorem pwf_cartanWeight_hq (q q' : Fin 4) : cartanWeight q' (pwf_hq q : Module.End ℝ Albert) = if q = q' then 1 else 0 := by
  rw [pwf_cartanWeight_apply', ← psi_apply, pwf_psi_hq, pwf_cartanGen_planeFst]
  by_cases h : q = q'
  · subst h; simp [-octDot_self, octDot_octBasis]
  · simp [h, pwf_octDot_zero_right']

theorem pwf_rootEval_hq (α : PosRoot) (q : Fin 4) : rootEval α (pwf_hq q) = ((α.weight q : ℤ) : ℝ) := by
  simp only [rootEval, pwf_cartanWeight_hq, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-! ### Cube roots of unity and the fixed vectors of slot rotations -/

theorem pwf_omega_eq : ω = ⟨-1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext <;> simp [ω, UnitaryErrorBases.ThreeCycleFourier.omega]

theorem pwf_omega_re : ω.re = -1 / 2 := by rw [pwf_omega_eq]
theorem pwf_omega_im : ω.im = Real.sqrt 3 / 2 := by rw [pwf_omega_eq]

theorem pwf_omega_sq_eq : ω ^ 2 = ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩ := by
  rw [show ω ^ 2 = -1 - ω from UnitaryErrorBases.ThreeCycleFourier.omega_sq, pwf_omega_eq]
  apply Complex.ext <;> norm_num

theorem pwf_omega_sq_re : (ω ^ 2).re = -1 / 2 := by rw [pwf_omega_sq_eq]
theorem pwf_omega_sq_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by rw [pwf_omega_sq_eq]

theorem pwf_omega_pow_mod (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, UnitaryErrorBases.ThreeCycleFourier.omega_cube,
    one_pow, one_mul]

theorem pwf_sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem pwf_omega_pow_moving {n : ℕ} (hn : n % 3 ≠ 0) :
    (ω ^ n).re = -1 / 2 ∧ (ω ^ n).im ^ 2 = 3 / 4 := by
  rw [pwf_omega_pow_mod]
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h <;> rw [h]
  · rw [pow_one, pwf_omega_re, pwf_omega_im]; constructor; rfl; rw [div_pow, pwf_sqrt3_sq]; norm_num
  · rw [pwf_omega_sq_re, pwf_omega_sq_im]; constructor; rfl; rw [neg_sq, div_pow, pwf_sqrt3_sq]; norm_num

theorem pwf_omega_pow_fixed {n : ℕ} (hn : n % 3 = 0) : ω ^ n = 1 := by
  rw [pwf_omega_pow_mod, hn, pow_zero]

theorem pwf_planeRot_apply' (z : Fin 4 → ℂ) (x : Octonion) :
    planeRot z x =
    (⟨(z 0).re * x.1.re - (z 0).im * x.1.imI, (z 0).im * x.1.re + (z 0).re * x.1.imI,
      (z 1).re * x.1.imJ - (z 1).im * x.1.imK, (z 1).im * x.1.imJ + (z 1).re * x.1.imK⟩,
     ⟨(z 2).re * x.2.re - (z 2).im * x.2.imI, (z 2).im * x.2.re + (z 2).re * x.2.imI,
      (z 3).re * x.2.imJ - (z 3).im * x.2.imK, (z 3).im * x.2.imJ + (z 3).re * x.2.imK⟩) := rfl

theorem pwf_octDot_F_planeRot (z : Fin 4 → ℂ) (r : Fin 4) (x : Octonion) :
    octDot (octBasis (planeFst r)) (planeRot z x) =
      (z r).re * octDot (octBasis (planeFst r)) x - (z r).im * octDot (octBasis (planeSnd r)) x := by
  fin_cases r <;>
    simp [Fin.reduceFinMk, pwf_planeRot_apply', pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates]

theorem pwf_octDot_S_planeRot (z : Fin 4 → ℂ) (r : Fin 4) (x : Octonion) :
    octDot (octBasis (planeSnd r)) (planeRot z x) =
      (z r).im * octDot (octBasis (planeFst r)) x + (z r).re * octDot (octBasis (planeSnd r)) x := by
  fin_cases r <;>
    simp [Fin.reduceFinMk, pwf_planeRot_apply', pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates]

/-- A slot rotation fixes no nonzero vector of a plane whose exponent is not divisible by three. -/
theorem pwf_fixed_coords {e : Fin 4 → ℕ} {x : Octonion} (hx : planeRot (omegaPow e) x = x) {r : Fin 4}
    (hr : e r % 3 ≠ 0) :
    octDot (octBasis (planeFst r)) x = 0 ∧ octDot (octBasis (planeSnd r)) x = 0 := by
  obtain ⟨hre, him⟩ := pwf_omega_pow_moving hr
  have h1 := pwf_octDot_F_planeRot (omegaPow e) r x
  have h2 := pwf_octDot_S_planeRot (omegaPow e) r x
  rw [hx] at h1 h2
  simp only [omegaPow] at h1 h2
  rw [hre] at h1 h2
  set u := octDot (octBasis (planeFst r)) x
  set v := octDot (octBasis (planeSnd r)) x
  set t := (ω ^ e r).im
  have hv : v = 0 := by linear_combination (t / 3) * h1 + (1 / 2) * h2 - (v / 3) * him
  refine ⟨?_, hv⟩
  rw [hv] at h1
  linear_combination (2 / 3) * h1

theorem pwf_planeRot_planeFst_fixed {e : Fin 4 → ℕ} {p : Fin 4} (hp : e p % 3 = 0) :
    planeRot (omegaPow e) (octBasis (planeFst p)) = octBasis (planeFst p) := by
  rw [planeRot_planeFst]
  simp [omegaPow, pwf_omega_pow_fixed hp]

theorem pwf_planeRot_planeSnd_fixed {e : Fin 4 → ℕ} {p : Fin 4} (hp : e p % 3 = 0) :
    planeRot (omegaPow e) (octBasis (planeSnd p)) = octBasis (planeSnd p) := by
  rw [planeRot_planeSnd]
  simp [omegaPow, pwf_omega_pow_fixed hp]

/-- A fixed vector of a slot rotation with exactly one fixed plane `p` lies in that plane. -/
theorem pwf_fixed_decomp {e : Fin 4 → ℕ} {p : Fin 4} (he : ∀ r, r ≠ p → e r % 3 ≠ 0) {x : Octonion}
    (hx : planeRot (omegaPow e) x = x) :
    x = octDot (octBasis (planeFst p)) x • octBasis (planeFst p) +
      octDot (octBasis (planeSnd p)) x • octBasis (planeSnd p) := by
  have hc : ∀ r, r ≠ p → octDot (octBasis (planeFst r)) x = 0 ∧ octDot (octBasis (planeSnd r)) x = 0 :=
    fun r hr => pwf_fixed_coords hx (he r hr)
  obtain ⟨⟨x0, x1, x2, x3⟩, ⟨x4, x5, x6, x7⟩⟩ := x
  fin_cases p <;> simp only [Fin.reduceFinMk] at hc ⊢
  · obtain ⟨a1, b1⟩ := hc 1 (by decide)
    obtain ⟨a2, b2⟩ := hc 2 (by decide)
    obtain ⟨a3, b3⟩ := hc 3 (by decide)
    simp [pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates] at a1 b1 a2 b2 a3 b3 ⊢
    clear hx he hc; simp_all
  · obtain ⟨a1, b1⟩ := hc 0 (by decide)
    obtain ⟨a2, b2⟩ := hc 2 (by decide)
    obtain ⟨a3, b3⟩ := hc 3 (by decide)
    simp [pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates] at a1 b1 a2 b2 a3 b3 ⊢
    clear hx he hc; simp_all
  · obtain ⟨a1, b1⟩ := hc 0 (by decide)
    obtain ⟨a2, b2⟩ := hc 1 (by decide)
    obtain ⟨a3, b3⟩ := hc 3 (by decide)
    simp [pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates] at a1 b1 a2 b2 a3 b3 ⊢
    clear hx he hc; simp_all
  · obtain ⟨a1, b1⟩ := hc 0 (by decide)
    obtain ⟨a2, b2⟩ := hc 1 (by decide)
    obtain ⟨a3, b3⟩ := hc 2 (by decide)
    simp [pwf_obF0, pwf_obS0, pwf_obF1, pwf_obS1, pwf_obF2, pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates] at a1 b1 a2 b2 a3 b3 ⊢
    clear hx he hc; simp_all

theorem PwfKillsPlane.apply_of_fixed {S : Module.End ℝ Octonion} {p : Fin 4} (hS : PwfKillsPlane S p)
    {e : Fin 4 → ℕ} (he : ∀ r, r ≠ p → e r % 3 ≠ 0) {x : Octonion}
    (hx : planeRot (omegaPow e) x = x) : S x = 0 := by
  rw [pwf_fixed_decomp he hx, map_add, map_smul, map_smul, hS.1, hS.2, smul_zero, smul_zero, add_zero]

/-! ### The four anchor generators act slotwise -/

/-- The fixed plane of `anchorGenerator H` on the slots `o01, o02, o12`. -/
def pwf_fixP : Fin 4 → Fin 3 → Fin 4 := ![![0, 0, 0], ![1, 2, 3], ![2, 3, 1], ![3, 1, 2]]

/-- Slot exponents of the anchor generators (unreduced). -/
def pwf_genExp (H : Fin 4) (i : Fin 3) (r : Fin 4) : ℕ :=
  ![r0Exp r, r1Exp i r, 2 * r0Exp r + 2 * r1Exp i r, 2 * r0Exp r + r1Exp i r] H

theorem pwf_genExp_fix : ∀ H i, pwf_genExp H i (pwf_fixP H i) % 3 = 0 := by decide

theorem pwf_genExp_move : ∀ H i r, r ≠ pwf_fixP H i → pwf_genExp H i r % 3 ≠ 0 := by decide

theorem pwf_slotwise_mul (a b c a' b' c' : Module.End ℝ Octonion) :
    slotwise a b c * slotwise a' b' c' = slotwise (a * a') (b * b') (c * c') :=
  LinearMap.ext fun _ => rfl

theorem pwf_omegaPow_mul (e e' : Fin 4 → ℕ) : omegaPow e * omegaPow e' = omegaPow (e + e') := by
  funext r; simp [omegaPow, pow_add]

theorem pwf_anchorGenerator_eq (H : Fin 4) :
    anchorGenerator H = slotwise (planeRot (omegaPow (pwf_genExp H 0))) (planeRot (omegaPow (pwf_genExp H 1)))
      (planeRot (omegaPow (pwf_genExp H 2))) := by
  fin_cases H
  · exact R0_eq_slotwise
  · exact R1_eq_slotwise
  · show R0 ^ 2 * R1 ^ 2 = _
    rw [R0_eq_slotwise, R1_eq_slotwise, pow_two, pow_two, pwf_slotwise_mul, pwf_slotwise_mul, pwf_slotwise_mul]
    simp only [planeRot_mul, pwf_omegaPow_mul]
    congr 3 <;> funext r <;> simp [pwf_genExp] <;> ring
  · show R0 ^ 2 * R1 = _
    rw [R0_eq_slotwise, R1_eq_slotwise, pow_two, pwf_slotwise_mul, pwf_slotwise_mul]
    simp only [planeRot_mul, pwf_omegaPow_mul]
    congr 3 <;> funext r <;> simp [pwf_genExp] <;> ring

/-- The marked subalgebra `J^H`: fixed points of the generator of `H`. -/
def anchorFixedAlg (H : Fin 4) : Submodule ℝ Albert := fixedSpace (anchorGenerator H)

/-- Derivations vanishing on `J^H`, as a submodule. -/
def pointwiseSubmodule (H : Fin 4) : Submodule ℝ (Module.End ℝ Albert) where
  carrier := {D | D ∈ jordanDerivations ∧ ∀ x ∈ anchorFixedAlg H, D x = 0}
  zero_mem' := ⟨jordanDerivations.zero_mem, fun _ _ => rfl⟩
  add_mem' := by
    rintro D E ⟨hD, hD'⟩ ⟨hE, hE'⟩
    exact ⟨jordanDerivations.add_mem hD hE, fun x hx => by
      rw [LinearMap.add_apply, hD' x hx, hE' x hx, add_zero]⟩
  smul_mem' := by
    rintro c D ⟨hD, hD'⟩
    exact ⟨jordanDerivations.smul_mem c hD, fun x hx => by
      rw [LinearMap.smul_apply, hD' x hx, smul_zero]⟩

theorem commutator_mem_pointwiseSubmodule (H : Fin 4) {D E : Module.End ℝ Albert}
    (hD : D ∈ pointwiseSubmodule H) (hE : E ∈ pointwiseSubmodule H) :
    D * E - E * D ∈ pointwiseSubmodule H := by
  refine ⟨commutator_mem_derivationSubmodule hD.1 hE.1, fun x hx => ?_⟩
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hD.2 x hx, hE.2 x hx,
    map_zero, map_zero, sub_zero]

/-- The pointwise factor of `H`: the Lie algebra of derivations vanishing on `J^H`. -/
def pointwiseFactor (H : Fin 4) : LieSubalgebra ℝ (Module.End ℝ Albert) :=
  { pointwiseSubmodule H with lie_mem' := fun hD hE => commutator_mem_pointwiseSubmodule H hD hE }

theorem mem_pointwiseFactor {H : Fin 4} {D : Module.End ℝ Albert} :
    D ∈ pointwiseFactor H ↔ D ∈ jordanDerivations ∧ ∀ x ∈ anchorFixedAlg H, D x = 0 := Iff.rfl

/-! ### Membership of extended triples -/

theorem pwf_mem_anchorFixedAlg_iff (H : Fin 4) (x : Albert) :
    x ∈ anchorFixedAlg H ↔
      planeRot (omegaPow (pwf_genExp H 0)) x.o01 = x.o01 ∧ planeRot (omegaPow (pwf_genExp H 1)) x.o02 = x.o02 ∧
        planeRot (omegaPow (pwf_genExp H 2)) x.o12 = x.o12 := by
  rw [anchorFixedAlg, mem_fixedSpace, pwf_anchorGenerator_eq, slotwise_apply]
  constructor
  · intro h
    exact ⟨congrArg Albert.o01 h, congrArg Albert.o02 h, congrArg Albert.o12 h⟩
  · rintro ⟨h1, h2, h3⟩
    apply Albert.extExplicit <;> simp [h1, h2, h3]

theorem pwf_slot01_mem_fixed (H : Fin 4) {a : Octonion}
    (ha : a = octBasis (planeFst (pwf_fixP H 0)) ∨ a = octBasis (planeSnd (pwf_fixP H 0))) :
    slot01 a ∈ anchorFixedAlg H := by
  rw [pwf_mem_anchorFixedAlg_iff]
  refine ⟨?_, by simp [slot01], by simp [slot01]⟩
  rcases ha with rfl | rfl
  · exact pwf_planeRot_planeFst_fixed (pwf_genExp_fix H 0)
  · exact pwf_planeRot_planeSnd_fixed (pwf_genExp_fix H 0)

theorem pwf_slot02_mem_fixed (H : Fin 4) {a : Octonion}
    (ha : a = octBasis (planeFst (pwf_fixP H 1)) ∨ a = octBasis (planeSnd (pwf_fixP H 1))) :
    slot02 a ∈ anchorFixedAlg H := by
  rw [pwf_mem_anchorFixedAlg_iff]
  refine ⟨by simp [slot02], ?_, by simp [slot02]⟩
  rcases ha with rfl | rfl
  · exact pwf_planeRot_planeFst_fixed (pwf_genExp_fix H 1)
  · exact pwf_planeRot_planeSnd_fixed (pwf_genExp_fix H 1)

theorem pwf_slot12_mem_fixed (H : Fin 4) {a : Octonion}
    (ha : a = octBasis (planeFst (pwf_fixP H 2)) ∨ a = octBasis (planeSnd (pwf_fixP H 2))) :
    slot12 a ∈ anchorFixedAlg H := by
  rw [pwf_mem_anchorFixedAlg_iff]
  refine ⟨by simp [slot12], by simp [slot12], ?_⟩
  rcases ha with rfl | rfl
  · exact pwf_planeRot_planeFst_fixed (pwf_genExp_fix H 2)
  · exact pwf_planeRot_planeSnd_fixed (pwf_genExp_fix H 2)

/-- **Membership criterion.** An extended related triple vanishes on `J^H` exactly when its three
components kill the fixed planes of their slots. -/
theorem pwf_extend_mem_pointwiseFactor_iff {t : EndTriple} (ht : IsRelatedTriple t) (H : Fin 4) :
    extendTriple t ∈ pointwiseFactor H ↔
      PwfKillsPlane t.1 (pwf_fixP H 0) ∧ PwfKillsPlane t.2.2 (pwf_fixP H 1) ∧ PwfKillsPlane t.2.1 (pwf_fixP H 2) := by
  rw [mem_pointwiseFactor]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact congrArg Albert.o01 (h _ (pwf_slot01_mem_fixed H (Or.inl rfl)))
    · exact congrArg Albert.o01 (h _ (pwf_slot01_mem_fixed H (Or.inr rfl)))
    · exact congrArg Albert.o02 (h _ (pwf_slot02_mem_fixed H (Or.inl rfl)))
    · exact congrArg Albert.o02 (h _ (pwf_slot02_mem_fixed H (Or.inr rfl)))
    · exact congrArg Albert.o12 (h _ (pwf_slot12_mem_fixed H (Or.inl rfl)))
    · exact congrArg Albert.o12 (h _ (pwf_slot12_mem_fixed H (Or.inr rfl)))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨diagonalFixer_le (extendTriple_mem ht), fun x hx => ?_⟩
    rw [pwf_mem_anchorFixedAlg_iff] at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [extendTriple_apply, h1.apply_of_fixed (pwf_genExp_move H 0) hx1,
      h2.apply_of_fixed (pwf_genExp_move H 1) hx2, h3.apply_of_fixed (pwf_genExp_move H 2) hx3]
    rfl

theorem pwf_idem_mem_fixed (H : Fin 4) :
    idem0 ∈ anchorFixedAlg H ∧ idem1 ∈ anchorFixedAlg H ∧ idem2 ∈ anchorFixedAlg H := by
  simp only [pwf_mem_anchorFixedAlg_iff, idem0, idem1, idem2, map_zero, and_self]

theorem pwf_commute_anchorGenerator {h : Module.End ℝ Albert} (hh : h ∈ commonCartan) (H : Fin 4) :
    anchorGenerator H * h = h * anchorGenerator H := by
  obtain ⟨-, h0, h1⟩ := mem_commonCartan.mp hh
  have c0 : Commute R0 h := h0
  have c1 : Commute R1 h := h1
  fin_cases H
  · exact h0
  · exact h1
  · exact ((c0.pow_left 2).mul_left (c1.pow_left 2)).eq
  · exact ((c0.pow_left 2).mul_left c1).eq

theorem pointwiseFactor_le_diagonalFixer (H : Fin 4) : pointwiseFactor H ≤ diagonalFixer := by
  intro D hD
  obtain ⟨hD, hD'⟩ := mem_pointwiseFactor.mp hD
  obtain ⟨i0, i1, i2⟩ := pwf_idem_mem_fixed H
  exact mem_diagonalFixer.mpr ⟨hD, hD' _ i0, hD' _ i1, hD' _ i2⟩

theorem commonCartan_normalizes_pointwiseFactor (H : Fin 4) {h D : Module.End ℝ Albert}
    (hh : h ∈ commonCartan) (hD : D ∈ pointwiseFactor H) : h * D - D * h ∈ pointwiseFactor H := by
  obtain ⟨hD, hD'⟩ := mem_pointwiseFactor.mp hD
  refine mem_pointwiseFactor.mpr ⟨commutator_mem_derivationSubmodule hh.1 hD, fun x hx => ?_⟩
  have hhx : h x ∈ anchorFixedAlg H := by
    rw [anchorFixedAlg, mem_fixedSpace] at hx ⊢
    rw [← Module.End.mul_apply, pwf_commute_anchorGenerator hh H, Module.End.mul_apply, hx]
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hD' x hx, hD' _ hhx, map_zero,
    sub_zero]

/-! ### Root-plane projections as polynomials in `ad t` -/

/-- `ad (h_q)` on endomorphisms, `h_q = psi⁻¹ J_q`. -/
def pwf_adL (q : Fin 4) : Module.End ℝ (Module.End ℝ Albert) :=
  LinearMap.mulLeft ℝ (pwf_hq q : Module.End ℝ Albert) - LinearMap.mulRight ℝ (pwf_hq q : Module.End ℝ Albert)

theorem pwf_adL_apply (q : Fin 4) (E : Module.End ℝ Albert) :
    pwf_adL q E = (pwf_hq q : Module.End ℝ Albert) * E - E * (pwf_hq q : Module.End ℝ Albert) := rfl

theorem pwf_adL_X (q : Fin 4) (β : PosRoot) :
    pwf_adL q (sRootX β) = ((β.weight q : ℤ) : ℝ) • (sRootY β : Module.End ℝ Albert) := by
  rw [pwf_adL_apply, commonCartan_bracket_sRootX β (pwf_hq_mem q), pwf_rootEval_hq]

theorem pwf_adL_Y (q : Fin 4) (β : PosRoot) :
    pwf_adL q (sRootY β) = -(((β.weight q : ℤ) : ℝ) • (sRootX β : Module.End ℝ Albert)) := by
  rw [pwf_adL_apply, commonCartan_bracket_sRootY β (pwf_hq_mem q), pwf_rootEval_hq]

theorem pwf_adL_cartan (q : Fin 4) {E : Module.End ℝ Albert} (hE : E ∈ commonCartan) : pwf_adL q E = 0 := by
  rw [pwf_adL_apply, commonCartan_abelian (pwf_hq_mem q) hE, sub_self]

theorem pwf_adL_mem (H : Fin 4) (q : Fin 4) {E : Module.End ℝ Albert} (hE : E ∈ pointwiseFactor H) :
    pwf_adL q E ∈ pointwiseFactor H :=
  commonCartan_normalizes_pointwiseFactor H (pwf_hq_mem q) hE

/-- The sign `±1` of `α = ε_r ± ε_s`. -/
def pwf_sgnR (α : PosRoot) : ℝ := if α.plus then 1 else -1

/-- Projection onto the root plane of `α`: `½ (ad_r² ad_s² − sgn ad_r ad_s)`. -/
def pwf_projR (α : PosRoot) : Module.End ℝ (Module.End ℝ Albert) :=
  (1 / 2 : ℝ) • (pwf_adL α.r ∘ₗ pwf_adL α.r ∘ₗ pwf_adL α.s ∘ₗ pwf_adL α.s - pwf_sgnR α • (pwf_adL α.r ∘ₗ pwf_adL α.s))

theorem pwf_kappa_int : ∀ α β : PosRoot,
    (β.weight α.r) ^ 2 * (β.weight α.s) ^ 2 + (if α.plus then 1 else -1) * β.weight α.r * β.weight α.s =
      if β = α then 2 else 0 := by
  decide

theorem pwf_kappa_real (α β : PosRoot) :
    ((β.weight α.r : ℤ) : ℝ) ^ 2 * ((β.weight α.s : ℤ) : ℝ) ^ 2 +
        pwf_sgnR α * ((β.weight α.r : ℤ) : ℝ) * ((β.weight α.s : ℤ) : ℝ) = if β = α then 2 else 0 := by
  have h := pwf_kappa_int α β
  have hs : pwf_sgnR α = (((if α.plus then 1 else -1 : ℤ)) : ℝ) := by
    unfold pwf_sgnR; split_ifs <;> simp
  rw [hs]
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow] at h'
  rw [h']
  split_ifs <;> simp

theorem pwf_projR_X (α β : PosRoot) :
    pwf_projR α (sRootX β) = if β = α then (sRootX β : Module.End ℝ Albert) else 0 := by
  have key : pwf_projR α (sRootX β) = ((((β.weight α.r : ℤ) : ℝ) ^ 2 * ((β.weight α.s : ℤ) : ℝ) ^ 2 +
      pwf_sgnR α * ((β.weight α.r : ℤ) : ℝ) * ((β.weight α.s : ℤ) : ℝ)) / 2) • (sRootX β : Module.End ℝ Albert) := by
    simp only [pwf_projR, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, pwf_adL_X, pwf_adL_Y,
      map_smul, map_neg]
    module
  rw [key, pwf_kappa_real]
  split_ifs <;> simp

theorem pwf_projR_Y (α β : PosRoot) :
    pwf_projR α (sRootY β) = if β = α then (sRootY β : Module.End ℝ Albert) else 0 := by
  have key : pwf_projR α (sRootY β) = ((((β.weight α.r : ℤ) : ℝ) ^ 2 * ((β.weight α.s : ℤ) : ℝ) ^ 2 +
      pwf_sgnR α * ((β.weight α.r : ℤ) : ℝ) * ((β.weight α.s : ℤ) : ℝ)) / 2) • (sRootY β : Module.End ℝ Albert) := by
    simp only [pwf_projR, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, pwf_adL_X, pwf_adL_Y,
      map_smul, map_neg]
    module
  rw [key, pwf_kappa_real]
  split_ifs <;> simp

theorem pwf_projR_cartan (α : PosRoot) {E : Module.End ℝ Albert} (hE : E ∈ commonCartan) : pwf_projR α E = 0 := by
  simp [pwf_projR, pwf_adL_cartan _ hE]

theorem pwf_projR_mem (H : Fin 4) (α : PosRoot) {E : Module.End ℝ Albert} (hE : E ∈ pointwiseFactor H) :
    pwf_projR α E ∈ pointwiseFactor H := by
  have : pwf_projR α E = (1 / 2 : ℝ) • (pwf_adL α.r (pwf_adL α.r (pwf_adL α.s (pwf_adL α.s E))) - pwf_sgnR α • pwf_adL α.r (pwf_adL α.s E)) :=
    rfl
  rw [this]
  exact (pointwiseFactor H).smul_mem _ ((pointwiseFactor H).sub_mem
    (pwf_adL_mem H _ (pwf_adL_mem H _ (pwf_adL_mem H _ (pwf_adL_mem H _ hE))))
    ((pointwiseFactor H).smul_mem _ (pwf_adL_mem H _ (pwf_adL_mem H _ hE))))

/-- Root decomposition of an element of `s`. -/
theorem pwf_s_decomp (D : diagonalFixer) : ∃ h ∈ commonCartan, ∃ a b : PosRoot → ℝ,
    (D : Module.End ℝ Albert) =
      h + ∑ α, (a α • (sRootX α : Module.End ℝ Albert) + b α • (sRootY α : Module.End ℝ Albert)) := by
  have hD : D ∈ cartanInS ⊔ Submodule.span ℝ (Set.range sRootX ∪ Set.range sRootY) := by
    rw [cartanInS_sup_roots]; trivial
  obtain ⟨h, hh, w, hw, rfl⟩ := Submodule.mem_sup.mp hD
  rw [Submodule.span_union] at hw
  obtain ⟨wx, hwx, wy, hwy, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwy
  refine ⟨h, hh, a, b, ?_⟩
  push_cast
  rw [Finset.sum_add_distrib]

theorem pwf_projR_decomp (α : PosRoot) {D h : Module.End ℝ Albert} (hh : h ∈ commonCartan) {a b : PosRoot → ℝ}
    (hD : D = h + ∑ β, (a β • (sRootX β : Module.End ℝ Albert) + b β • (sRootY β : Module.End ℝ Albert))) :
    pwf_projR α D = a α • (sRootX α : Module.End ℝ Albert) + b α • (sRootY α : Module.End ℝ Albert) := by
  rw [hD, map_add, pwf_projR_cartan α hh, zero_add, map_sum]
  simp only [map_add, map_smul, pwf_projR_X, pwf_projR_Y, smul_ite, smul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ### Independence of a root pair -/

theorem pwf_rootXY_indep (α : PosRoot) (a b : ℝ) (h : a • rootX α + b • rootY α = 0) : a = 0 ∧ b = 0 := by
  have hinj : Function.Injective (![Sum.inr (α, false), Sum.inr (α, true)] : Fin 2 → RootIndex) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := rootFamily_linearIndependent.comp _ hinj
  have hf : rootFamily ∘ (![Sum.inr (α, false), Sum.inr (α, true)] : Fin 2 → RootIndex) =
      ![rootX α, rootY α] := by
    funext i; fin_cases i <;> rfl
  rw [hf] at hli
  exact LinearIndependent.pair_iff.mp hli a b h

theorem pwf_sRoot_pair_indep (α : PosRoot) (a b : ℝ)
    (h : a • (sRootX α : Module.End ℝ Albert) + b • (sRootY α : Module.End ℝ Albert) = 0) :
    a = 0 ∧ b = 0 := by
  have h' : a • sRootX α + b • sRootY α = 0 := Subtype.ext (by push_cast; exact h)
  have h'' := congrArg (fun D => ((psi D : skewEnd) : Module.End ℝ Octonion)) h'
  simp only [map_add, map_smul, sRootX, sRootY, LieEquiv.apply_symm_apply, map_zero] at h''
  exact pwf_rootXY_indep α a b (by simpa using h'')

/-! ### The hexagon criterion -/

theorem pwf_hex_iff_conds : ∀ (H : Fin 4) (α : PosRoot), (∃ j, (rowRoot H j).1 = α) ↔
    ((pwf_fixP H 0 ≠ (pwf_permA α).r ∧ pwf_fixP H 0 ≠ (pwf_permA α).s) ∧ (pwf_fixP H 1 ≠ (pwf_permC α).r ∧ pwf_fixP H 1 ≠ (pwf_permC α).s) ∧
      (pwf_fixP H 2 ≠ α.r ∧ pwf_fixP H 2 ≠ α.s)) := by
  decide

theorem pwf_sgnA_ne' (α : PosRoot) : ((pwf_sgnARaw α.r α.s α.plus : ℤ) : ℝ) ≠ 0 := by
  exact_mod_cast pwf_sgnA_ne_zero α

theorem pwf_sgnC_ne' (α : PosRoot) : ((pwf_sgnCRaw α.r α.s α.plus : ℤ) : ℝ) ≠ 0 := by
  exact_mod_cast pwf_sgnC_ne_zero α

theorem pwf_sRootX_mem_of_hex {H : Fin 4} {α : PosRoot} (hα : α ∈ hexagon H) :
    (sRootX α : Module.End ℝ Albert) ∈ pointwiseFactor H := by
  obtain ⟨⟨a1, a2⟩, ⟨c1, c2⟩, ⟨b1, b2⟩⟩ := (pwf_hex_iff_conds H α).mp hα
  rw [pwf_sRootX_eq, pwf_extend_mem_pointwiseFactor_iff (pwf_tripleX_related α)]
  exact ⟨(pwf_rootX_kills _ _ a1 a2).smul _, (pwf_rootX_kills _ _ c1 c2).smul _, pwf_rootX_kills _ _ b1 b2⟩

theorem pwf_sRootX_not_mem {H : Fin 4} {α : PosRoot} (hα : α ∉ hexagon H) :
    (sRootX α : Module.End ℝ Albert) ∉ pointwiseFactor H := by
  intro hX
  rw [pwf_sRootX_eq, pwf_extend_mem_pointwiseFactor_iff (pwf_tripleX_related α)] at hX
  obtain ⟨hA, hC, hB⟩ := hX
  have hB' : PwfKillsPlane ((1 : ℝ) • rootX α) (pwf_fixP H 2) := by rw [one_smul]; exact hB
  apply hα
  refine (pwf_hex_iff_conds H α).mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inl e) (pwf_sgnA_ne' α) hA
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inr e) (pwf_sgnA_ne' α) hA
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inl e) (pwf_sgnC_ne' α) hC
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inr e) (pwf_sgnC_ne' α) hC
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inl e) one_ne_zero hB'
  · exact fun e => pwf_rootX_not_kills _ _ (Or.inr e) one_ne_zero hB'

/-- The hexagon root planes lie in the pointwise factor. -/
theorem sRoot_mem_pointwiseFactor {H : Fin 4} {α : PosRoot} (hα : α ∈ hexagon H) :
    (sRootX α : Module.End ℝ Albert) ∈ pointwiseFactor H ∧
      (sRootY α : Module.End ℝ Albert) ∈ pointwiseFactor H := by
  have hX := pwf_sRootX_mem_of_hex hα
  refine ⟨hX, ?_⟩
  obtain ⟨g, hg, hne⟩ := exists_rootEval_ne_zero α
  have h1 := commonCartan_normalizes_pointwiseFactor H hg hX
  rw [commonCartan_bracket_sRootX α hg] at h1
  have h2 := (pointwiseFactor H).smul_mem (rootEval α g)⁻¹ h1
  rwa [inv_smul_smul₀ hne] at h2

/-- No other root plane meets the pointwise factor. -/
theorem sRoot_plane_inf_pointwiseFactor {H : Fin 4} {α : PosRoot} (hα : α ∉ hexagon H) (a b : ℝ)
    (h : a • (sRootX α : Module.End ℝ Albert) + b • (sRootY α : Module.End ℝ Albert) ∈ pointwiseFactor H) :
    a = 0 ∧ b = 0 := by
  obtain ⟨g, hg, hne⟩ := exists_rootEval_ne_zero α
  set X := (sRootX α : Module.End ℝ Albert)
  set Y := (sRootY α : Module.End ℝ Albert)
  have e1 : g * X - X * g = rootEval α g • Y := commonCartan_bracket_sRootX α hg
  have e2 : g * Y - Y * g = -(rootEval α g • X) := commonCartan_bracket_sRootY α hg
  have hbr : g * (a • X + b • Y) - (a • X + b • Y) * g = rootEval α g • (a • Y - b • X) := by
    have : g * (a • X + b • Y) - (a • X + b • Y) * g = a • (g * X - X * g) + b • (g * Y - Y * g) := by
      simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    rw [this, e1, e2]
    module
  have h1 := commonCartan_normalizes_pointwiseFactor H hg h
  rw [hbr] at h1
  have h2 := (pointwiseFactor H).smul_mem (rootEval α g)⁻¹ h1
  rw [inv_smul_smul₀ hne] at h2
  have h3 := (pointwiseFactor H).sub_mem ((pointwiseFactor H).smul_mem a h) ((pointwiseFactor H).smul_mem b h2)
  have h4 : a • (a • X + b • Y) - b • (a • Y - b • X) = (a ^ 2 + b ^ 2) • X := by module
  rw [h4] at h3
  by_cases hab : a ^ 2 + b ^ 2 = 0
  · constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · exfalso
    have h5 := (pointwiseFactor H).smul_mem (a ^ 2 + b ^ 2)⁻¹ h3
    rw [inv_smul_smul₀ hab] at h5
    exact pwf_sRootX_not_mem hα h5

/-! ### The Cartan part of a pointwise factor -/

/-- The Cartan element with coordinates `c` in the basis `h_q = psi⁻¹ J_q`. -/
def pwf_cartanElt (c : Fin 4 → ℝ) : Module.End ℝ Albert := ∑ q, c q • (pwf_hq q : Module.End ℝ Albert)

theorem pwf_cartanElt_mem_cartan (c : Fin 4 → ℝ) : pwf_cartanElt c ∈ commonCartan :=
  commonCartan.toSubmodule.sum_mem fun q _ => commonCartan.smul_mem _ (pwf_hq_mem q)

theorem pwf_cartanWeight_cartanElt (c : Fin 4 → ℝ) (q' : Fin 4) : cartanWeight q' (pwf_cartanElt c) = c q' := by
  simp only [pwf_cartanElt, map_sum, map_smul, pwf_cartanWeight_hq, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem pwf_cartanElt_add_smul (a b : ℝ) (u v : Fin 4 → ℝ) :
    pwf_cartanElt (a • u + b • v) = a • pwf_cartanElt u + b • pwf_cartanElt v := by
  simp only [pwf_cartanElt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]

/-- The related triple of `pwf_cartanElt c`. -/
def pwf_cartanSum (c : Fin 4 → ℝ) : EndTriple := ∑ q, c q • pwf_cartanTriple q

theorem pwf_cartanSum_related (c : Fin 4 → ℝ) : IsRelatedTriple (pwf_cartanSum c) :=
  relatedTriples.toSubmodule.sum_mem fun q _ => relatedTriples.smul_mem _ (pwf_cartanTriple_related q)

theorem pwf_cartanElt_eq (c : Fin 4 → ℝ) : pwf_cartanElt c = extendTriple (pwf_cartanSum c) := by
  simp only [pwf_cartanElt, pwf_cartanSum, pwf_hq_eq, map_sum, map_smul]

theorem pwf_sum_smul_combo (c : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) :
    ∑ q, c q • ∑ q', (M q q' / 2) • cartanGen q' = ∑ q', (∑ q, c q * M q q' / 2) • cartanGen q' := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun q _ => ?_
  rw [mul_div_assoc]

theorem pwf_cartanSum_fst (c : Fin 4 → ℝ) :
    (pwf_cartanSum c).1 = ∑ q', (∑ q, c q * PwfMA q q' / 2) • cartanGen q' := by
  rw [← pwf_sum_smul_combo]
  simp only [pwf_cartanSum, Prod.fst_sum, Prod.smul_fst, pwf_cartanTriple, pwf_cartanA]

theorem pwf_cartanSum_thd (c : Fin 4 → ℝ) :
    (pwf_cartanSum c).2.2 = ∑ q', (∑ q, c q * PwfMC q q' / 2) • cartanGen q' := by
  rw [← pwf_sum_smul_combo]
  simp only [pwf_cartanSum, Prod.snd_sum, Prod.smul_snd, pwf_cartanTriple, pwf_cartanC]

theorem pwf_cartanSum_snd (c : Fin 4 → ℝ) : (pwf_cartanSum c).2.1 = ∑ q, c q • cartanGen q := by
  simp only [pwf_cartanSum, Prod.snd_sum, Prod.fst_sum, Prod.smul_snd, Prod.smul_fst, pwf_cartanTriple]

/-- The linear conditions for a Cartan element to lie in the pointwise factor of `H`. -/
def PwfCartanCond (H : Fin 4) (c : Fin 4 → ℝ) : Prop :=
  (∑ q, c q * PwfMA q (pwf_fixP H 0)) = 0 ∧ (∑ q, c q * PwfMC q (pwf_fixP H 1)) = 0 ∧ c (pwf_fixP H 2) = 0

theorem pwf_cartanElt_mem_iff (H : Fin 4) (c : Fin 4 → ℝ) : pwf_cartanElt c ∈ pointwiseFactor H ↔ PwfCartanCond H c := by
  rw [pwf_cartanElt_eq, pwf_extend_mem_pointwiseFactor_iff (pwf_cartanSum_related c), pwf_cartanSum_fst, pwf_cartanSum_thd,
    pwf_cartanSum_snd, pwf_killsPlane_combo, pwf_killsPlane_combo, pwf_killsPlane_combo, PwfCartanCond, ← Finset.sum_div,
    ← Finset.sum_div, div_eq_zero_iff, div_eq_zero_iff]
  simp only [two_ne_zero, or_false]

theorem pwf_cartan_eq_cartanElt {h : Module.End ℝ Albert} (hh : h ∈ commonCartan) :
    h = pwf_cartanElt (fun q => cartanWeight q h) := by
  have hE : pwf_cartanElt (fun q => cartanWeight q h) ∈ diagonalFixer :=
    commonCartan_le_diagonalFixer (pwf_cartanElt_mem_cartan _)
  have hp : psi (⟨h, commonCartan_le_diagonalFixer hh⟩ : diagonalFixer) = psi ⟨_, hE⟩ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    rw [psi_commonCartan ⟨h, commonCartan_le_diagonalFixer hh⟩ hh, psi_apply]
    simp only [pwf_cartanElt, Fin.sum_univ_four, LinearMap.add_apply, LinearMap.smul_apply, Albert.add_o12,
      Albert.smul_o12]
    rw [← psi_apply, ← psi_apply, ← psi_apply, ← psi_apply, pwf_psi_hq, pwf_psi_hq, pwf_psi_hq, pwf_psi_hq]
  have key := psi.injective hp
  exact congrArg Subtype.val key

theorem pwf_mem_pt_iff (H : Fin 4) (E : Module.End ℝ Albert) :
    E ∈ (pointwiseFactor H).toSubmodule ⊓ commonCartan.toSubmodule ↔ ∃ c, PwfCartanCond H c ∧ E = pwf_cartanElt c := by
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨_, ?_, pwf_cartan_eq_cartanElt ht⟩
    rw [← pwf_cartanElt_mem_iff, ← pwf_cartan_eq_cartanElt ht]
    exact hp
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(pwf_cartanElt_mem_iff H c).2 hc, pwf_cartanElt_mem_cartan c⟩

/-- Coordinates of a basis of the solutions of `PwfCartanCond H`. -/
def pwf_cb : Fin 4 → Fin 2 → Fin 4 → ℝ :=
  ![![![0, 1, 0, 1], ![0, 0, 1, 1]], ![![1, 0, 1, 0], ![0, 1, 1, 0]],
    ![![1, 0, -1, 0], ![0, 0, -1, 1]], ![![1, 1, 0, 0], ![1, 0, 0, 1]]]

/-- Coordinates read off by the basis `pwf_cb H`. -/
def pwf_ci : Fin 4 → Fin 2 → Fin 4 := ![![1, 2], ![0, 1], ![0, 3], ![1, 3]]

theorem pwf_cond_cb (H : Fin 4) (k : Fin 2) : PwfCartanCond H (pwf_cb H k) := by
  fin_cases H <;> fin_cases k <;>
    simp [PwfCartanCond, pwf_cb, PwfMA, PwfMC, pwf_fixP, Fin.sum_univ_four]

theorem pwf_cond_decomp (H : Fin 4) (c : Fin 4 → ℝ) (hc : PwfCartanCond H c) :
    c = c (pwf_ci H 0) • pwf_cb H 0 + c (pwf_ci H 1) • pwf_cb H 1 := by
  obtain ⟨h1, h2, h3⟩ := hc
  funext q
  fin_cases H <;> fin_cases q <;>
    simp [pwf_cb, pwf_ci, PwfMA, PwfMC, pwf_fixP, Fin.sum_univ_four] at h1 h2 h3 ⊢ <;> linarith

/-- The two Cartan generators of the pointwise factor. -/
def pwf_cartanPair (H : Fin 4) : Fin 2 → Module.End ℝ Albert := ![pwf_cartanElt (pwf_cb H 0), pwf_cartanElt (pwf_cb H 1)]

theorem pwf_pt_eq (H : Fin 4) :
    (pointwiseFactor H).toSubmodule ⊓ commonCartan.toSubmodule = Submodule.span ℝ (Set.range (pwf_cartanPair H)) := by
  apply le_antisymm
  · intro E hE
    obtain ⟨c, hc, rfl⟩ := (pwf_mem_pt_iff H E).mp hE
    rw [pwf_cond_decomp H c hc, pwf_cartanElt_add_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (pwf_mem_pt_iff H _).mpr ⟨pwf_cb H k, pwf_cond_cb H k, by fin_cases k <;> rfl⟩

theorem pwf_cartanPair_indep (H : Fin 4) : LinearIndependent ℝ (pwf_cartanPair H) := by
  unfold pwf_cartanPair
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e0 := congrArg (cartanWeight (pwf_ci H 0)) hst
  have e1 := congrArg (cartanWeight (pwf_ci H 1)) hst
  simp only [map_add, map_smul, pwf_cartanWeight_cartanElt, map_zero, smul_eq_mul] at e0 e1
  fin_cases H <;> simp [pwf_cb, pwf_ci] at e0 e1 <;> constructor <;> linarith

theorem finrank_pointwiseFactor_inf_cartan (H : Fin 4) :
    Module.finrank ℝ ↥((pointwiseFactor H).toSubmodule ⊓ commonCartan.toSubmodule) = 2 := by
  rw [pwf_pt_eq, finrank_span_eq_card (pwf_cartanPair_indep H)]
  simp

/-! ### The hexagon span and the dimension count -/

/-- The six hexagon root vectors of `H`. -/
def pwf_hexVec (H : Fin 4) (jb : Fin 3 × Bool) : Module.End ℝ Albert :=
  if jb.2 then (sRootY (rowRoot H jb.1).1 : Module.End ℝ Albert) else (sRootX (rowRoot H jb.1).1 : Module.End ℝ Albert)

/-- Their span. -/
def pwf_hexSpan (H : Fin 4) : Submodule ℝ (Module.End ℝ Albert) := Submodule.span ℝ (Set.range (pwf_hexVec H))

theorem pwf_rowRoot_inj : ∀ (H : Fin 4) (j j' : Fin 3), (rowRoot H j').1 = (rowRoot H j).1 ↔ j' = j := by decide

theorem pwf_projR_hexVec (H : Fin 4) (j : Fin 3) (jb : Fin 3 × Bool) :
    pwf_projR (rowRoot H j).1 (pwf_hexVec H jb) = if jb.1 = j then pwf_hexVec H jb else 0 := by
  obtain ⟨j', b⟩ := jb
  cases b <;> simp [pwf_hexVec, pwf_projR_X, pwf_projR_Y, pwf_rowRoot_inj]

theorem pwf_hex_combo_zero (H : Fin 4) {E : Module.End ℝ Albert} (hE : E ∈ commonCartan)
    (c : Fin 3 × Bool → ℝ) (h : E = ∑ jb, c jb • pwf_hexVec H jb) (jb : Fin 3 × Bool) : c jb = 0 := by
  obtain ⟨j, b⟩ := jb
  have key := congrArg (pwf_projR (rowRoot H j).1) h
  rw [pwf_projR_cartan _ hE, map_sum] at key
  simp only [map_smul, pwf_projR_hexVec, smul_ite, smul_zero] at key
  rw [Fintype.sum_eq_add (j, false) (j, true) (by simp)] at key
  · simp only [ite_true, pwf_hexVec, Bool.false_eq_true, ite_false] at key
    obtain ⟨h1, h2⟩ := pwf_sRoot_pair_indep (rowRoot H j).1 _ _ key.symm
    cases b
    · exact h1
    · exact h2
  · rintro ⟨j', b'⟩ ⟨hne1, hne2⟩
    have : j' ≠ j := by
      rintro rfl
      cases b' <;> simp_all
    simp [this]

theorem pwf_hexVec_indep (H : Fin 4) : LinearIndependent ℝ (pwf_hexVec H) :=
  Fintype.linearIndependent_iff.mpr fun c hc jb =>
    pwf_hex_combo_zero H commonCartan.zero_mem c hc.symm jb

theorem pwf_finrank_hexSpan (H : Fin 4) : Module.finrank ℝ (pwf_hexSpan H) = 6 := by
  rw [pwf_hexSpan, finrank_span_eq_card (pwf_hexVec_indep H)]
  simp

theorem pwf_hexSpan_le (H : Fin 4) : pwf_hexSpan H ≤ (pointwiseFactor H).toSubmodule := by
  rw [pwf_hexSpan, Submodule.span_le]
  rintro _ ⟨⟨j, b⟩, rfl⟩
  cases b
  · exact (sRoot_mem_pointwiseFactor ⟨j, rfl⟩).1
  · exact (sRoot_mem_pointwiseFactor ⟨j, rfl⟩).2

theorem pwf_p_eq (H : Fin 4) :
    (pointwiseFactor H).toSubmodule = Submodule.span ℝ (Set.range (pwf_cartanPair H)) ⊔ pwf_hexSpan H := by
  apply le_antisymm
  · intro D hD
    have hDs : D ∈ diagonalFixer := pointwiseFactor_le_diagonalFixer H hD
    obtain ⟨h, hh, a, b, hdec⟩ := pwf_s_decomp ⟨D, hDs⟩
    change D = _ at hdec
    have hzero : ∀ α, α ∉ hexagon H → a α = 0 ∧ b α = 0 := fun α hα =>
      sRoot_plane_inf_pointwiseFactor hα _ _ (by rw [← pwf_projR_decomp α hh hdec]; exact pwf_projR_mem H α hD)
    have hS : ∑ α, (a α • (sRootX α : Module.End ℝ Albert) + b α • (sRootY α : Module.End ℝ Albert)) ∈
        pwf_hexSpan H := by
      refine Submodule.sum_mem _ fun α _ => ?_
      by_cases hα : α ∈ hexagon H
      · obtain ⟨j, rfl⟩ := hα
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, false), rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, true), rfl⟩))
      · obtain ⟨ha, hb⟩ := hzero α hα
        simp [ha, hb]
    have hhp : h ∈ (pointwiseFactor H).toSubmodule := by
      have : h = D - ∑ α, (a α • (sRootX α : Module.End ℝ Albert) + b α • (sRootY α : Module.End ℝ Albert)) := by
        rw [hdec]; abel
      rw [this]
      exact Submodule.sub_mem _ hD (pwf_hexSpan_le H hS)
    have hht : h ∈ Submodule.span ℝ (Set.range (pwf_cartanPair H)) := by
      rw [← pwf_pt_eq]; exact Submodule.mem_inf.mpr ⟨hhp, hh⟩
    rw [hdec]
    exact Submodule.add_mem_sup hht hS
  · exact sup_le (by rw [← pwf_pt_eq]; exact inf_le_left) (pwf_hexSpan_le H)

theorem pwf_cartan_hex_disjoint (H : Fin 4) :
    Submodule.span ℝ (Set.range (pwf_cartanPair H)) ⊓ pwf_hexSpan H = ⊥ := by
  rw [eq_bot_iff]
  intro E hE
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hE
  have hEt : E ∈ commonCartan := by
    rw [← pwf_pt_eq] at h1; exact (Submodule.mem_inf.mp h1).2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h2
  have hz := pwf_hex_combo_zero H hEt c hc.symm
  rw [Submodule.mem_bot, ← hc]
  simp [hz]

theorem finrank_pointwiseFactor (H : Fin 4) : Module.finrank ℝ (pointwiseFactor H) = 8 := by
  have e1 : Module.finrank ℝ (pointwiseFactor H) =
      Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (pwf_cartanPair H)) ⊔ pwf_hexSpan H) :=
    (LinearEquiv.ofEq _ _ (pwf_p_eq H)).finrank_eq
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range (pwf_cartanPair H))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have : FiniteDimensional ℝ (pwf_hexSpan H) := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span ℝ (Set.range (pwf_cartanPair H))) (pwf_hexSpan H)
  rw [pwf_cartan_hex_disjoint, finrank_bot, add_zero, finrank_span_eq_card (pwf_cartanPair_indep H),
    pwf_finrank_hexSpan] at e2
  rw [e1, e2]
  simp

/-! ### Transport -/

theorem pwf_conj_mem_jordanDerivations {g ginv : Module.End ℝ Albert} (hg : IsNativeAut g)
    (hginv : IsNativeAut ginv) (hgg : ginv ∘ₗ g = LinearMap.id) {D : Module.End ℝ Albert}
    (hD : D ∈ jordanDerivations) : ginv * D * g ∈ jordanDerivations := by
  have hD' : ∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y) := hD
  have hc : ∀ z, ginv (g z) = z := fun z => LinearMap.congr_fun hgg z
  show ∀ x y, _
  intro x y
  simp only [Module.End.mul_apply]
  rw [hg.jordan, hD', map_add, hginv.jordan, hginv.jordan, hc, hc]

theorem pwf_transport_conj (i : Fin 3) : transportTinv i ∘ₗ anchorGenerator i.succ = R0 ∘ₗ transportTinv i := by
  fin_cases i
  · show transportTinv 0 ∘ₗ R1 = R0 ∘ₗ transportTinv 0
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, R1]
    exact LinearMap.congr_fun (transportTinv_comp_transportT 0) _
  · exact transportTinv_one_conj
  · exact transportTinv_two_conj

theorem pwf_transportT_transportTinv (i : Fin 3) (z : Albert) : transportT i (transportTinv i z) = z :=
  LinearMap.congr_fun (transportT_comp_transportTinv i) z

theorem pwf_transportTinv_transportT (i : Fin 3) (z : Albert) : transportTinv i (transportT i z) = z :=
  LinearMap.congr_fun (transportTinv_comp_transportT i) z

theorem pwf_transportTinv_mem_fixed {i : Fin 3} {x : Albert} (hx : x ∈ anchorFixedAlg i.succ) :
    transportTinv i x ∈ anchorFixedAlg 0 := by
  rw [anchorFixedAlg, mem_fixedSpace] at hx ⊢
  have h := LinearMap.congr_fun (pwf_transport_conj i) x
  simp only [LinearMap.comp_apply] at h
  show R0 (transportTinv i x) = transportTinv i x
  rw [← h, hx]

theorem pwf_transportT_mem_fixed {i : Fin 3} {y : Albert} (hy : y ∈ anchorFixedAlg 0) :
    transportT i y ∈ anchorFixedAlg i.succ := by
  rw [anchorFixedAlg, mem_fixedSpace] at hy ⊢
  have hy' : R0 y = y := hy
  have h := LinearMap.congr_fun (pwf_transport_conj i) (transportT i y)
  simp only [LinearMap.comp_apply, pwf_transportTinv_transportT, hy'] at h
  have h2 := congrArg (transportT i) h
  rwa [pwf_transportT_transportTinv] at h2

/-- The other three factors are the signed transports of the first. -/
theorem mem_pointwiseFactor_succ_iff (i : Fin 3) (D : Module.End ℝ Albert) :
    D ∈ pointwiseFactor i.succ ↔ transportTinv i * D * transportT i ∈ pointwiseFactor 0 := by
  constructor
  · intro hD
    obtain ⟨hD, hD'⟩ := mem_pointwiseFactor.mp hD
    refine mem_pointwiseFactor.mpr ⟨pwf_conj_mem_jordanDerivations (transportT_isNativeAut i)
      (transportTinv_isNativeAut i) (transportTinv_comp_transportT i) hD, fun y hy => ?_⟩
    simp only [Module.End.mul_apply]
    rw [hD' _ (pwf_transportT_mem_fixed hy), map_zero]
  · intro hE
    obtain ⟨hE, hE'⟩ := mem_pointwiseFactor.mp hE
    have hDeq : D = transportT i * (transportTinv i * D * transportT i) * transportTinv i := by
      apply LinearMap.ext
      intro x
      simp only [Module.End.mul_apply, pwf_transportT_transportTinv]
    refine mem_pointwiseFactor.mpr ⟨?_, fun x hx => ?_⟩
    · rw [hDeq]
      exact pwf_conj_mem_jordanDerivations (transportTinv_isNativeAut i) (transportT_isNativeAut i)
        (transportT_comp_transportTinv i) hE
    · have h := hE' _ (pwf_transportTinv_mem_fixed hx)
      simp only [Module.End.mul_apply, pwf_transportT_transportTinv] at h
      have h2 := congrArg (transportT i) h
      rwa [pwf_transportT_transportTinv, map_zero] at h2

/-! ## The `H₀` factor: complex structure and weights `(ε₂, ε₃, −ε₄)` -/

/-- The complex structure `I = J₁ + J₂ − J₃` on the `R0`-moving planes of `o12`. -/
def h0Complex : Module.End ℝ Octonion := cartanGen 1 + cartanGen 2 - cartanGen 3

theorem pwf_octDot_smul_right' (u x : Octonion) (c : ℝ) : octDot u (c • x) = c * octDot u x := by
  rw [octDot_coordinates, octDot_coordinates]
  simp only [Prod.smul_fst, Prod.smul_snd]
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul]
  ring

/-- The `R0`-moving part of an octonion slot: orthogonal to the fixed plane `(1, i)`. -/
def h0Moving : Submodule ℝ Octonion where
  carrier := {x | octDot (octBasis (planeFst 0)) x = 0 ∧ octDot (octBasis (planeSnd 0)) x = 0}
  zero_mem' := ⟨pwf_octDot_zero_right' _, pwf_octDot_zero_right' _⟩
  add_mem' := by
    rintro x y ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [restr_octDot_add_right, h1, h3, add_zero], by rw [restr_octDot_add_right, h2, h4, add_zero]⟩
  smul_mem' := by
    rintro c x ⟨h1, h2⟩
    exact ⟨by rw [pwf_octDot_smul_right', h1, mul_zero], by rw [pwf_octDot_smul_right', h2, mul_zero]⟩

theorem planeRot_r0_moving {x : Octonion} (hx : x ∈ h0Moving) :
    planeRot (omegaPow r0Exp) x = (-1 / 2 : ℝ) • x - (Real.sqrt 3 / 2) • h0Complex x := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨⟨x0, x1, x2, x3⟩, ⟨x4, x5, x6, x7⟩⟩ := x
  rw [pwf_obF0, octDot_coordinates] at h1
  rw [pwf_obS0, octDot_coordinates] at h2
  simp only [one_mul, zero_mul, add_zero, zero_add] at h1 h2
  subst h1 h2
  have hz0 : omegaPow r0Exp 0 = 1 := by simp [omegaPow, r0Exp]
  have hz1 : omegaPow r0Exp 1 = ω ^ 2 := by simp [omegaPow, r0Exp]
  have hz2 : omegaPow r0Exp 2 = ω ^ 2 := by simp [omegaPow, r0Exp]
  have hz3 : omegaPow r0Exp 3 = ω := by simp [omegaPow, r0Exp]
  rw [pwf_planeRot_apply', hz0, hz1, hz2, hz3]
  simp only [h0Complex, cartanGen, LinearMap.add_apply, LinearMap.sub_apply, wedge_apply, pwf_obF1, pwf_obS1, pwf_obF2,
    pwf_obS2, pwf_obF3, pwf_obS3, octDot_coordinates, pwf_omega_re, pwf_omega_im, pwf_omega_sq_re, pwf_omega_sq_im]
  apply Prod.ext <;> apply Quaternion.ext <;> simp <;> ring

/-- The weights `(ε₂, ε₃, −ε₄)` on the three moving planes `1, 2, 3`. -/
def h0Weight (r : Fin 3) (h : Module.End ℝ Albert) : ℝ :=
  (if r = 2 then -1 else 1) * cartanWeight r.succ h

theorem psi_commonCartan_moving (h : diagonalFixer) (hh : (h : Module.End ℝ Albert) ∈ commonCartan)
    (r : Fin 3) :
    ((psi h : skewEnd) : Module.End ℝ Octonion) (octBasis (planeFst r.succ)) =
        h0Weight r h • h0Complex (octBasis (planeFst r.succ)) ∧
      ((psi h : skewEnd) : Module.End ℝ Octonion) (octBasis (planeSnd r.succ)) =
        h0Weight r h • h0Complex (octBasis (planeSnd r.succ)) := by
  rw [psi_commonCartan h hh, pwf_combo_planeFst, pwf_combo_planeSnd]
  simp only [h0Weight, h0Complex, LinearMap.add_apply, LinearMap.sub_apply, pwf_cartanGen_planeFst,
    pwf_cartanGen_planeSnd]
  fin_cases r <;> simp

/-- The weight vectors `ε₂, ε₃, −ε₄`. -/
def h0WeightVec : Fin 3 → Fin 4 → ℤ := ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1]]

/-- The hexagon of `H₀` is the set of differences of `(ε₂, ε₃, −ε₄)`. -/
theorem mem_hexagon_zero_iff (α : PosRoot) :
    α ∈ hexagon 0 ↔ ∃ a b : Fin 3, a ≠ b ∧ α.weight = h0WeightVec a - h0WeightVec b := by
  have key : ∀ β : PosRoot, (∃ j, (rowRoot 0 j).1 = β) ↔
      ∃ a b : Fin 3, a ≠ b ∧ β.weight = h0WeightVec a - h0WeightVec b := by
    decide
  exact key α

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.commutator_mem_pointwiseSubmodule
#print axioms CKM.NativeIntrinsicTriality.mem_pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.pointwiseFactor_le_diagonalFixer
#print axioms CKM.NativeIntrinsicTriality.commonCartan_normalizes_pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.sRoot_mem_pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.sRoot_plane_inf_pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.finrank_pointwiseFactor_inf_cartan
#print axioms CKM.NativeIntrinsicTriality.finrank_pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.mem_pointwiseFactor_succ_iff
#print axioms CKM.NativeIntrinsicTriality.planeRot_r0_moving
#print axioms CKM.NativeIntrinsicTriality.psi_commonCartan_moving
#print axioms CKM.NativeIntrinsicTriality.mem_hexagon_zero_iff
#print axioms CKM.NativeIntrinsicTriality.pointwiseFactor
#print axioms CKM.NativeIntrinsicTriality.pointwiseSubmodule
#print axioms CKM.NativeIntrinsicTriality.anchorFixedAlg
#print axioms CKM.NativeIntrinsicTriality.h0Moving
#print axioms CKM.NativeIntrinsicTriality.h0Complex
#print axioms CKM.NativeIntrinsicTriality.h0Weight
#print axioms CKM.NativeIntrinsicTriality.h0WeightVec

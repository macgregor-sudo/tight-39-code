module

public import HTPhaseCompleteCartan
public import HTPCValSupp

@[expose] public section

/-!
# Root property of the anchor operators `N_j` under the Cartan lifts (first-party)

`N_j = A_j − K_j` (VALUE's `nZ j = 2 N_j` over `ℤ[i]`; `A_j` the certificate's derivation extensions,
`K_j` the specified fixed operators) acts on one native state by `nLin j`. For the Cartan lift of quartet
`i ∈ {2, 3}` and every unit tuple `U`:

  `root_N : d_i(U)⁻¹ (N_j s) = U^{rootExp i j} • N_j (d_i(U)⁻¹ s)`   (every `j`, every state vector `s`),

i.e. each `N_j` is a root vector of the torus `{d_i(U)}` (matrix level, not only on the anchors).
Proof: a generic lemma in the weight basis of the plane rotations (`root_of_weight`: diagonal,
`α_p = x_{3+2p} − i x_{4+2p}`, `β_p = x_{3+2p} + i x_{4+2p}`), and one kernel check per `(i, j)` over
`ℤ[i]` (`rootCheck`): every nonzero entry of `N_j` in the weight basis has weight difference `rootExp i j`.
Exact Python: py/mat_root.py (A_j and K_j separately are NOT root vectors; N_j is, for all 24 j).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open Option2.NativeStress.HTPhaseKron

/-! ## Weight basis, generic over a ring with a chosen square root of `-1` -/

section Generic
variable {R : Type*} [CommRing R]

def xg (x : Fin 27 → R) (n : ℕ) : R := if h : n < 27 then x ⟨n, h⟩ else 0

/-- Weight-basis coordinates. -/
def wbG (iR : R) (x : Fin 27 → R) : Fin 27 → R := fun c =>
  if c.val < 3 then x c else
    if (c.val - 3) % 2 = 0 then xg x c.val - iR * xg x (c.val + 1)
    else xg x (c.val - 1) + iR * xg x c.val

/-- Twice the inverse change of basis. -/
def wiG (iR : R) (y : Fin 27 → R) : Fin 27 → R := fun c =>
  if c.val < 3 then 2 * y c else
    if (c.val - 3) % 2 = 0 then xg y c.val + xg y (c.val + 1)
    else iR * (xg y (c.val - 1) - xg y c.val)

/-- Column `n` of twice the inverse change of basis, contracted with a row `f`. -/
def colG (iR : R) (f : Fin 27 → R) (n : Fin 27) : R :=
  if n.val < 3 then 2 * f n else
    if (n.val - 3) % 2 = 0 then xg f n.val + iR * xg f (n.val + 1)
    else xg f (n.val - 1) - iR * xg f n.val

/-- Transposition: `Σ_p f_p (W' y)_p = Σ_q (W'^T f)_q y_q`. -/
theorem wiG_transp (iR : R) (f y : Fin 27 → R) :
    ∑ p, f p * wiG iR y p = ∑ q, colG iR f q * y q := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wiG, colG, xg]
  simp
  ring_nf

theorem wiG_single (iR : R) (f : Fin 27 → R) (n : Fin 27) :
    ∑ p, f p * wiG iR (Pi.single n 1) p = colG iR f n := by
  rw [wiG_transp, Finset.sum_eq_single n]
  · simp
  · intro q _ hq; simp [hq]
  · simp

variable {S : Type*} [CommRing S]

theorem xg_map (f : R →+* S) (x : Fin 27 → R) (n : ℕ) : f (xg x n) = xg (fun c => f (x c)) n := by
  unfold xg; split_ifs <;> simp

theorem wbG_map (f : R →+* S) (iR : R) (x : Fin 27 → R) (c : Fin 27) :
    f (wbG iR x c) = wbG (f iR) (fun c => f (x c)) c := by
  unfold wbG; split_ifs <;> simp [xg_map]

theorem colG_map (f : R →+* S) (iR : R) (g : Fin 27 → R) (n : Fin 27) :
    f (colG iR g n) = colG (f iR) (fun c => f (g c)) n := by
  unfold colG; split_ifs <;> simp [xg_map, map_ofNat]

theorem wiG_map (f : R →+* S) (iR : R) (y : Fin 27 → R) (c : Fin 27) :
    f (wiG iR y c) = wiG (f iR) (fun c => f (y c)) c := by
  unfold wiG; split_ifs <;> simp [xg_map, map_ofNat]

end Generic

/-! ## Over `ℂ` -/

/-- Weight-basis coordinates as a linear map. -/
def wbL : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) where
  toFun := wbG Complex.I
  map_add' x y := by funext c; simp only [wbG, xg, Pi.add_apply]; split_ifs <;> ring
  map_smul' a x := by funext c; simp only [wbG, xg, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- Inverse change of basis as a linear map. -/
def wiL : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) where
  toFun y := fun c => wiG Complex.I y c / 2
  map_add' x y := by funext c; simp only [wiG, xg, Pi.add_apply]; split_ifs <;> ring
  map_smul' a x := by funext c; simp only [wiG, xg, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem wi_wb (x : Fin 27 → ℂ) : wiL (wbL x) = x := by
  funext c
  change wiG Complex.I (wbG Complex.I x) c / 2 = x c
  fin_cases c <;> simp [wiG, wbG, xg] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem wb_wi (y : Fin 27 → ℂ) : wbL (wiL y) = y := by
  funext c
  change wbG Complex.I (fun c => wiG Complex.I y c / 2) c = y c
  fin_cases c <;> simp [wiG, wbG, xg] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem wbL_injective {x y : Fin 27 → ℂ} (h : wbL x = wbL y) : x = y := by
  rw [← wi_wb x, ← wi_wb y, h]

/-- Line characters of a plane-rotation map in the weight basis. -/
def lamF (χ χ' : ℕ → ℂ) (c : Fin 27) : ℂ :=
  if c.val < 3 then 1 else if (c.val - 3) % 2 = 0 then χ ((c.val - 3) / 2) else χ' ((c.val - 3) / 2)

theorem wb_rot (χ χ' : ℕ → ℂ) (x : Fin 27 → ℂ) (c : Fin 27) :
    wbL (rotForm 1 χ χ' x) c = lamF χ χ' c * wbL x c := by
  change wbG Complex.I (rotForm 1 χ χ' x) c = lamF χ χ' c * wbG Complex.I x c
  fin_cases c <;> simp [wbG, rotForm, xn, xg, lamF] <;> ring_nf <;>
    simp only [Complex.I_sq, I_cube] <;> ring

/-- The plane-rotation map as a linear map. -/
def rotL (χ χ' : ℕ → ℂ) : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) where
  toFun := rotForm 1 χ χ'
  map_add' := rotForm_add 1 χ χ'
  map_smul' a x := rotForm_smul 1 χ χ' a x

/-- **Generic root lemma.** If every nonzero weight-basis entry `(c, n)` of `M` has `λ_c = μ λ_n`, then
`R (M x) = μ • M (R x)` for the plane-rotation map `R`. -/
theorem root_of_weight (M : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (χ χ' : ℕ → ℂ) (μ : ℂ)
    (h : ∀ n c : Fin 27, wbL (M (wiL (Pi.single n 1))) c = 0 ∨ lamF χ χ' c = μ * lamF χ χ' n)
    (x : Fin 27 → ℂ) : rotForm 1 χ χ' (M x) = μ • M (rotForm 1 χ χ' x) := by
  have hx : ∀ y : Fin 27 → ℂ, y = ∑ n, wbL y n • wiL (Pi.single n 1) := by
    intro y
    conv_lhs => rw [← wi_wb y, ← Finset.univ_sum_single (wbL y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← map_smul]
    congr 1
    funext p
    by_cases hp : p = n
    · subst hp; simp
    · simp [hp]
  have hrot : ∀ n, rotForm 1 χ χ' (wiL (Pi.single n 1)) = lamF χ χ' n • wiL (Pi.single n 1) := by
    intro n
    apply wbL_injective
    funext c
    rw [wb_rot, map_smul, Pi.smul_apply, wb_wi, smul_eq_mul]
    by_cases hc : c = n
    · subst hc; rfl
    · simp [hc]
  have hM : ∀ n, rotForm 1 χ χ' (M (wiL (Pi.single n 1))) =
      (μ * lamF χ χ' n) • M (wiL (Pi.single n 1)) := by
    intro n
    apply wbL_injective
    funext c
    rw [wb_rot, map_smul, Pi.smul_apply, smul_eq_mul]
    rcases h n c with h0 | h1
    · rw [h0, mul_zero, mul_zero]
    · rw [h1]
  have e1 : rotForm 1 χ χ' (M x) = rotL χ χ' (M x) := rfl
  have e2 : rotForm 1 χ χ' x = rotL χ χ' x := rfl
  rw [e1, e2, hx x]
  simp only [map_sum, map_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  change wbL x n • rotForm 1 χ χ' (M (wiL (Pi.single n 1))) =
    μ • (wbL x n • M (rotForm 1 χ χ' (wiL (Pi.single n 1))))
  rw [hM, hrot, map_smul, smul_smul, smul_smul, smul_smul]
  congr 1; ring

/-! ## The anchor operators -/

/-- Entry of `N_j` (same expression as VALUE's `nOp`). -/
def nEnt (j : Fin 24) (m n : Fin 27) : ℂ := Q12.toComplex kHalf * Q12.toComplex (gToQ12 (nZ j m n))

/-- `N_j` on one native state. -/
def nLin (j : Fin 24) : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) where
  toFun s := fun m => ∑ n, nEnt j m n * s n
  map_add' x y := by funext m; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring

/-- Gaussian-integer weight-basis entry `4 · (W N_j W⁻¹)_{c n}`. -/
def zK (j : Fin 24) (n c : Fin 27) : GaussianInt :=
  wbG gaussI (fun m => colG gaussI (fun q => nZ j m q) n) c

/-- Composite ring map `ℤ[i] → ℂ`. -/
def gC : GaussianInt →+* ℂ := Q12.toComplex.comp gToQ12

theorem gC_gaussI : gC gaussI = Complex.I := by
  simp only [gC, RingHom.comp_apply, gToQ12_gaussI, Q12.toComplex_I]

theorem kHalf_c : Q12.toComplex kHalf = 1 / 2 := by
  simp only [kHalf, Q12.toComplex_ofRat]; push_cast; ring

theorem zK_bridge (j : Fin 24) (n c : Fin 27) :
    wbL (nLin j (wiL (Pi.single n 1))) c = gC (zK j n c) / 4 := by
  have hm : nLin j (wiL (Pi.single n 1)) =
      (1 / 4 : ℂ) • fun m => colG Complex.I (fun q => gC (nZ j m q)) n := by
    funext m
    change ∑ p, nEnt j m p * (wiG Complex.I (Pi.single n 1) p / 2) = _
    rw [Pi.smul_apply, smul_eq_mul, ← wiG_single, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [nEnt, kHalf_c, gC, RingHom.comp_apply]; ring
  rw [hm, map_smul, Pi.smul_apply, smul_eq_mul]
  change 1 / 4 * wbG Complex.I _ c = _
  unfold zK
  rw [wbG_map, gC_gaussI]
  simp only [colG_map, gC_gaussI]
  ring

/-! ## Weights and the kernel checks -/

/-- Weight (exponent of the line character of `d_i(U)`) of weight-basis coordinate `c`. -/
def wexp (i : Fin 4) (c : Fin 27) : Ex :=
  if c.val < 3 then (0, 0, 0, 0) else
    if (c.val - 3) % 2 = 0 then dExp i ((c.val - 3) / 2) else Ex.neg (dExp i ((c.val - 3) / 2))

/-- Root exponent of `N_j` for the torus of quartet `i` (exact Python py/mat_root.py). -/
def rootExp (i : Fin 4) (j : Fin 24) : Ex :=
  if i = 2 then
    [(1, 2, 0, 0), (1, -1, 0, 0), (-2, -1, 0, 0), (-1, -2, 0, 0), (2, 1, 0, 0), (-1, 1, 0, 0),
      (-1, 0, 0, 0), (0, -1, 0, 0), (1, 1, 0, 0), (0, -1, 0, 0), (1, 1, 0, 0), (-1, 0, 0, 0),
      (1, 1, 0, 0), (-1, 0, 0, 0), (0, -1, 0, 0), (1, 0, 0, 0), (-1, -1, 0, 0), (0, 1, 0, 0),
      (-1, -1, 0, 0), (0, 1, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (1, 0, 0, 0), (-1, -1, 0, 0)].getD j.val (0, 0, 0, 0)
  else if i = 3 then
    [(0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0),
      (0, 0, 0, -1), (0, 0, 0, -1), (0, 0, 0, -1), (0, 0, 1, 1), (0, 0, 1, 1), (0, 0, 1, 1),
      (0, 0, -1, 0), (0, 0, -1, 0), (0, 0, -1, 0), (0, 0, 0, 1), (0, 0, 0, 1), (0, 0, 0, 1),
      (0, 0, 1, 0), (0, 0, 1, 0), (0, 0, 1, 0), (0, 0, -1, -1), (0, 0, -1, -1), (0, 0, -1, -1)].getD j.val (0, 0, 0, 0)
  else (0, 0, 0, 0)

/-- Weight condition for the weight-basis entry `(c, n)` of `N_j`. -/
def wB (i : Fin 4) (j : Fin 24) (c n : Fin 27) : Bool :=
  decide (Ex.neg (wexp i c) = Ex.add (rootExp i j) (Ex.neg (wexp i n)))

/-- The coordinates of `J_s` (diagonal and the three planes of window `s`). -/
def jList (s : ℕ) : List (Fin 27) := (List.finRange 27).filter (jMem s)

/-- `N_j` on `J_s × J_s`, materialised once (VALUE's support theorem `nZ_support`: zero elsewhere). -/
def Tab (j : Fin 24) : List (List GaussianInt) :=
  (jList (sheetOf j)).map fun m => (jList (sheetOf j)).map fun q => nZ j m q

/-- Table lookup, extended by zero off `J_s × J_s`. -/
def tabF (T : List (List GaussianInt)) (s : ℕ) (m q : Fin 27) : GaussianInt :=
  if jMem s m = true ∧ jMem s q = true then
    (T.getD ((jList s).idxOf m) []).getD ((jList s).idxOf q) 0 else 0

def zT (T : List (List GaussianInt)) (s : ℕ) (n c : Fin 27) : GaussianInt :=
  wbG gaussI (fun m => colG gaussI (fun q => tabF T s m q) n) c

def rootCheckT (i : Fin 4) (j : Fin 24) (T : List (List GaussianInt)) : Bool :=
  (List.finRange 27).all fun n => (List.finRange 27).all fun c =>
    wB i j c n || decide (zT T (sheetOf j) n c = 0)

/-- Kernel check for one `j`, both moving quartets (the table is shared). -/
def rootCheck (j : Fin 24) : Bool :=
  let T := Tab j
  rootCheckT 2 j T && rootCheckT 3 j T

theorem mem_jList {s : ℕ} {m : Fin 27} (h : jMem s m = true) : m ∈ jList s :=
  List.mem_filter.mpr ⟨List.mem_finRange m, h⟩

theorem tabF_eq (j : Fin 24) (m q : Fin 27) : tabF (Tab j) (sheetOf j) m q = nZ j m q := by
  unfold tabF
  split_ifs with h
  · have pm := List.idxOf_lt_length_of_mem (mem_jList h.1)
    have pq := List.idxOf_lt_length_of_mem (mem_jList h.2)
    unfold Tab
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem pm,
      List.getElem?_eq_getElem pq, Option.map_some, Option.getD_some, List.getElem_idxOf]
  · by_contra hne
    exact h (nZ_support j m q (Ne.symm hne))

theorem zT_eq (j : Fin 24) (n c : Fin 27) : zT (Tab j) (sheetOf j) n c = zK j n c := by
  unfold zT zK
  simp only [tabF_eq]

theorem rootCheck_0 : rootCheck 0 = true := by decide +kernel
theorem rootCheck_1 : rootCheck 1 = true := by decide +kernel
theorem rootCheck_2 : rootCheck 2 = true := by decide +kernel
theorem rootCheck_3 : rootCheck 3 = true := by decide +kernel
theorem rootCheck_4 : rootCheck 4 = true := by decide +kernel
theorem rootCheck_5 : rootCheck 5 = true := by decide +kernel
theorem rootCheck_6 : rootCheck 6 = true := by decide +kernel
theorem rootCheck_7 : rootCheck 7 = true := by decide +kernel
theorem rootCheck_8 : rootCheck 8 = true := by decide +kernel
theorem rootCheck_9 : rootCheck 9 = true := by decide +kernel
theorem rootCheck_10 : rootCheck 10 = true := by decide +kernel
theorem rootCheck_11 : rootCheck 11 = true := by decide +kernel
theorem rootCheck_12 : rootCheck 12 = true := by decide +kernel
theorem rootCheck_13 : rootCheck 13 = true := by decide +kernel
theorem rootCheck_14 : rootCheck 14 = true := by decide +kernel
theorem rootCheck_15 : rootCheck 15 = true := by decide +kernel
theorem rootCheck_16 : rootCheck 16 = true := by decide +kernel
theorem rootCheck_17 : rootCheck 17 = true := by decide +kernel
theorem rootCheck_18 : rootCheck 18 = true := by decide +kernel
theorem rootCheck_19 : rootCheck 19 = true := by decide +kernel
theorem rootCheck_20 : rootCheck 20 = true := by decide +kernel
theorem rootCheck_21 : rootCheck 21 = true := by decide +kernel
theorem rootCheck_22 : rootCheck 22 = true := by decide +kernel
theorem rootCheck_23 : rootCheck 23 = true := by decide +kernel

theorem rootCheck_all (j : Fin 24) : rootCheck j = true := by
  fin_cases j
  exacts [rootCheck_0, rootCheck_1, rootCheck_2, rootCheck_3, rootCheck_4, rootCheck_5, rootCheck_6, rootCheck_7, rootCheck_8, rootCheck_9, rootCheck_10, rootCheck_11, rootCheck_12, rootCheck_13, rootCheck_14, rootCheck_15, rootCheck_16, rootCheck_17, rootCheck_18, rootCheck_19, rootCheck_20, rootCheck_21, rootCheck_22, rootCheck_23]

theorem lamF_cartan (U : Fin 4 → ℂˣ) (i : Fin 4) (c : Fin 27) :
    lamF (fun p => mono (Uinv U) (dExp i p)) (fun p => mono (Uinv U) (Ex.neg (dExp i p))) c =
      mono U (Ex.neg (wexp i c)) := by
  unfold lamF wexp
  split_ifs
  · simp [Ex.neg, mono_zero]
  · dsimp only; rw [mono_Uinv]
  · dsimp only; rw [mono_Uinv]

/-- **Root property** of `N_j` for the Cartan lifts of quartets 2 and 3, every unit tuple `U`. -/
theorem root_N (U : Fin 4 → ℂˣ) (i : Fin 4) (hi : i = 2 ∨ i = 3) (j : Fin 24) (s : Fin 27 → ℂ) :
    cartanFun (Uinv U) i (nLin j s) = mono U (rootExp i j) • nLin j (cartanFun (Uinv U) i s) := by
  rw [cartanFun_eq_rot]
  apply root_of_weight
  intro n c
  have hc : rootCheckT i j (Tab j) = true := by
    have h := rootCheck_all j
    simp only [rootCheck, Bool.and_eq_true] at h
    rcases hi with rfl | rfl
    · exact h.1
    · exact h.2
  unfold rootCheckT at hc
  simp only [List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
    decide_eq_true_eq] at hc
  rcases hc n c with hw | hz
  · right
    rw [lamF_cartan, lamF_cartan, mono_mul]
    unfold wB at hw
    rw [decide_eq_true_eq] at hw
    rw [hw]
  · left
    rw [zK_bridge, ← zT_eq, hz, map_zero, zero_div]

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.root_of_weight
#print axioms Option2.NativeStress.HTPhaseComplete.zK_bridge
#print axioms Option2.NativeStress.HTPhaseComplete.rootCheck_all
#print axioms Option2.NativeStress.HTPhaseComplete.tabF_eq
#print axioms Option2.NativeStress.HTPhaseComplete.root_N

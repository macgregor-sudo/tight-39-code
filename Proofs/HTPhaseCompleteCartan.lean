module

public import AutS
public import HTPhaseKronBridge4

@[expose] public section

/-!
# F4 Cartan automorphisms `d_i(u)` for the H transport (first-party)

The diagonal Tits-pair action `TitsS.pairAct ι h (diag g) (diag k)` (accepted A4 tree, `AutS.lean`,
`pairAct_isAut`: product, unit, trace and pairing preserved whenever `det g = det k = 1`) is, in
native coordinates, a plane-rotation map `rotForm`: the diagonal is scaled by `det g`, and on native
plane `j` (coordinates `3+2j, 4+2j`) the line `x - i y` is multiplied by `chiA j` and `x + i y` by
`chiB j`, explicit products of the diagonal entries (`pairAct_diag`, a ring identity).

The Cartan lift of quartet `i` is the choice of diagonal Laurent monomials in the phase units
`U = ξ/ξ_base`:
* `i = 0, 1`: `g = k = 1` (windows 0 and 1 do not move at literal phases);
* `i = 2`: `g = diag(u0 u1, u1⁻¹, u0⁻¹)`, `k = 1`;
* `i = 3`: `g = 1`, `k = diag(u3, (u2 u3)⁻¹, u2)`.
On the planes of window `i` its characters equal the literal phase characters `planeExp`; on the
other planes they differ (that is why it is NOT a global transport of the literal configuration).
The anchor-matching statement proved here is exactly what the H transport uses: `d_i(U) · P_k =
Φ(U)_k` for the twelve states `k` of quartet `i` (frame 0 and window `i`) only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open Matrix TitsS NativePolynomial.CoordinateMaps Option2.NativeStress.HTPhaseKron

/-- Native coordinate by natural index, zero-padded. -/
def xn (x : Fin 27 → ℂ) (n : ℕ) : ℂ := if h : n < 27 then x ⟨n, h⟩ else 0

/-- The plane-rotation form (diagonal scaled by `δ`; characters `χ` on `x - i y`, `χ'` on `x + i y`). -/
def rotForm (δ : ℂ) (χ χ' : ℕ → ℂ) (x : Fin 27 → ℂ) : Fin 27 → ℂ := fun c =>
  if c.val < 3 then δ * x c else
    if (c.val - 3) % 2 = 0 then
      (χ ((c.val - 3) / 2) * (xn x c.val - Complex.I * xn x (c.val + 1)) +
        χ' ((c.val - 3) / 2) * (xn x c.val + Complex.I * xn x (c.val + 1))) / 2
    else
      Complex.I * (χ ((c.val - 3) / 2) * (xn x (c.val - 1) - Complex.I * xn x c.val) -
        χ' ((c.val - 3) / 2) * (xn x (c.val - 1) + Complex.I * xn x c.val)) / 2

/-- Line character of the diagonal Tits-pair action (`x - i y` line of plane `j`). -/
def chiA (a0 a1 a2 b0 b1 b2 : ℂ) : ℕ → ℂ
  | 0 => a1 ^ 2 * a2 | 1 => a2 * b1 * b2 | 2 => a2 * b0 * b2 | 3 => a0 * a1 * b2
  | 4 => a1 * a2 ^ 2 | 5 => a1 * b1 * b2 | 6 => a1 * b0 * b2 | 7 => a0 * a2 * b2
  | 8 => a0 * a2 ^ 2 | 9 => a0 * b1 * b2 | 10 => a0 * b0 * b2 | 11 => a1 * a2 * b2
  | _ => 1

/-- Line character of the diagonal Tits-pair action (`x + i y` line of plane `j`). -/
def chiB (a0 a1 a2 b0 b1 b2 : ℂ) : ℕ → ℂ
  | 0 => a0 ^ 2 * a2 | 1 => a0 * a1 * b0 | 2 => a0 * a1 * b1 | 3 => a2 * b0 * b1
  | 4 => a0 ^ 2 * a1 | 5 => a0 * a2 * b0 | 6 => a0 * a2 * b1 | 7 => a1 * b0 * b1
  | 8 => a0 * a1 ^ 2 | 9 => a1 * a2 * b0 | 10 => a1 * a2 * b1 | 11 => a0 * b0 * b1
  | _ => 1

/-- The diagonal Tits-pair action IS a plane-rotation map (a ring identity, no det hypothesis). -/
theorem pairAct_diag (a0 a1 a2 b0 b1 b2 : ℂ) (x : Fin 27 → ℂ) :
    pairAct Q12.toComplex (1 / 2 : ℂ) (diagonal ![a0, a1, a2]) (diagonal ![b0, b1, b2]) x =
      rotForm (a0 * a1 * a2) (chiA a0 a1 a2 b0 b1 b2) (chiB a0 a1 a2 b0 b1 b2) x := by
  funext c
  fin_cases c <;>
    simp [-Matrix.adjugate_diagonal, pairAct, titsToNative, titsAct, titsOfNative, cA, cB, cBt,
      rotForm, xn, chiA, chiB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three,
      Matrix.diagonal_apply, Q12.toComplex_I] <;>
    (ring_nf; try simp only [Complex.I_sq, Complex.I_pow_four]; try ring_nf)


/-! ## Generic algebra of `rotForm` -/

theorem I_cube : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq, neg_one_mul]

theorem rotForm_add (δ : ℂ) (χ χ' : ℕ → ℂ) (x y : Fin 27 → ℂ) :
    rotForm δ χ χ' (x + y) = rotForm δ χ χ' x + rotForm δ χ χ' y := by
  funext c
  simp only [rotForm, xn, Pi.add_apply]
  split_ifs <;> ring

theorem rotForm_smul (δ : ℂ) (χ χ' : ℕ → ℂ) (a : ℂ) (x : Fin 27 → ℂ) :
    rotForm δ χ χ' (a • x) = a • rotForm δ χ χ' x := by
  funext c
  simp only [rotForm, xn, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Composition multiplies the line characters. -/
theorem rotForm_comp (χ χ' ψ ψ' : ℕ → ℂ) (x : Fin 27 → ℂ) :
    rotForm 1 χ χ' (rotForm 1 ψ ψ' x) = rotForm 1 (χ * ψ) (χ' * ψ') x := by
  funext c
  fin_cases c <;> simp [rotForm, xn] <;> ring_nf <;>
    simp only [Complex.I_sq, I_cube, Complex.I_pow_four] <;> ring

theorem rotForm_one (x : Fin 27 → ℂ) : rotForm 1 1 1 x = x := by
  funext c
  fin_cases c <;> simp [rotForm, xn] <;> ring_nf <;>
    simp only [Complex.I_sq, I_cube, Complex.I_pow_four] <;> ring

/-- Agreement: characters may differ on a plane where the vector has no component. -/
theorem rotForm_congr (δ : ℂ) (χ χ' ψ ψ' : ℕ → ℂ) (x : Fin 27 → ℂ)
    (h : ∀ j, j < 12 → (χ j = ψ j ∧ χ' j = ψ' j) ∨ (xn x (3 + 2 * j) = 0 ∧ xn x (4 + 2 * j) = 0)) :
    rotForm δ χ χ' x = rotForm δ ψ ψ' x := by
  funext c
  have hc := c.isLt
  unfold rotForm
  split_ifs with h3 he
  · rfl
  · rcases h ((c.val - 3) / 2) (by omega) with ⟨e1, e2⟩ | ⟨z1, z2⟩
    · rw [e1, e2]
    · have i1 : 3 + 2 * ((c.val - 3) / 2) = c.val := by omega
      have i2 : 4 + 2 * ((c.val - 3) / 2) = c.val + 1 := by omega
      rw [i1] at z1; rw [i2] at z2
      rw [z1, z2]; ring
  · rcases h ((c.val - 3) / 2) (by omega) with ⟨e1, e2⟩ | ⟨z1, z2⟩
    · rw [e1, e2]
    · have i1 : 3 + 2 * ((c.val - 3) / 2) = c.val - 1 := by omega
      have i2 : 4 + 2 * ((c.val - 3) / 2) = c.val := by omega
      rw [i1] at z1; rw [i2] at z2
      rw [z1, z2]; ring

/-! ## The Cartan lifts `d_i(U)` -/

section Lift

variable (U : Fin 4 → ℂˣ)

/-- Exponents of `g = diag(g0, g1, g2)` (quartet 2 moves `g`). -/
def gExp (i : Fin 4) : Fin 3 → Ex :=
  if i = 2 then ![(1, 1, 0, 0), (0, -1, 0, 0), (-1, 0, 0, 0)] else fun _ => (0, 0, 0, 0)

/-- Exponents of `k = diag(k0, k1, k2)` (quartet 3 moves `k`). -/
def kExp (i : Fin 4) : Fin 3 → Ex :=
  if i = 3 then ![(0, 0, 0, 1), (0, 0, -1, -1), (0, 0, 1, 0)] else fun _ => (0, 0, 0, 0)

/-- Resulting exponent of the `x - i y` line of native plane `j` (computed, py/tits_torus.py). -/
def dExp (i : Fin 4) (j : ℕ) : Ex :=
  if i = 2 then
    match j with
    | 0 => (-1, -2, 0, 0) | 1 => (-1, 0, 0, 0) | 2 => (-1, 0, 0, 0) | 3 => (1, 0, 0, 0)
    | 4 => (-2, -1, 0, 0) | 5 => (0, -1, 0, 0) | 6 => (0, -1, 0, 0) | 7 => (0, 1, 0, 0)
    | 8 => (-1, 1, 0, 0) | 9 => (1, 1, 0, 0) | 10 => (1, 1, 0, 0) | 11 => (-1, -1, 0, 0)
    | _ => (0, 0, 0, 0)
  else if i = 3 then
    match j with
    | 1 => (0, 0, 0, -1) | 2 => (0, 0, 1, 1) | 3 => (0, 0, 1, 0)
    | 5 => (0, 0, 0, -1) | 6 => (0, 0, 1, 1) | 7 => (0, 0, 1, 0)
    | 9 => (0, 0, 0, -1) | 10 => (0, 0, 1, 1) | 11 => (0, 0, 1, 0)
    | _ => (0, 0, 0, 0)
  else (0, 0, 0, 0)

theorem dExp_high (i : Fin 4) (j : ℕ) : dExp i (j + 12) = (0, 0, 0, 0) := by
  unfold dExp; split_ifs <;> rfl

/-- Literal phase exponent of plane `j` (`planeExp`, zero on fixed planes). -/
def litExp (j : ℕ) : Ex := (planeExp j).getD (0, 0, 0, 0)

noncomputable def gDiag (i : Fin 4) : M3 ℂ :=
  diagonal ![mono U (gExp i 0), mono U (gExp i 1), mono U (gExp i 2)]

noncomputable def kDiag (i : Fin 4) : M3 ℂ :=
  diagonal ![mono U (kExp i 0), mono U (kExp i 1), mono U (kExp i 2)]

/-- `d_i(U)` as a native coordinate map: the accepted diagonal Tits-pair action. -/
noncomputable def cartanFun (i : Fin 4) : (Fin 27 → ℂ) → (Fin 27 → ℂ) :=
  pairAct Q12.toComplex (1 / 2 : ℂ) (gDiag U i) (kDiag U i)

theorem mono_zero : mono U ((0, 0, 0, 0) : Ex) = 1 := by simp [mono]

theorem mono_mul (x y : Ex) : mono U x * mono U y = mono U (Ex.add x y) := (mono_add U x y).symm

theorem det_gDiag (i : Fin 4) : (gDiag U i).det = 1 := by
  rw [gDiag, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [mono_mul, mono_mul, ← mono_zero U]
  congr 1
  fin_cases i <;> decide

theorem det_kDiag (i : Fin 4) : (kDiag U i).det = 1 := by
  rw [kDiag, det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [mono_mul, mono_mul, ← mono_zero U]
  congr 1
  fin_cases i <;> decide

/-- **(a) `d_i(U)` is a native automorphism**: product (h = 1/2), unit, trace, pairing preserved,
for every unit tuple `U` (accepted `TitsS.pairAct_isAut`). -/
theorem cartan_isAut (i : Fin 4) : IsAut (1 / 2 : ℂ) (cartanFun U i) :=
  pairAct_isAut Q12.toComplex (1 / 2 : ℂ) (by norm_num) (det_gDiag U i) (det_kDiag U i)

/-- The plane-rotation form of `d_i(U)`: line characters `U^{dExp i j}` and `U^{-dExp i j}`. -/
theorem cartanFun_eq_rot (i : Fin 4) :
    cartanFun U i = rotForm 1 (fun j => mono U (dExp i j)) (fun j => mono U (Ex.neg (dExp i j))) := by
  funext x
  rw [cartanFun, gDiag, kDiag, pairAct_diag]
  have hdet : mono U (gExp i 0) * mono U (gExp i 1) * mono U (gExp i 2) = 1 := by
    rw [mono_mul, mono_mul, ← mono_zero U]; congr 1; fin_cases i <;> decide
  rw [hdet]
  congr 1
  · funext j
    rcases j with _|_|_|_|_|_|_|_|_|_|_|_|j
    all_goals first
      | (simp only [chiA, pow_two, mono_mul]; congr 1; fin_cases i <;> decide)
      | (show (1 : ℂ) = _; rw [dExp_high, mono_zero])
  · funext j
    rcases j with _|_|_|_|_|_|_|_|_|_|_|_|j
    all_goals first
      | (simp only [chiB, pow_two, mono_mul]; congr 1; fin_cases i <;> decide)
      | (show (1 : ℂ) = _; rw [dExp_high]; simpa [Ex.neg] using (mono_zero U).symm)

/-- `d_i(U)` as a complex-linear map on native vectors. -/
noncomputable def cartanLin (i : Fin 4) : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ) where
  toFun := cartanFun U i
  map_add' x y := (cartan_isAut U i).map_add x y
  map_smul' a x := by rw [cartanFun_eq_rot]; exact rotForm_smul _ _ _ a x

/-- Pointwise inverse units. -/
def Uinv : Fin 4 → ℂˣ := fun a => (U a)⁻¹

theorem mono_Uinv (m : Ex) : mono (Uinv U) m = mono U (Ex.neg m) := by
  simp [mono, Uinv, Ex.neg, _root_.inv_zpow', Units.val_mul]

theorem mono_mul_neg (m : Ex) : mono U m * mono U (Ex.neg m) = 1 := by
  rw [mono_mul, ← mono_zero U]; congr 1
  obtain ⟨a, b, c, d⟩ := m
  simp [Ex.add, Ex.neg]

/-- `d_i(U⁻¹)` is the inverse of `d_i(U)`. -/
theorem cartanFun_inv_comp (i : Fin 4) (x : Fin 27 → ℂ) :
    cartanFun (Uinv U) i (cartanFun U i x) = x := by
  rw [cartanFun_eq_rot, cartanFun_eq_rot, rotForm_comp]
  have h1 : ((fun j => mono (Uinv U) (dExp i j)) * fun j => mono U (dExp i j)) = 1 := by
    funext j; simp only [Pi.mul_apply, Pi.one_apply, mono_Uinv]; rw [mul_comm]; exact mono_mul_neg U _
  have h2 : ((fun j => mono (Uinv U) (Ex.neg (dExp i j))) * fun j => mono U (Ex.neg (dExp i j))) = 1 := by
    funext j; simp only [Pi.mul_apply, Pi.one_apply, mono_Uinv]
    obtain ⟨a, b, c, d⟩ := dExp i j
    rw [mul_comm]
    simpa [Ex.neg] using mono_mul_neg U (-a, -b, -c, -d)
  rw [h1, h2, rotForm_one]

theorem cartanFun_comp_inv (i : Fin 4) (x : Fin 27 → ℂ) :
    cartanFun U i (cartanFun (Uinv U) i x) = x := by
  have h : Uinv (Uinv U) = U := by funext a; simp [Uinv]
  conv_lhs => rw [← h]
  exact cartanFun_inv_comp (Uinv U) i x

end Lift

/-! ## Anchor matching (b) -/

/-- The base state `k` (original `baseQ12`, = literal configuration at `exactPhases`). -/
noncomputable def bvec (k : ℕ) : Fin 27 → ℂ := fun c => Q12.toComplex (bq (27 * k + c.val))

theorem xn_bvec (k c : ℕ) (hc : c < 27) : xn (bvec k) c = Q12.toComplex (bq (27 * k + c)) := by
  simp [xn, hc, bvec]

/-- The literal Laurent configuration is the LITERAL plane rotation `g(U)` of the base, statewise
(all 39 states; this map is not an automorphism). -/
theorem phiR_rot (U : Fin 4 → ℂˣ) (v : Fin 1053) :
    PhiR Q12.toComplex U v =
      rotForm 1 (fun j => mono U (litExp j)) (fun j => mono U (Ex.neg (litExp j)))
        (bvec (v.val / 27)) ⟨v.val % 27, Nat.mod_lt _ (by norm_num)⟩ := by
  have hv := v.isLt
  have hsplit : 27 * (v.val / 27) + v.val % 27 = v.val := Nat.div_add_mod _ _
  by_cases h3 : v.val % 27 < 3
  · rw [PhiR_fixed _ _ v (Or.inl h3)]
    simp only [rotForm, h3, ite_true, one_mul, bvec, hsplit]
  · by_cases he : (v.val % 27 - 3) % 2 = 0
    · cases hpe : planeExp ((v.val % 27 - 3) / 2) with
      | none =>
        rw [PhiR_fixed _ _ v (Or.inr hpe)]
        simp only [rotForm, h3, ite_false, he, ite_true, litExp, hpe, Option.getD_none]
        rw [xn_bvec _ _ (by omega), xn_bvec _ _ (by omega), hsplit]
        simp only [Ex.neg, neg_zero, mono_zero]; ring
      | some m =>
        rw [PhiR_even _ _ v m h3 hpe he]
        simp only [rotForm, h3, ite_false, he, ite_true, litExp, hpe, Option.getD_some]
        rw [xn_bvec _ _ (by omega), xn_bvec _ _ (by omega)]
        have hA : 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) = 27 * (v.val / 27) + v.val % 27 := by
          omega
        rw [hA, Nat.add_assoc, hsplit, toComplex_half, Q12.toComplex_I]; ring
    · cases hpe : planeExp ((v.val % 27 - 3) / 2) with
      | none =>
        rw [PhiR_fixed _ _ v (Or.inr hpe)]
        simp only [rotForm, h3, ite_false, he, litExp, hpe, Option.getD_none]
        rw [xn_bvec _ _ (by omega), xn_bvec _ _ (by omega), hsplit]
        simp only [Ex.neg, neg_zero, mono_zero]; ring_nf; simp only [Complex.I_sq]; ring
      | some m =>
        rw [PhiR_odd _ _ v m h3 hpe he]
        simp only [rotForm, h3, ite_false, he, litExp, hpe, Option.getD_some]
        rw [xn_bvec _ _ (by omega), xn_bvec _ _ (by omega)]
        have hA : 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) = 27 * (v.val / 27) + (v.val % 27 - 1) := by
          omega
        have hB : 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1 = v.val := by omega
        rw [hB, hA, toComplex_half, Q12.toComplex_I, hsplit]; ring

/-- States of quartet `i`: frame 0 and the three frames of window `i` (`AnchorCoordinate` frames). -/
def quartetState (i : Fin 4) (k : ℕ) : Bool :=
  decide (k / 3 = 0 ∨ (1 + 3 * i.val ≤ k / 3 ∧ k / 3 ≤ 3 + 3 * i.val))

/-- The finite certificate behind anchor matching: on every quartet-`i` state, every plane either has
equal `d_i` and literal exponents, or zero base coordinates. -/
noncomputable def anchorOK (i : Fin 4) : Bool :=
  (List.range 39).all fun k => !quartetState i k ||
    (List.range 12).all fun j => decide (dExp i j = litExp j) ||
      (decide (bq (27 * k + (3 + 2 * j)) = 0) && decide (bq (27 * k + (4 + 2 * j)) = 0))

theorem anchorOK_true (i : Fin 4) : anchorOK i = true := by
  fin_cases i <;> decide +kernel

/-- **(b) anchor matching.** For every unit tuple `U` and every state `k` of quartet `i`:
`d_i(U) · P_k = Φ(U)_k`. (False off the quartet for `i = 2, 3`: py/run_H.out.) -/
theorem cartan_anchor_match (U : Fin 4 → ℂˣ) (i : Fin 4) (k : ℕ) (hk : k < 39)
    (hq : quartetState i k = true) (c : Fin 27) :
    cartanFun U i (bvec k) c = PhiR Q12.toComplex U ⟨27 * k + c.val, by omega⟩ := by
  rw [phiR_rot]
  have e1 : (27 * k + c.val) / 27 = k := by omega
  have e2 : (27 * k + c.val) % 27 = c.val := by omega
  simp only [e1, e2]
  rw [cartanFun_eq_rot]
  have h := anchorOK_true i
  simp only [anchorOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq] at h
  have hr := rotForm_congr 1 (fun j => mono U (dExp i j)) (fun j => mono U (Ex.neg (dExp i j)))
    (fun j => mono U (litExp j)) (fun j => mono U (Ex.neg (litExp j))) (bvec k) (by
      intro j hj
      rcases h k hk with hn | hall
      · rw [hq] at hn; exact absurd hn (by decide)
      rcases hall j hj with he | ⟨z1, z2⟩
      · left; rw [he]; exact ⟨rfl, rfl⟩
      · right
        rw [xn_bvec _ _ (by omega), xn_bvec _ _ (by omega), z1, z2, map_zero]
        exact ⟨rfl, rfl⟩)
  rw [hr]

/-- Anchor matching in the direction used by the transport: `d_i(U)⁻¹ · Φ(U)_k = P_k`. -/
theorem cartan_inv_anchor (U : Fin 4 → ℂˣ) (i : Fin 4) (k : ℕ) (hk : k < 39)
    (hq : quartetState i k = true) :
    cartanFun (Uinv U) i (fun c => PhiR Q12.toComplex U ⟨27 * k + c.val, by omega⟩) = bvec k := by
  have : (fun c : Fin 27 => PhiR Q12.toComplex U ⟨27 * k + c.val, by omega⟩) = cartanFun U i (bvec k) := by
    funext c; exact (cartan_anchor_match U i k hk hq c).symm
  rw [this, cartanFun_inv_comp]

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.pairAct_diag
#print axioms Option2.NativeStress.HTPhaseComplete.rotForm_comp
#print axioms Option2.NativeStress.HTPhaseComplete.cartan_isAut
#print axioms Option2.NativeStress.HTPhaseComplete.cartanFun_eq_rot
#print axioms Option2.NativeStress.HTPhaseComplete.cartanFun_inv_comp
#print axioms Option2.NativeStress.HTPhaseComplete.cartanFun_comp_inv
#print axioms Option2.NativeStress.HTPhaseComplete.phiR_rot
#print axioms Option2.NativeStress.HTPhaseComplete.anchorOK_true
#print axioms Option2.NativeStress.HTPhaseComplete.cartan_anchor_match
#print axioms Option2.NativeStress.HTPhaseComplete.cartan_inv_anchor

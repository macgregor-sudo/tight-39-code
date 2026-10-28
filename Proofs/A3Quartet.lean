module

public import A3Interfaces
public import A3QuartetOrbit

@[expose] public section

/-!
# The complete complex quartet: tangent dimension eight
-/

noncomputable section

namespace CKM.NativeFirstOrder

open CompactAlbert UnitaryErrorBases.ComplexQuartet

theorem stdQuartet_idem (k : Fin 4) (t : Fin 3) :
    (stdQuartet k t).val * (stdQuartet k t).val = (stdQuartet k t).val := by
  exact QuartetAux.std_idem k t

/-- The standard complete complex quartet has real first-order dimension eight. -/
theorem finrank_quartetFirstOrder_std :
    Module.finrank ℝ (quartetFirstOrder fun k t => (stdQuartet k t).val) = 8 := by
  exact QuartetAux.finrank_std

/-- Unitary conjugation and frame/outcome relabelling preserve the quartet first-order dimension. -/
theorem finrank_quartetFirstOrder_conj (q : Fin 4 → Fin 3 → TitsComplexMatrix) (g : TitsComplexMatrix)
    (hg : g * g.conjTranspose = 1) (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) :
    Module.finrank ℝ (quartetFirstOrder fun k t => g * q (fperm k) (τ k t) * g.conjTranspose) =
      Module.finrank ℝ (quartetFirstOrder q) := by
  exact QuartetAux.finrank_conj q g hg fperm τ

/-- The clock conjugation `Z⁻¹ = diag(1, ω², ω)` used by `R1` on the standard quartet. -/
def clockInv : TitsComplexMatrix :=
  Matrix.diagonal ![1, UnitaryErrorBases.ThreeCycleFourier.omega ^ 2,
    UnitaryErrorBases.ThreeCycleFourier.omega]

/-- The `R1`-compatible fixed quartet variations: frame 0 fixed, frames 1–3 shifted by one. -/
def quartetClockFixed : Submodule ℝ (Fin 4 → Fin 3 → TitsComplexMatrix) :=
  quartetFirstOrder (fun k t => (stdQuartet k t).val) ⊓
    { carrier := {δ | ∀ k t, δ k t =
        clockInv * δ k (t + if k = 0 then 0 else 1) * clockInv.conjTranspose}
      add_mem' := by
        intro x y hx hy k t
        simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, ← hx k t, ← hy k t]
      zero_mem' := by intro k t; simp
      smul_mem' := by
        intro c x hx k t
        simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← hx k t] }


namespace QuartetAux

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega

theorem clockInv_eq : clockInv = Matrix.diagonal ![1, ω ^ 2, ω] := rfl

theorem clock_std (k : Fin 4) (t : Fin 3) :
    clockInv * (stdQuartet k (t + if k = 0 then 0 else 1)).val * clockInv.conjTranspose =
      (stdQuartet k t).val := by
  rw [clockInv_eq]
  fin_cases k <;> fin_cases t
  exacts [qclock_0_0, qclock_0_1, qclock_0_2, qclock_1_0, qclock_1_1, qclock_1_2, qclock_2_0,
    qclock_2_1, qclock_2_2, qclock_3_0, qclock_3_1, qclock_3_2]

theorem clock_entry (M : TitsComplexMatrix) (i j : Fin 3) :
    (clockInv * M * clockInv.conjTranspose) i j =
      (![1, ω ^ 2, ω] : Fin 3 → ℂ) i * M i j * star ((![1, ω ^ 2, ω] : Fin 3 → ℂ) j) := by
  rw [clockInv_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp [UnitaryErrorBases.ThreeCycleFourier.omega] at this

theorem omega_sq_ne_one : ω ^ 2 ≠ 1 := by
  rw [w2]
  intro h
  have := congrArg Complex.im h
  simp [UnitaryErrorBases.ThreeCycleFourier.omega] at this

theorem fix_zero (z a b : ℂ) (h : z = a * z * b) (hab : a * b ≠ 1) : z = 0 := by
  have e : z * (1 - a * b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp e with h1 | h1
  · exact h1
  · exact absurd (by linear_combination -h1) hab

theorem conj_comm_diag (Z D Q : TitsComplexMatrix) (h1 : Z * D = D * Z)
    (h2 : D * Z.conjTranspose = Z.conjTranspose * D) :
    Z * (D * Q - Q * D) * Z.conjTranspose =
      D * (Z * Q * Z.conjTranspose) - Z * Q * Z.conjTranspose * D := by
  calc Z * (D * Q - Q * D) * Z.conjTranspose =
        (Z * D) * Q * Z.conjTranspose - Z * Q * (D * Z.conjTranspose) := by noncomm_ring
    _ = (D * Z) * Q * Z.conjTranspose - Z * Q * (Z.conjTranspose * D) := by rw [h1, h2]
    _ = D * (Z * Q * Z.conjTranspose) - Z * Q * Z.conjTranspose * D := by noncomm_ring

/-- The two clock-compatible coordinates. -/
def cvec (u v : ℝ) : Fin 8 → ℝ := ![0, 0, 0, 0, 0, 0, u, v]

theorem Xmat_cvec (u v : ℝ) :
    Xmat (cvec u v) = Matrix.diagonal fun i => Xmat (cvec u v) i i := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, cvec]

theorem diag_comm (d e : Fin 3 → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem clock_mem (u v : ℝ) : orbitL (Xmat (cvec u v)) ∈ quartetClockFixed := by
  refine Submodule.mem_inf.mpr ⟨orbit_mem _ (Xmat_skew _), ?_⟩
  show ∀ k t, orbitL (Xmat (cvec u v)) k t =
    clockInv * orbitL (Xmat (cvec u v)) k (t + if k = 0 then 0 else 1) * clockInv.conjTranspose
  intro k t
  simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Xmat_cvec, conj_comm_diag, clock_std]
  · rw [clockInv_eq]; exact diag_comm _ _
  · rw [clockInv_eq, Matrix.diagonal_conjTranspose]; exact diag_comm _ _

/-- The two clock-compatible coordinates of a variation. -/
def rhoL : Var →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun δ := ![(δ 1 0 0 1).im, (δ 1 0 1 2).im]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

def rhoR : quartetClockFixed →ₗ[ℝ] (Fin 2 → ℝ) := rhoL ∘ₗ quartetClockFixed.subtype

theorem rhoR_injective : Function.Injective rhoR := by
  refine (injective_iff_map_eq_zero rhoR).mpr fun x hx => ?_
  obtain ⟨hFO, hcl⟩ := Submodule.mem_inf.mp x.2
  have hcl' : ∀ k t, x.1 k t =
      clockInv * x.1 k (t + if k = 0 then 0 else 1) * clockInv.conjTranspose := hcl
  have r0 : (x.1 1 0 0 1).im = 0 := congrFun hx 0
  have r1 : (x.1 1 0 1 2).im = 0 := congrFun hx 1
  have s3 : star (ω ^ 2) = ω := by rw [star_pow, star_omega, ← pow_mul, w4]
  have a := congrFun (congrFun (hcl' 0 0) 0) 1
  have b := congrFun (congrFun (hcl' 0 0) 0) 2
  have c := congrFun (congrFun (hcl' 0 1) 1) 2
  rw [clock_entry] at a b c
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, s3, star_omega] at a b c
  have z1 := fix_zero _ _ _ a (by rw [one_mul]; exact omega_ne_one)
  have z2 := fix_zero _ _ _ b (by rw [one_mul]; exact omega_sq_ne_one)
  have z3 := fix_zero _ _ _ c (by rw [← pow_add, w4]; exact omega_ne_one)
  have hφ : phiL x.1 = 0 := by
    funext i
    fin_cases i
    · show (x.1 0 0 0 1).re = 0; rw [z1]; rfl
    · show (x.1 0 0 0 1).im = 0; rw [z1]; rfl
    · show (x.1 0 0 0 2).re = 0; rw [z2]; rfl
    · show (x.1 0 0 0 2).im = 0; rw [z2]; rfl
    · show (x.1 0 1 1 2).re = 0; rw [z3]; rfl
    · show (x.1 0 1 1 2).im = 0; rw [z3]; rfl
    · exact r0
    · exact r1
  have h0 := phiR_injective (a₁ := ⟨x.1, hFO⟩) (a₂ := 0) (by rw [map_zero]; exact hφ)
  have h1 : x.1 = 0 := congrArg Subtype.val h0
  exact Subtype.ext h1

theorem rhoR_surjective : Function.Surjective rhoR := by
  intro v
  refine ⟨⟨orbitL (Xmat (cvec (v 0) (v 1))), clock_mem (v 0) (v 1)⟩, ?_⟩
  have e6 := congrFun (phi_orbit (cvec (v 0) (v 1))) 6
  have e7 := congrFun (phi_orbit (cvec (v 0) (v 1))) 7
  funext i
  fin_cases i
  · exact e6
  · exact e7

end QuartetAux

/-- Two diagonal conjugation directions survive the clock symmetry. -/
theorem finrank_quartetClockFixed : Module.finrank ℝ quartetClockFixed = 2 := by
  exact (LinearEquiv.ofBijective QuartetAux.rhoR
    ⟨QuartetAux.rhoR_injective, QuartetAux.rhoR_surjective⟩).finrank_eq.trans
      (Module.finrank_fin_fun ℝ)

end CKM.NativeFirstOrder

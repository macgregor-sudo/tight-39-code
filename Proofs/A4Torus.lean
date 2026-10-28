module

public import A4DerFixed
public import A3PhaseTriples

@[expose] public section

/-!
# The adjoint torus `τ(ξ)`, the twelve signed root rows and the centralizer `z_s(τ)`

* `betaWeight`: `β₁ = ε₄ − ε₂, β₂ = ε₁ + ε₂, β₃ = ε₁ − ε₃, β₄ = ε₃ − ε₄`, a `ℤ`-basis of the
  even-coordinate-sum lattice `Q(D₄)` (`rootLattice`).
* `adjointTorus ξ ∈ Hom(Q(D₄), S¹)`: `β₁ ↦ −A³, β₂ ↦ −B³, β₃ ↦ C³, β₄ ↦ −D³` (`ξ = (A,B,C,D)`),
  extended multiplicatively through the `β`-coordinates `betaCoord`.
* The orthogonal lift `planeRot (liftEig ξ λ)` with plane eigenvalues
  `(λ, −B³/λ, λ/C³, −λ/(C³D³))`, `λ² = −(ABCD)³`; its conjugation action does not depend on `λ`.
  `adTau ξ` is the resulting Lie automorphism of the actual `s` (through `psi`). On the root plane of `α`
  it rotates by `adjointTorus ξ α` and it fixes `t`.
* MASTER §6.6 table (lines 749–760): twelve roots `rowRoot H j` in four labelled hexagons, each the
  cube of its signed normalized phase `anchorPhases ξ H j` (A3's table, verbatim), with root characters
  `kChar H`; the hexagons are disjoint and exhaust the 24 roots.
* `zs ξ = z_s(τ(ξ))`, the fixed space of `adTau ξ` on `s`, is `K`-invariant and
  `≃_K ℝ⁴_triv ⊕ ⨁_H V_H^(r_H)` with `r_H` A3's cube-one count — at every unit phase, resonances included.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The root lattice and the adjoint torus -/

/-- `β₁ = ε₄ − ε₂, β₂ = ε₁ + ε₂, β₃ = ε₁ − ε₃, β₄ = ε₃ − ε₄`. -/
def betaWeight : Fin 4 → Fin 4 → ℤ := ![![0, -1, 0, 1], ![1, 1, 0, 0], ![1, 0, -1, 0], ![0, 0, 1, -1]]

/-- The even-coordinate-sum lattice `Q(D₄)`. -/
def rootLattice : AddSubgroup (Fin 4 → ℤ) where
  carrier := {v | Even (∑ i, v i)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    exact ha.add hb
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib] at *
    exact ha.neg

/-- `β`-coordinates of a lattice vector (`h = (Σ v)/2`). -/
def betaCoord (v : Fin 4 → ℤ) : Fin 4 → ℤ :=
  let h := (∑ i, v i) / 2
  ![h - v 1, h, h - v 1 - v 2 - v 3, h - v 1 - v 3]

theorem mem_rootLattice {v : Fin 4 → ℤ} : v ∈ rootLattice ↔ Even (∑ i, v i) := Iff.rfl

theorem mem_rootLattice_iff {v : Fin 4 → ℤ} : v ∈ rootLattice ↔ ∃ k, v 0 + v 1 + v 2 + v 3 = k + k := by
  rw [mem_rootLattice, Fin.sum_univ_four]; rfl

theorem betaCoord_eq {v : Fin 4 → ℤ} {k : ℤ} (hk : v 0 + v 1 + v 2 + v 3 = k + k) :
    betaCoord v = ![k - v 1, k, k - v 1 - v 2 - v 3, k - v 1 - v 3] := by
  have h : (∑ i, v i) / 2 = k := by rw [Fin.sum_univ_four, hk]; omega
  simp only [betaCoord, h]

theorem betaWeight_mem (i : Fin 4) : betaWeight i ∈ rootLattice := by
  rw [mem_rootLattice_iff]
  fin_cases i
  · exact ⟨0, by simp [betaWeight]⟩
  · exact ⟨1, by simp [betaWeight]⟩
  · exact ⟨0, by simp [betaWeight]⟩
  · exact ⟨0, by simp [betaWeight]⟩

/-- The `β`'s form a `ℤ`-basis of `Q(D₄)`. -/
theorem betaWeight_basis (v : Fin 4 → ℤ) (hv : v ∈ rootLattice) :
    ∑ i, betaCoord v i • betaWeight i = v ∧
      ∀ n : Fin 4 → ℤ, ∑ i, n i • betaWeight i = v → n = betaCoord v := by
  obtain ⟨k, hk⟩ := mem_rootLattice_iff.mp hv
  rw [betaCoord_eq hk]
  refine ⟨?_, fun n hn => ?_⟩
  · funext q
    fin_cases q <;> simp [Fin.sum_univ_four, betaWeight]
    all_goals omega
  · have h0 := congrFun hn 0
    have h1 := congrFun hn 1
    have h2 := congrFun hn 2
    have h3 := congrFun hn 3
    simp [Fin.sum_univ_four, betaWeight] at h0 h1 h2 h3
    funext i
    fin_cases i <;> simp <;> omega

/-- Values of `τ(ξ)` on the `β`-basis: `(−A³, −B³, C³, −D³)`. -/
def betaValue (ξ : Fin 4 → ℂ) : Fin 4 → ℂ := ![-(ξ 0 ^ 3), -(ξ 1 ^ 3), ξ 2 ^ 3, -(ξ 3 ^ 3)]

/-- The adjoint-torus element `τ(ξ) : Q(D₄) → S¹`. -/
def adjointTorus (ξ : Fin 4 → ℂ) (v : Fin 4 → ℤ) : ℂ := ∏ i, betaValue ξ i ^ betaCoord v i

theorem unit_ne_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (a : Fin 4) : ξ a ≠ 0 := by
  intro h
  have := hξ a
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem betaValue_ne_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (i : Fin 4) : betaValue ξ i ≠ 0 := by
  fin_cases i <;> simp [betaValue, unit_ne_zero hξ]

theorem normSq_betaValue {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (i : Fin 4) :
    Complex.normSq (betaValue ξ i) = 1 := by
  fin_cases i <;> simp [betaValue, map_pow, Complex.normSq_neg, hξ _]

theorem adjointTorus_betaWeight (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    adjointTorus ξ (betaWeight i) = betaValue ξ i := by
  fin_cases i <;> simp [adjointTorus, betaCoord, betaWeight, Fin.prod_univ_four, Fin.sum_univ_four]

theorem adjointTorus_add (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {v w : Fin 4 → ℤ}
    (hv : v ∈ rootLattice) (hw : w ∈ rootLattice) :
    adjointTorus ξ (v + w) = adjointTorus ξ v * adjointTorus ξ w := by
  obtain ⟨k, hk⟩ := mem_rootLattice_iff.mp hv
  obtain ⟨l, hl⟩ := mem_rootLattice_iff.mp hw
  have hvw : (v + w) 0 + (v + w) 1 + (v + w) 2 + (v + w) 3 = (k + l) + (k + l) := by
    simp only [Pi.add_apply]; omega
  have hc : ∀ i, betaCoord (v + w) i = betaCoord v i + betaCoord w i := by
    intro i
    rw [betaCoord_eq hk, betaCoord_eq hl, betaCoord_eq hvw]
    fin_cases i <;> simp <;> ring
  unfold adjointTorus
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hc, zpow_add₀ (betaValue_ne_zero hξ i)]

theorem normSq_adjointTorus (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (v : Fin 4 → ℤ) :
    Complex.normSq (adjointTorus ξ v) = 1 := by
  simp [adjointTorus, map_prod, map_zpow₀, normSq_betaValue hξ]

theorem posRoot_weight_mem (α : PosRoot) : α.weight ∈ rootLattice := by
  rw [mem_rootLattice]
  rcases α with ⟨⟨r, s, p⟩, h⟩
  cases p <;> simp [PosRoot.weight, Finset.sum_add_distrib]

/-! ## The orthogonal lift and the adjoint action on `s` -/

/-- The square `−(ABCD)³` of the lift parameter. -/
def liftSq (ξ : Fin 4 → ℂ) : ℂ := -((ξ 0 * ξ 1 * ξ 2 * ξ 3) ^ 3)

/-- Plane eigenvalues `(λ, −B³/λ, λ/C³, −λ/(C³D³))` of an orthogonal lift. -/
def liftEig (ξ : Fin 4 → ℂ) (lam : ℂ) : Fin 4 → ℂ :=
  ![lam, -(ξ 1 ^ 3) / lam, lam / ξ 2 ^ 3, -lam / (ξ 2 ^ 3 * ξ 3 ^ 3)]

/-- One square root of `liftSq ξ` (the principal one; any choice works, see `adRot_liftEig_eq`). -/
def liftChoice (ξ : Fin 4 → ℂ) : ℂ := liftSq ξ ^ ((2 : ℂ)⁻¹)

theorem liftChoice_sq (ξ : Fin 4 → ℂ) : liftChoice ξ ^ 2 = liftSq ξ :=
  Complex.cpow_ofNat_inv_pow (liftSq ξ) 2

theorem normSq_liftSq {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : Complex.normSq (liftSq ξ) = 1 := by
  simp [liftSq, map_mul, map_pow, Complex.normSq_neg, hξ _]

theorem normSq_lam {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) {lam : ℂ} (hlam : lam ^ 2 = liftSq ξ) :
    Complex.normSq lam = 1 := by
  have h : Complex.normSq lam ^ 2 = 1 := by rw [← map_pow, hlam, normSq_liftSq hξ]
  exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg lam) two_ne_zero).mp h

theorem star_eq_inv_of_normSq {z : ℂ} (hz : Complex.normSq z = 1) : star z = z⁻¹ := by
  rw [Complex.inv_def, hz]; simp

theorem liftEig_unit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {lam : ℂ} (hlam : lam ^ 2 = liftSq ξ) (r : Fin 4) :
    Complex.normSq (liftEig ξ lam r) = 1 := by
  have hl := normSq_lam hξ hlam
  fin_cases r <;> simp [liftEig, map_div₀, map_mul, map_pow, Complex.normSq_neg, hξ _, hl]

/-- **Lift independence**: the conjugation action of the lift does not depend on the square root. -/
theorem adRot_liftEig_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {lam lam' : ℂ}
    (hlam : lam ^ 2 = liftSq ξ) (hlam' : lam' ^ 2 = liftSq ξ) :
    adRot (liftEig ξ lam) = adRot (liftEig ξ lam') := by
  have hsq : lam' ^ 2 = lam ^ 2 := hlam'.trans hlam.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · rw [h]
  · have hneg : liftEig ξ lam' = -liftEig ξ lam := by
      subst h
      funext r
      fin_cases r <;> simp [liftEig] <;> ring
    rw [hneg, adRot_neg]

/-- The lift realizes the adjoint torus: its root values are `τ(ξ)` on the roots. -/
theorem rootValue_liftEig (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {lam : ℂ} (hlam : lam ^ 2 = liftSq ξ)
    (α : PosRoot) : rootValue (liftEig ξ lam) α = adjointTorus ξ α.weight := by
  have hl := normSq_lam hξ hlam
  have hst : ∀ r, star (liftEig ξ lam r) = (liftEig ξ lam r)⁻¹ := fun r =>
    star_eq_inv_of_normSq (liftEig_unit ξ hξ hlam r)
  have hne : lam ≠ 0 := by rintro rfl; simp at hl
  have h0 := unit_ne_zero hξ 0
  have h1 := unit_ne_zero hξ 1
  have h2 := unit_ne_zero hξ 2
  have h3 := unit_ne_zero hξ 3
  simp only [liftSq] at hlam
  rcases α with ⟨⟨r, s, p⟩, h⟩
  simp only [rootValue, hst, PosRoot.r, PosRoot.s, PosRoot.plus]
  fin_cases r <;> fin_cases s <;> cases p <;> simp at h <;>
    simp [liftEig, adjointTorus, betaCoord, PosRoot.weight, PosRoot.r, PosRoot.s, PosRoot.plus,
      Fin.sum_univ_four, Fin.prod_univ_four, betaValue] <;> field_simp
  all_goals first | linear_combination hlam | linear_combination -hlam

/-- The adjoint action `Ad(τ(ξ))` on the actual `s`, a Lie automorphism. -/
def adTau (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : diagonalFixer ≃ₗ⁅ℝ⁆ diagonalFixer :=
  psi.trans ((adRotEquiv (liftEig ξ (liftChoice ξ)) (liftEig_unit ξ hξ (liftChoice_sq ξ))).trans psi.symm)

theorem psi_adTau (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : diagonalFixer) :
    ((psi (adTau ξ hξ D) : skewEnd) : Module.End ℝ Octonion) =
      adRot (liftEig ξ (liftChoice ξ)) (psi D) := by
  simp only [adTau, LieEquiv.trans_apply, LieEquiv.apply_symm_apply, adRotEquiv_apply]

theorem liftEig_choice_unit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (r : Fin 4) :
    Complex.normSq (liftEig ξ (liftChoice ξ) r) = 1 :=
  liftEig_unit ξ hξ (liftChoice_sq ξ) r

theorem psi_ext {D E : diagonalFixer}
    (h : ((psi D : skewEnd) : Module.End ℝ Octonion) = ((psi E : skewEnd) : Module.End ℝ Octonion)) :
    D = E :=
  psi.injective (Subtype.ext h)

theorem adTau_cartan (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {D : diagonalFixer} (hD : D ∈ cartanInS) :
    adTau ξ hξ D = D := by
  apply psi_ext
  rw [psi_adTau]
  have hmem := (psi_mem_commonCartan_iff D).mp (mem_cartanInS.mp hD)
  have hle : Submodule.span ℝ (Set.range cartanGen) ≤ fixedSpace (adRot (liftEig ξ (liftChoice ξ))) :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q =>
      mem_fixedSpace.mpr (adRot_cartanGen (liftEig_choice_unit hξ) q))
  exact mem_fixedSpace.mp (hle hmem)

theorem adTau_sRootX (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (α : PosRoot) :
    adTau ξ hξ (sRootX α) =
      (adjointTorus ξ α.weight).re • sRootX α + (adjointTorus ξ α.weight).im • sRootY α := by
  apply psi_ext
  rw [psi_adTau]
  simp only [sRootX, sRootY, map_add, map_smul, LieEquiv.apply_symm_apply]
  rw [adRot_rootX (liftEig_choice_unit hξ), rootValue_liftEig ξ hξ (liftChoice_sq ξ)]
  rfl

theorem adTau_sRootY (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (α : PosRoot) :
    adTau ξ hξ (sRootY α) =
      -((adjointTorus ξ α.weight).im • sRootX α) + (adjointTorus ξ α.weight).re • sRootY α := by
  apply psi_ext
  rw [psi_adTau]
  simp only [sRootX, sRootY, map_add, map_neg, map_smul, LieEquiv.apply_symm_apply]
  rw [adRot_rootY (liftEig_choice_unit hξ), rootValue_liftEig ξ hξ (liftChoice_sq ξ)]
  rfl

theorem adTau_comm_g0 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : diagonalFixer) :
    adTau ξ hξ (sAction.g0 D) = sAction.g0 (adTau ξ hξ D) := by
  apply psi_ext
  rw [psi_adTau, psi_sAction_g0, psi_sAction_g0, psi_adTau]
  exact LinearMap.congr_fun (adRot_comm _ _) _

theorem adTau_comm_g1 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : diagonalFixer) :
    adTau ξ hξ (sAction.g1 D) = sAction.g1 (adTau ξ hξ D) := by
  apply psi_ext
  rw [psi_adTau, psi_sAction_g1, psi_sAction_g1, psi_adTau]
  exact LinearMap.congr_fun (adRot_comm _ _) _

/-! ## The twelve signed rows (MASTER §6.6 table) -/

/-- Table roots: `rowRoot H j = (α, neg)` is the root `−α` if `neg`, else `α`. -/
def rowRoot : Fin 4 → Fin 3 → PosRoot × Bool :=
  ![![(⟨(2, 3, true), by decide⟩, false), (⟨(1, 2, false), by decide⟩, false),
      (⟨(1, 3, true), by decide⟩, true)],
    ![(⟨(0, 1, false), by decide⟩, false), (⟨(1, 2, true), by decide⟩, false),
      (⟨(0, 2, true), by decide⟩, true)],
    ![(⟨(0, 3, false), by decide⟩, false), (⟨(0, 2, false), by decide⟩, true),
      (⟨(2, 3, false), by decide⟩, true)],
    ![(⟨(1, 3, false), by decide⟩, false), (⟨(0, 1, true), by decide⟩, true),
      (⟨(0, 3, true), by decide⟩, false)]]

/-- The signed weight of a table root. -/
def rowWeight (H : Fin 4) (j : Fin 3) : Fin 4 → ℤ :=
  if (rowRoot H j).2 then -(rowRoot H j).1.weight else (rowRoot H j).1.weight

/-- MASTER's `β`-coordinates of the table roots, row by row. -/
def rowBeta : Fin 4 → Fin 3 → Fin 4 → ℤ :=
  ![![![1, 1, -1, 0], ![-1, 0, 0, -1], ![0, -1, 1, 1]],
    ![![1, 0, 1, 1], ![0, 1, -1, 0], ![-1, -1, 0, -1]],
    ![![0, 0, 1, 1], ![0, 0, -1, 0], ![0, 0, 0, -1]],
    ![![-1, 0, 0, 0], ![0, -1, 0, 0], ![1, 1, 0, 0]]]

theorem rowWeight_beta (H : Fin 4) (j : Fin 3) : ∑ i, rowBeta H j i • betaWeight i = rowWeight H j := by
  revert H j; decide

theorem betaCoord_rowWeight (H : Fin 4) (j : Fin 3) : betaCoord (rowWeight H j) = rowBeta H j := by
  revert H j; decide

/-- Each labelled triple sums to zero, has squared length two and pairwise inner products `−1`. -/
theorem rowWeight_triple (H : Fin 4) :
    (∑ j, rowWeight H j = 0) ∧ (∀ j, ∑ q, rowWeight H j q * rowWeight H j q = 2) ∧
      ∀ j j', j ≠ j' → ∑ q, rowWeight H j q * rowWeight H j' q = -1 := by
  revert H; decide

/-- The `K`-character `Σ_q w_q · peirceChar q` of a weight. -/
def weightChar (w : Fin 4 → ℤ) : ZMod 3 × ZMod 3 := ∑ q, w q • peirceChar q

theorem rowWeight_char (H : Fin 4) (j : Fin 3) : weightChar (rowWeight H j) = kChar H := by
  revert H j; decide

/-- **Root value of each table row: the cube of its signed normalized phase.** -/
theorem adjointTorus_rowWeight (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (j : Fin 3) :
    adjointTorus ξ (rowWeight H j) = anchorPhases ξ H j ^ 3 := by
  rw [adjointTorus, betaCoord_rowWeight]
  fin_cases H <;> fin_cases j <;> simp [rowBeta, Fin.prod_univ_four, betaValue, anchorPhases] <;> ring

/-- The labelled hexagon of `H` (its three positive roots; adjoining negatives gives six). -/
def hexagon (H : Fin 4) : Set PosRoot := {α | ∃ j, (rowRoot H j).1 = α}

theorem mem_hexagon_iff_char (H : Fin 4) (α : PosRoot) :
    α ∈ hexagon H ↔ weightChar α.weight = kChar H ∨ weightChar α.weight = -kChar H := by
  show (∃ j, (rowRoot H j).1 = α) ↔ _
  revert H α; decide

theorem hexagon_disjoint {H H' : Fin 4} (hne : H ≠ H') (α : PosRoot) : ¬ (α ∈ hexagon H ∧ α ∈ hexagon H') := by
  show ¬ ((∃ j, (rowRoot H j).1 = α) ∧ (∃ j, (rowRoot H' j).1 = α))
  revert H H' α; decide

theorem hexagon_cover (α : PosRoot) : ∃ H, α ∈ hexagon H := by
  show ∃ H, ∃ j, (rowRoot H j).1 = α
  revert α; decide

theorem star_omega : star ω = ω ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]
  apply Complex.ext <;> simp [UnitaryErrorBases.ThreeCycleFourier.omega] <;> ring

theorem omega_cube' : ω ^ 3 = 1 := UnitaryErrorBases.ThreeCycleFourier.omega_cube

theorem rootValue_omegaPow (e : Fin 4 → ℕ) (α : PosRoot) :
    rootValue (omegaPow e) α = ω ^ (e α.r + if α.plus then e α.s else 2 * e α.s) := by
  unfold rootValue omegaPow
  cases α.plus <;> simp [pow_add, star_pow, star_omega, ← pow_mul]

theorem weightChar_exps (α : PosRoot) :
    (r0Exp α.r + (if α.plus then r0Exp α.s else 2 * r0Exp α.s)) % 3 = (weightChar α.weight).1.val ∧
      (r1Exp 2 α.r + (if α.plus then r1Exp 2 α.s else 2 * r1Exp 2 α.s)) % 3 =
        (weightChar α.weight).2.val := by
  revert α; decide

/-- The `K`-generators act on root planes by the root characters. -/
theorem rootValue_K (α : PosRoot) :
    rootValue (omegaPow r0Exp) α = ω ^ (weightChar α.weight).1.val ∧
      rootValue (omegaPow (r1Exp 2)) α = ω ^ (weightChar α.weight).2.val := by
  constructor
  · rw [rootValue_omegaPow, pow_eq_pow_mod _ omega_cube', (weightChar_exps α).1]
  · rw [rootValue_omegaPow, pow_eq_pow_mod _ omega_cube', (weightChar_exps α).2]

/-! ## The centralizer `z_s(τ)` -/

/-! ### Helpers: `psi` as a linear map into endomorphisms -/

/-- `psi` followed by the inclusion of `skewEnd`. -/
def Lpsi : diagonalFixer →ₗ[ℝ] Module.End ℝ Octonion where
  toFun D := ((psi D : skewEnd) : Module.End ℝ Octonion)
  map_add' D E := by simp only [map_add]; rfl
  map_smul' c D := by simp only [map_smul]; rfl

theorem Lpsi_apply (D : diagonalFixer) : Lpsi D = ((psi D : skewEnd) : Module.End ℝ Octonion) := rfl

theorem Lpsi_injective : Function.Injective Lpsi := fun _ _ h => psi_ext h

theorem Lpsi_symm (x : Module.End ℝ Octonion) (hx : x ∈ skewEnd) : Lpsi (psi.symm ⟨x, hx⟩) = x := by
  rw [Lpsi_apply, LieEquiv.apply_symm_apply]

theorem Lpsi_sRootX (α : PosRoot) : Lpsi (sRootX α) = rootX α := Lpsi_symm _ _

theorem Lpsi_sRootY (α : PosRoot) : Lpsi (sRootY α) = rootY α := Lpsi_symm _ _

theorem Lpsi_mem_skewEnd (D : diagonalFixer) : Lpsi D ∈ skewEnd := (psi D).2

theorem adRot_adRot (z w : Fin 4 → ℂ) (B : Module.End ℝ Octonion) :
    adRot z (adRot w B) = adRot (z * w) B := by
  rw [adRot_apply, adRot_apply, adRot_apply, star_mul, ← planeRot_mul, ← planeRot_mul]
  simp only [mul_assoc]

theorem omegaPow_add (e f : Fin 4 → ℕ) : omegaPow (e + f) = omegaPow e * omegaPow f := by
  funext r; simp [omegaPow, pow_add]

/-- Plane exponents of the generator `gen H` on `o12`. -/
def genE (H : Fin 4) (r : Fin 4) : ℕ := (![1, 0, 2, 2] H) * r0Exp r + (![0, 1, 2, 1] H) * r1Exp 2 r

theorem Lpsi_gen (H : Fin 4) (D : diagonalFixer) :
    Lpsi (sAction.gen H D) = adRot (omegaPow (genE H)) (Lpsi D) := by
  fin_cases H
  · show Lpsi (sAction.g0 D) = adRot (omegaPow (genE 0)) (Lpsi D)
    have h : genE 0 = r0Exp := by funext r; simp [genE]
    rw [h]; exact psi_sAction_g0 D
  · show Lpsi (sAction.g1 D) = adRot (omegaPow (genE 1)) (Lpsi D)
    have h : genE 1 = r1Exp 2 := by funext r; simp [genE]
    rw [h]; exact psi_sAction_g1 D
  · show Lpsi ((sAction.g0 ^ 2 * sAction.g1 ^ 2) D) = adRot (omegaPow (genE 2)) (Lpsi D)
    have h : genE 2 = r0Exp + r0Exp + (r1Exp 2 + r1Exp 2) := by funext r; simp [genE]; ring
    rw [h, omegaPow_add, omegaPow_add, omegaPow_add, ← adRot_adRot, ← adRot_adRot, ← adRot_adRot]
    simp only [pow_two, Module.End.mul_apply, Lpsi_apply, psi_sAction_g0, psi_sAction_g1]
  · show Lpsi ((sAction.g0 ^ 2 * sAction.g1) D) = adRot (omegaPow (genE 3)) (Lpsi D)
    have h : genE 3 = r0Exp + r0Exp + r1Exp 2 := by funext r; simp [genE]; ring
    rw [h, omegaPow_add, omegaPow_add, ← adRot_adRot, ← adRot_adRot]
    simp only [pow_two, Module.End.mul_apply, Lpsi_apply, psi_sAction_g0, psi_sAction_g1]

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp [UnitaryErrorBases.ThreeCycleFourier.omega] at this

theorem omega_pow_eq_one_iff (n : ℕ) : ω ^ n = 1 ↔ n % 3 = 0 := by
  rw [pow_eq_pow_mod n omega_cube']
  obtain h | h | h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  · simp [h]
  · simp [h, omega_ne_one]
  · rw [h, ← star_omega]
    simp only [OfNat.ofNat_ne_zero, iff_false]
    intro h'
    apply omega_ne_one
    simpa using congrArg star h'

theorem genE_hexagon (H : Fin 4) (α : PosRoot) :
    (genE H α.r + (if α.plus then genE H α.s else 2 * genE H α.s)) % 3 = 0 ↔ ∃ j, (rowRoot H j).1 = α := by
  revert H α; decide

theorem rootValue_gen_eq_one_iff (H : Fin 4) (α : PosRoot) :
    rootValue (omegaPow (genE H)) α = 1 ↔ α ∈ hexagon H := by
  rw [rootValue_omegaPow, omega_pow_eq_one_iff, genE_hexagon]; rfl

theorem adjointTorus_zero (ξ : Fin 4 → ℂ) : adjointTorus ξ 0 = 1 := by
  simp [adjointTorus, betaCoord, Fin.prod_univ_four]

theorem adjointTorus_neg_eq_one_iff {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) {v : Fin 4 → ℤ}
    (hv : v ∈ rootLattice) : adjointTorus ξ (-v) = 1 ↔ adjointTorus ξ v = 1 := by
  have h := adjointTorus_add ξ hξ (neg_mem hv) hv
  rw [neg_add_cancel, adjointTorus_zero] at h
  constructor
  · intro h1; rw [h1, one_mul] at h; exact h.symm
  · intro h1; rw [h1, mul_one] at h; exact h.symm

theorem rowRoot_torus_iff {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (j : Fin 3) :
    adjointTorus ξ (rowRoot H j).1.weight = 1 ↔ anchorPhases ξ H j ^ 3 = 1 := by
  rw [← adjointTorus_rowWeight ξ hξ H j, rowWeight]
  split_ifs
  · exact (adjointTorus_neg_eq_one_iff hξ (posRoot_weight_mem _)).symm
  · exact Iff.rfl

theorem rowRoot_inj (H : Fin 4) (j j' : Fin 3) (h : (rowRoot H j).1 = (rowRoot H j').1) : j = j' := by
  revert H j j'; decide

theorem resonanceCount_eq_card (d : UnitaryErrorBases.PhaseTriple) :
    UnitaryErrorBases.resonanceCount d = Nat.card (UnitaryErrorBases.ResonantIndex d) := by
  rw [Nat.card_eq_fintype_card]
  unfold UnitaryErrorBases.resonanceCount
  convert rfl

/-- The resonant hexagon roots of `H` are counted by A3's resonance count. -/
theorem card_hexagon_resonant {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Nat.card {α : PosRoot // α ∈ hexagon H ∧ adjointTorus ξ α.weight = 1} =
      UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  rw [resonanceCount_eq_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun j => ⟨(rowRoot H j.1).1, ⟨j.1, rfl⟩, (rowRoot_torus_iff hξ H j.1).mpr j.2⟩) ⟨?_, ?_⟩)
  · intro j j' h
    exact Subtype.ext (rowRoot_inj H j.1 j'.1 (congrArg Subtype.val h))
  · rintro ⟨α, ⟨j, rfl⟩, h⟩
    exact ⟨⟨j, (rowRoot_torus_iff hξ H j).mp h⟩, rfl⟩

open Classical in
theorem card_split (P : PosRoot → Prop) :
    Nat.card {α // P α} = ∑ H, Nat.card {α // α ∈ hexagon H ∧ P α} := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  obtain ⟨H, hH⟩ := hexagon_cover α
  rw [Finset.sum_eq_single H]
  · by_cases hP : P α <;> simp [hP, hH]
  · intro H' _ hne
    have := hexagon_disjoint hne.symm α
    split_ifs with h
    · exact absurd ⟨hH, h.1⟩ this
    · rfl
  · simp

theorem map_Lpsi_eq {ι : Type*} (U : Submodule ℝ diagonalFixer) (Z : ι → Fin 4 → ℂ)
    (hU : ∀ D, D ∈ U ↔ ∀ i, adRot (Z i) (Lpsi D) = Lpsi D) :
    U.map Lpsi = (⨅ i, fixedSpace (adRot (Z i))) ⊓ skewEnd.toSubmodule := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf, mem_fixedSpace]
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact ⟨(hU D).mp hD, Lpsi_mem_skewEnd D⟩
  · rintro ⟨hfix, hx⟩
    refine ⟨psi.symm ⟨x, hx⟩, (hU _).mpr ?_, Lpsi_symm x hx⟩
    rw [Lpsi_symm x hx]
    exact hfix

theorem finrank_of_Lpsi {ι : Type*} [Finite ι] (U : Submodule ℝ diagonalFixer) (Z : ι → Fin 4 → ℂ)
    (hZ : ∀ i r, Complex.normSq (Z i r) = 1)
    (hU : ∀ D, D ∈ U ↔ ∀ i, adRot (Z i) (Lpsi D) = Lpsi D) :
    Module.finrank ℝ U = 4 + 2 * Nat.card {α : PosRoot // ∀ i, rootValue (Z i) α = 1} := by
  rw [← finrank_fixed_adRot Z hZ, ← map_Lpsi_eq U Z hU]
  exact (Submodule.equivMapOfInjective Lpsi Lpsi_injective U).finrank_eq

theorem map_Lpsi_cartanInS : cartanInS.map Lpsi = Submodule.span ℝ (Set.range cartanGen) := by
  ext x
  constructor
  · rintro ⟨D, hD, rfl⟩
    exact (psi_mem_commonCartan_iff D).mp hD
  · intro hx
    have hle : Submodule.span ℝ (Set.range cartanGen) ≤ skewEnd.toSubmodule :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun q => cartanGen_mem q)
    have hs : x ∈ skewEnd := hle hx
    refine ⟨psi.symm ⟨x, hs⟩, ?_, Lpsi_symm x hs⟩
    show ((psi.symm ⟨x, hs⟩ : diagonalFixer) : Module.End ℝ Albert) ∈ commonCartan
    rw [psi_mem_commonCartan_iff, LieEquiv.apply_symm_apply]
    exact hx

/-! ### The centralizer -/

/-- `z_s(τ(ξ))`: the fixed subspace of the adjoint action on `s`. -/
def zs (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Submodule ℝ diagonalFixer :=
  fixedSpace (adTau ξ hξ).toLinearEquiv.toLinearMap

theorem mem_zs {ξ : Fin 4 → ℂ} {hξ : IsUnitPhase ξ} {D : diagonalFixer} : D ∈ zs ξ hξ ↔ adTau ξ hξ D = D := by
  rw [zs, mem_fixedSpace]; rfl

theorem Lpsi_adTau (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : diagonalFixer) :
    Lpsi (adTau ξ hξ D) = adRot (liftEig ξ (liftChoice ξ)) (Lpsi D) :=
  psi_adTau ξ hξ D

theorem mem_zs_iff_Lpsi {ξ : Fin 4 → ℂ} {hξ : IsUnitPhase ξ} {D : diagonalFixer} :
    D ∈ zs ξ hξ ↔ adRot (liftEig ξ (liftChoice ξ)) (Lpsi D) = Lpsi D := by
  rw [mem_zs, ← Lpsi_adTau ξ hξ D]
  exact ⟨fun h => by rw [h], fun h => Lpsi_injective h⟩

theorem cartanInS_le_zs (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : cartanInS ≤ zs ξ hξ := by
  intro D hD
  exact mem_zs.mpr (adTau_cartan ξ hξ hD)

theorem rootXY_indep (α : PosRoot) {a b : ℝ} (h : a • rootX α + b • rootY α = 0) : a = 0 ∧ b = 0 := by
  have hli : LinearIndependent ℝ ![rootX α, rootY α] := by
    have hf : Function.Injective (![Sum.inr (α, false), Sum.inr (α, true)] : Fin 2 → RootIndex) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first | rfl | simp at hij
    have := rootFamily_linearIndependent.comp _ hf
    convert this using 1
    funext i
    fin_cases i <;> rfl
  exact LinearIndependent.pair_iff.mp hli a b h

/-- **Actual centralizer binding**: a root plane centralizes `τ` exactly when its root value is one. -/
theorem rootPlane_le_zs_iff (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (α : PosRoot) :
    (sRootX α ∈ zs ξ hξ ∧ sRootY α ∈ zs ξ hξ) ↔ adjointTorus ξ α.weight = 1 := by
  constructor
  · rintro ⟨hx, -⟩
    rw [mem_zs, adTau_sRootX] at hx
    have E := congrArg Lpsi hx
    simp only [map_add, map_smul, Lpsi_sRootX, Lpsi_sRootY] at E
    have h0 : ((adjointTorus ξ α.weight).re - 1) • rootX α + (adjointTorus ξ α.weight).im • rootY α = 0 := by
      calc _ = ((adjointTorus ξ α.weight).re • rootX α + (adjointTorus ξ α.weight).im • rootY α) - rootX α := by
            module
        _ = 0 := sub_eq_zero.mpr E
    obtain ⟨hre, him⟩ := rootXY_indep α h0
    apply Complex.ext
    · simp only [Complex.one_re]; linarith
    · simpa using him
  · intro h1
    refine ⟨?_, ?_⟩
    · rw [mem_zs, adTau_sRootX, h1]; simp
    · rw [mem_zs, adTau_sRootY, h1]; simp

theorem zs_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    zs ξ hξ = cartanInS ⊔ Submodule.span ℝ
      {D | ∃ α : PosRoot, adjointTorus ξ α.weight = 1 ∧ (D = sRootX α ∨ D = sRootY α)} := by
  apply Submodule.map_injective_of_injective Lpsi_injective
  have hU : ∀ D, D ∈ zs ξ hξ ↔ ∀ _ : Unit, adRot (liftEig ξ (liftChoice ξ)) (Lpsi D) = Lpsi D :=
    fun D => by rw [mem_zs_iff_Lpsi, forall_const]
  rw [map_Lpsi_eq (zs ξ hξ) (fun _ : Unit => liftEig ξ (liftChoice ξ)) hU,
    fixed_adRot_eq _ (fun _ => liftEig_choice_unit hξ), Submodule.map_sup, Submodule.map_span,
    map_Lpsi_cartanInS, Submodule.span_union]
  congr 2
  ext B
  simp only [forall_const, rootValue_liftEig ξ hξ (liftChoice_sq ξ), Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨α, h1, hB | hB⟩
    · exact ⟨sRootX α, ⟨α, h1, Or.inl rfl⟩, by rw [Lpsi_sRootX, hB]⟩
    · exact ⟨sRootY α, ⟨α, h1, Or.inr rfl⟩, by rw [Lpsi_sRootY, hB]⟩
  · rintro ⟨D, ⟨α, h1, hD | hD⟩, rfl⟩
    · exact ⟨α, h1, Or.inl (by rw [hD, Lpsi_sRootX])⟩
    · exact ⟨α, h1, Or.inr (by rw [hD, Lpsi_sRootY])⟩

theorem zs_invariant (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : sAction.IsInvariant (zs ξ hξ) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [mem_zs, adTau_comm_g0, mem_zs.mp hv]
  · rw [mem_zs, adTau_comm_g1, mem_zs.mp hv]

/-- `K` acting on `z_s(τ(ξ))`. -/
def zAction (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : KAction (zs ξ hξ) :=
  sAction.restrict (zs ξ hξ) (zs_invariant ξ hξ)

theorem finrank_zAction_fixK (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (zAction ξ hξ).fixK = 4 := by
  rw [zAction, finrank_fixK_restrict]
  have h : sAction.fixK ⊓ zs ξ hξ = sAction.fixK :=
    inf_eq_left.mpr (cartanInS_eq_fixK ▸ cartanInS_le_zs ξ hξ)
  rw [h, finrank_sAction_fixK]

theorem finrank_zAction_fixH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ((zAction ξ hξ).fixH H) =
      4 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  rw [zAction, finrank_fixH_restrict]
  have hZ : ∀ i r, Complex.normSq ((![omegaPow (genE H), liftEig ξ (liftChoice ξ)] : Fin 2 → Fin 4 → ℂ) i r) = 1 := by
    intro i r
    fin_cases i
    · exact omegaPow_unit _ r
    · exact liftEig_choice_unit hξ r
  have hU : ∀ D, D ∈ sAction.fixH H ⊓ zs ξ hξ ↔
      ∀ i, adRot ((![omegaPow (genE H), liftEig ξ (liftChoice ξ)] : Fin 2 → Fin 4 → ℂ) i) (Lpsi D) = Lpsi D := by
    intro D
    rw [Submodule.mem_inf, mem_zs_iff_Lpsi, Fin.forall_fin_two, KAction.fixH, mem_fixedSpace]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← Lpsi_gen]
    exact and_congr_left' Lpsi_injective.eq_iff.symm
  rw [finrank_of_Lpsi _ _ hZ hU, ← card_hexagon_resonant hξ H]
  congr 2
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun α => ?_
  rw [Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [rootValue_gen_eq_one_iff, rootValue_liftEig ξ hξ (liftChoice_sq ξ)]

theorem finrank_zs (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (zs ξ hξ) = 4 + 2 * ∑ H, UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  have hU : ∀ D, D ∈ zs ξ hξ ↔ ∀ _ : Unit, adRot (liftEig ξ (liftChoice ξ)) (Lpsi D) = Lpsi D :=
    fun D => by rw [mem_zs_iff_Lpsi, forall_const]
  rw [finrank_of_Lpsi (zs ξ hξ) (fun _ : Unit => liftEig ξ (liftChoice ξ)) (fun _ => liftEig_choice_unit hξ) hU]
  congr 2
  simp only [forall_const, rootValue_liftEig ξ hξ (liftChoice_sq ξ)]
  rw [card_split]
  exact Finset.sum_congr rfl fun H _ => card_hexagon_resonant hξ H

/-- **`z_s(τ(ξ)) ≃_K ℝ⁴_triv ⊕ ⨁_H V_H^(r_H)`**, at every unit phase. -/
theorem zs_kEquiv (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (KEquiv (zAction ξ hξ)
      (stdAction 4 fun H => UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H))) :=
  kEquiv_std_of_finrank (zAction ξ hξ) 4 _ (finrank_zAction_fixK ξ hξ) (finrank_zAction_fixH ξ hξ)

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.betaWeight_mem
#print axioms CKM.NativeIntrinsicTriality.betaWeight_basis
#print axioms CKM.NativeIntrinsicTriality.adjointTorus_betaWeight
#print axioms CKM.NativeIntrinsicTriality.adjointTorus_add
#print axioms CKM.NativeIntrinsicTriality.normSq_adjointTorus
#print axioms CKM.NativeIntrinsicTriality.posRoot_weight_mem
#print axioms CKM.NativeIntrinsicTriality.liftChoice_sq
#print axioms CKM.NativeIntrinsicTriality.liftEig_unit
#print axioms CKM.NativeIntrinsicTriality.adRot_liftEig_eq
#print axioms CKM.NativeIntrinsicTriality.rootValue_liftEig
#print axioms CKM.NativeIntrinsicTriality.adTau
#print axioms CKM.NativeIntrinsicTriality.psi_adTau
#print axioms CKM.NativeIntrinsicTriality.adTau_cartan
#print axioms CKM.NativeIntrinsicTriality.adTau_sRootX
#print axioms CKM.NativeIntrinsicTriality.adTau_sRootY
#print axioms CKM.NativeIntrinsicTriality.adTau_comm_g0
#print axioms CKM.NativeIntrinsicTriality.adTau_comm_g1
#print axioms CKM.NativeIntrinsicTriality.rowWeight_beta
#print axioms CKM.NativeIntrinsicTriality.rowWeight_triple
#print axioms CKM.NativeIntrinsicTriality.rowWeight_char
#print axioms CKM.NativeIntrinsicTriality.adjointTorus_rowWeight
#print axioms CKM.NativeIntrinsicTriality.mem_hexagon_iff_char
#print axioms CKM.NativeIntrinsicTriality.hexagon_disjoint
#print axioms CKM.NativeIntrinsicTriality.hexagon_cover
#print axioms CKM.NativeIntrinsicTriality.rootValue_K
#print axioms CKM.NativeIntrinsicTriality.rootLattice
#print axioms CKM.NativeIntrinsicTriality.zs
#print axioms CKM.NativeIntrinsicTriality.cartanInS_le_zs
#print axioms CKM.NativeIntrinsicTriality.rootPlane_le_zs_iff
#print axioms CKM.NativeIntrinsicTriality.zs_eq
#print axioms CKM.NativeIntrinsicTriality.zs_invariant
#print axioms CKM.NativeIntrinsicTriality.zAction
#print axioms CKM.NativeIntrinsicTriality.finrank_zAction_fixK
#print axioms CKM.NativeIntrinsicTriality.finrank_zAction_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_zs
#print axioms CKM.NativeIntrinsicTriality.zs_kEquiv

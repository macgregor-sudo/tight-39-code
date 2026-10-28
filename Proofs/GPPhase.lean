module

public import GPTorus
public import GPResonance

@[expose] public section

/-!
# Open dense good phases avoiding a polynomial, and punctured accumulation

`PhaseTorus` is the native unit-phase torus `{ξ : Fin 4 → ℂ // IsUnitPhase ξ}` (an abbreviation only).
For an ordinary complex polynomial `p` in the four phase variables, `GoodAvoid p` is the set of phases
satisfying A5's twelve nonresonance tests (`IsGoodPhase`) with `eval ξ p ≠ 0`. By the resonance
binding it is the nonvanishing locus of `resonancePoly * p`, so for `p ≠ 0` it is open and dense, and
every phase is the limit of a sequence of such phases different from it.

The four unit phases are the parameters of the deformation of the 39-point code in Cohn–Kumar–Minton,
arXiv:1308.3188v4, p.49 (the code itself at `ξ = 1`); that text asserts the family and states nothing about
genericity of the parameters. The correspondence of its `ξ₁, …, ξ₄` with `ξ 0, …, ξ 3` is not fixed here.
-/

noncomputable section

open MvPolynomial Filter Topology CKM.NativeFirstOrder CKM.NativeFourFamily

namespace CKM.NativeGoodPhase

/-- The native four-phase torus. -/
abbrev PhaseTorus := {ξ : Fin 4 → ℂ // IsUnitPhase ξ}

/-- Good phases avoiding the zero set of `p`. -/
def GoodAvoid (p : MvPolynomial (Fin 4) ℂ) : Set PhaseTorus :=
  {u : PhaseTorus | IsGoodPhase u.1 ∧ eval u.1 p ≠ 0}

theorem goodAvoid_eq (p : MvPolynomial (Fin 4) ℂ) :
    GoodAvoid p = {u : PhaseTorus | eval u.1 (resonancePoly * p) ≠ 0} := by
  -- Unit phases make `IsGoodPhase` the nonvanishing of `resonancePoly`; then `eval` is multiplicative.
  ext u
  simp only [GoodAvoid, Set.mem_ofPred_eq, isGoodPhase_iff_eval_resonancePoly u.2, eval_mul,
    mul_ne_zero_iff]

/-- **Open dense good phases.** -/
theorem isOpen_dense_goodAvoid {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0) :
    IsOpen (GoodAvoid p) ∧ Dense (GoodAvoid p) := by
  -- `PhaseTorus` is definitionally `UnitTorus 4`; apply torus density to `resonancePoly * p`.
  rw [goodAvoid_eq]
  exact ⟨isOpen_evalNeZeroSet (resonancePoly * p),
    dense_evalNeZeroSet (mul_ne_zero resonancePoly_ne_zero hp)⟩

/-- **Punctured phase accumulation.** -/
theorem exists_seq_goodAvoid_tendsto {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0) (u₀ : PhaseTorus) :
    ∃ u : ℕ → PhaseTorus, (∀ n, u n ∈ GoodAvoid p) ∧ (∀ n, u n ≠ u₀) ∧
      Tendsto u atTop (𝓝 u₀) := by
  -- The torus sequence lemma for `resonancePoly * p`, read back through `goodAvoid_eq`.
  obtain ⟨u, hu, hne, ht⟩ :=
    exists_seq_evalNeZero_tendsto (by norm_num : 0 < 4) (mul_ne_zero resonancePoly_ne_zero hp) u₀
  refine ⟨u, fun n => ?_, hne, ht⟩
  rw [goodAvoid_eq]
  exact hu n

end CKM.NativeGoodPhase


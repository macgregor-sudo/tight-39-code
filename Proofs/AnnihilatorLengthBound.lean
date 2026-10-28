module

/-
# Annihilator length bound

For a commutative Noetherian ring `R`, a finite `R`-module `M` and an ideal `m`, there are
`c r : ℕ` with, for every `N`, in `ℕ∞`,
`length R/(ann M + m^(N+1)) ≤ r * length M/m^(N+c+1) M`.

Argument: choose generators `s : Fin r → M`; the map `φ : R → M^r`, `a ↦ (a • s i)_i`, has
kernel `ann M`, so `R/ann M ≅ range φ ⊆ M^r`.  The pilot's Artin–Rees length comparison
(`ShiftedJetLength.exists_length_quotient_smul_le`) bounds the length of
`range φ / m^(N+1) range φ` by that of `M^r / m^(N+c+1) M^r = (M/m^(N+c+1) M)^r`.
-/
public import ArtinReesJetLength

@[expose] public section

namespace AnnihilatorLengthBound

open Submodule

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (R) in
/-- Step 2: the map `R → (Fin r → M)`, `a ↦ fun i => a • s i`. -/
noncomputable def evalMap {r : ℕ} (s : Fin r → M) : R →ₗ[R] (Fin r → M) :=
  LinearMap.pi fun i => LinearMap.toSpanSingleton R M (s i)

theorem evalMap_apply {r : ℕ} (s : Fin r → M) (a : R) (i : Fin r) :
    evalMap R s a i = a • s i := rfl

/-- Step 2: for a generating tuple, `φ a = 0 ↔ a ∈ ann M`. -/
theorem evalMap_eq_zero_iff {r : ℕ} {s : Fin r → M}
    (hs : Submodule.span R (Set.range s) = ⊤) (a : R) :
    evalMap R s a = 0 ↔ a ∈ Module.annihilator R M := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x
    have hle : Submodule.span R (Set.range s) ≤ LinearMap.ker (LinearMap.lsmul R M a) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [evalMap_apply] using congrFun h i
    have hx : x ∈ LinearMap.ker (LinearMap.lsmul R M a) := hle (hs ▸ Submodule.mem_top)
    simpa using hx
  · intro h
    funext i
    simp [evalMap_apply, h]

/-- Step 2 (submodule form): `ker φ = ann M` as submodules of `R`. -/
theorem ker_evalMap {r : ℕ} {s : Fin r → M} (hs : Submodule.span R (Set.range s) = ⊤) :
    LinearMap.ker (evalMap R s) = (Module.annihilator R M : Submodule R R) := by
  ext a
  rw [LinearMap.mem_ker]
  exact evalMap_eq_zero_iff hs a

/-- Step 3: `R ⧸ ann M ≃ₗ[R] range φ`. -/
noncomputable def quotAnnihilatorEquivRange {r : ℕ} {s : Fin r → M}
    (hs : Submodule.span R (Set.range s) = ⊤) :
    (R ⧸ (Module.annihilator R M : Submodule R R)) ≃ₗ[R] LinearMap.range (evalMap R s) :=
  (Submodule.quotEquivOfEq _ _ (ker_evalMap hs).symm).trans (evalMap R s).quotKerEquivRange

/-- A linear equivalence `e : A ≃ₗ B` identifies `A ⧸ a • ⊤` with `B ⧸ a • ⊤`. -/
theorem length_quotient_smul_top_congr {A B : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (a : Ideal R) :
    Module.length R (A ⧸ (a • (⊤ : Submodule R A))) =
      Module.length R (B ⧸ (a • (⊤ : Submodule R B))) := by
  have hmap : (a • (⊤ : Submodule R A)).map (e : A →ₗ[R] B) = a • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  exact (Submodule.Quotient.equiv _ _ e hmap).length_eq

/-- Step 5: the left side is the length of `range φ ⧸ m^k • range φ`. -/
theorem length_quotient_annihilator_sup_eq {r : ℕ} {s : Fin r → M}
    (hs : Submodule.span R (Set.range s) = ⊤) (a : Ideal R) :
    Module.length R (R ⧸ (Module.annihilator R M ⊔ a)) =
      Module.length R (LinearMap.range (evalMap R s) ⧸
        (a • (⊤ : Submodule R (LinearMap.range (evalMap R s))))) := by
  rw [← length_quotient_smul_top_congr (quotAnnihilatorEquivRange hs) a,
    ShiftedJetLength.length_quotient_quotient_smul_top, Ideal.smul_eq_mul, Ideal.mul_top]

/-- Step 6 (submodule identity): `a • ⊤` in `Fin r → M` is the product of the `a • ⊤`. -/
theorem smul_top_pi_eq {r : ℕ} (a : Ideal R) :
    (a • (⊤ : Submodule R (Fin r → M))) =
      Submodule.pi Set.univ (fun _ : Fin r => a • (⊤ : Submodule R M)) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro b hb x _
    rw [Submodule.mem_pi]
    intro i _
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · intro x hx
    rw [Submodule.mem_pi] at hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : Pi.single i (x i) ∈ (a • (⊤ : Submodule R M)).map (LinearMap.single R (fun _ => M) i) :=
      Submodule.mem_map_of_mem (hx i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact (smul_mono_right a (le_top : _ ≤ (⊤ : Submodule R (Fin r → M)))) h1

/-- Step 6 (equivalence): `(Fin r → M) ⧸ pi univ p ≃ₗ (Fin r → M ⧸ p)`.  Written directly
(first isomorphism theorem for the surjection `x ↦ (mk (x i))_i`) because the module
`Mathlib.LinearAlgebra.Quotient.Pi` (`Submodule.quotientPi`) is not built at this pin. -/
noncomputable def quotientPiConstEquiv (r : ℕ) (p : Submodule R M) :
    ((Fin r → M) ⧸ Submodule.pi Set.univ (fun _ : Fin r => p)) ≃ₗ[R] (Fin r → M ⧸ p) := by
  let f : (Fin r → M) →ₗ[R] (Fin r → M ⧸ p) :=
    LinearMap.pi fun i => p.mkQ ∘ₗ LinearMap.proj i
  have hf : Function.Surjective f := by
    intro y
    refine ⟨fun i => (Submodule.Quotient.mk_surjective p (y i)).choose, ?_⟩
    funext i
    exact (Submodule.Quotient.mk_surjective p (y i)).choose_spec
  have hker : LinearMap.ker f = Submodule.pi Set.univ (fun _ : Fin r => p) := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      have := congrFun h i
      simpa [f, Submodule.Quotient.mk_eq_zero] using this
    · intro h
      funext i
      simpa [f, Submodule.Quotient.mk_eq_zero] using h i
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)

/-- Step 6: `length (M^r ⧸ a • ⊤) = r * length (M ⧸ a • ⊤)`. -/
theorem length_quotient_pi_smul_top (r : ℕ) (a : Ideal R) :
    Module.length R ((Fin r → M) ⧸ (a • (⊤ : Submodule R (Fin r → M)))) =
      (r : ℕ∞) * Module.length R (M ⧸ (a • (⊤ : Submodule R M))) := by
  rw [ShiftedJetLength.length_quotient_congr (smul_top_pi_eq a),
    (quotientPiConstEquiv r (a • (⊤ : Submodule R M))).length_eq,
    Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **Annihilator length bound**. -/
theorem exists_length_quotient_annihilator_sup_pow_le
    [IsNoetherianRing R] [Module.Finite R M] (m : Ideal R) :
    ∃ c r : ℕ, ∀ N : ℕ,
      Module.length R (R ⧸ (Module.annihilator R M ⊔ m ^ (N + 1))) ≤
        (r : ℕ∞) * Module.length R (M ⧸ (m ^ (N + c + 1) • (⊤ : Submodule R M))) := by
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨c, hc⟩ :=
    ShiftedJetLength.exists_length_quotient_smul_le (E := Fin r → M) m (LinearMap.range (evalMap R s))
  refine ⟨c, r, fun N => ?_⟩
  rw [length_quotient_annihilator_sup_eq hs, ← length_quotient_pi_smul_top]
  exact hc N

end General

/-- The `M = 0` (subsingleton) case is an instance of the statement: here
`Module.annihilator R M = ⊤`, the left side is `0`, and the same proof applies. -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M]
    [IsNoetherianRing R] [Module.Finite R M] (m : Ideal R) :
    ∃ c r : ℕ, ∀ N : ℕ,
      Module.length R (R ⧸ (Module.annihilator R M ⊔ m ^ (N + 1))) ≤
        (r : ℕ∞) * Module.length R (M ⧸ (m ^ (N + c + 1) • (⊤ : Submodule R M))) :=
  exists_length_quotient_annihilator_sup_pow_le m

/-- With `M = 0` the left side really is `0` (annihilator is `⊤`). -/
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M]
    (m : Ideal R) (N : ℕ) :
    Module.length R (R ⧸ (Module.annihilator R M ⊔ m ^ (N + 1))) = 0 := by
  have h : Module.annihilator R M = ⊤ := by
    rw [Ideal.eq_top_iff_one, Module.mem_annihilator]
    intro x; exact Subsingleton.elim _ _
  rw [h, top_sup_eq, Module.length_eq_zero_iff]
  infer_instance

end AnnihilatorLengthBound

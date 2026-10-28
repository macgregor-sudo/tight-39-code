module

/-
# Lower jet-length bound for finitely many branches

Original source: `claude-finite-branch-jet-lower-2026-10-23`, 2026-10-23.
AI-assisted authorship: Claude (Opus). First-party; copies no upstream
proof body.  Pin: Lean v4.35.0-rc2, mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Mathematics

`R` Noetherian, `m` an ideal, `P : ι → Ideal R` finitely many pairwise incomparable primes,
`J = ⨅ i, P i`.  For `i ≠ j` choose `a i j ∈ P j \ P i`; put `w i = ∏_{j ≠ i} a i j`, so
`w i ∉ P i` (primality) and `w i ∈ P j` for `j ≠ i`.  Then `Φ : Π i, R/P i → R/J`,
`(r_i) ↦ ∑ w_i r_i` is well defined and injective (reduce modulo `P i`, cancel `w i`).
Artin–Rees on `range Φ ⊆ R/J` (`ShiftedJetLength.exists_length_quotient_smul_le`)
gives `c` with `length (Π R/P i)/m^(N+1) ≤ length (R/J)/m^(N+c+1)` for all `N`; the left side
is `∑ length R/(P i + m^(N+1))` (`Submodule.quotientPi`, `Module.length_pi_of_fintype`) and
the right side is `length R/(J + m^(N+c+1))`.  Lengths are in `ℕ∞`; no finiteness is used.
The empty family needs no case split (`⨅ ∅ = ⊤`, empty sum `0`).
-/
public import ArtinReesJetLength
public import AnnihilatorLengthBound
public import Mathlib.LinearAlgebra.Quotient.Pi

@[expose] public section

namespace BranchJetLower

open Submodule

section Defs

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (P : ι → Ideal R) (hInc : ∀ i j, i ≠ j → ¬ P i ≤ P j)

/-- Step 1: chosen separator `sep i j ∈ P j`, `∉ P i` for `i ≠ j` (`1` on the diagonal). -/
noncomputable def sep (i j : ι) : R :=
  if h : i = j then 1 else (IsConcreteLE.not_le_iff_exists.mp (hInc j i (Ne.symm h))).choose

/-- Step 1: `w i = ∏_{j ≠ i} sep i j`. -/
noncomputable def w (i : ι) : R := ∏ j ∈ Finset.univ.erase i, sep P hInc i j

omit [Fintype ι] in
theorem sep_mem {i j : ι} (h : i ≠ j) : sep P hInc i j ∈ P j := by
  unfold sep
  split_ifs with h'
  · exact absurd h' h
  exact (IsConcreteLE.not_le_iff_exists.mp (hInc j i (Ne.symm h))).choose_spec.1

omit [Fintype ι] in
theorem sep_not_mem {i j : ι} (h : i ≠ j) : sep P hInc i j ∉ P i := by
  unfold sep
  split_ifs with h'
  · exact absurd h' h
  exact (IsConcreteLE.not_le_iff_exists.mp (hInc j i (Ne.symm h))).choose_spec.2

/-- `w i ∉ P i`. -/
theorem w_not_mem (hP : ∀ i, (P i).IsPrime) (i : ι) : w P hInc i ∉ P i := by
  intro hmem
  have := hP i
  obtain ⟨j, hj, hjm⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  exact sep_not_mem P hInc (Ne.symm (Finset.ne_of_mem_erase hj)) hjm

/-- `w i ∈ P j` for `j ≠ i`. -/
theorem w_mem {i j : ι} (h : j ≠ i) : w P hInc i ∈ P j := by
  rw [w, ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)]
  exact Ideal.mul_mem_right _ _ (sep_mem P hInc (Ne.symm h))

/-- `x ∈ P i → w i * x ∈ ⨅ j, P j`. -/
theorem mul_mem_iInf {i : ι} {x : R} (hx : x ∈ P i) : w P hInc i * x ∈ ⨅ j, P j := by
  rw [Submodule.mem_iInf]
  intro j
  by_cases h : j = i
  · subst h
    exact Ideal.mul_mem_left _ _ hx
  · exact Ideal.mul_mem_right _ _ (w_mem P hInc h)

theorem le_comap_lsmul (i : ι) :
    P i ≤ Submodule.comap (LinearMap.lsmul R R (w P hInc i)) (⨅ j, P j) :=
  fun _ hx => mul_mem_iInf P hInc hx

/-- Step 2: `φ i : R/P i → R/J`, `[r] ↦ [w i * r]`. -/
noncomputable def φ (i : ι) : (R ⧸ P i) →ₗ[R] (R ⧸ (⨅ j, P j)) :=
  Submodule.mapQ (P i) (⨅ j, P j) (LinearMap.lsmul R R (w P hInc i)) (le_comap_lsmul P hInc i)

theorem φ_mk (i : ι) (r : R) :
    φ P hInc i (Submodule.Quotient.mk r) = Submodule.Quotient.mk (w P hInc i * r) := rfl

/-- Step 3: `Φ : Π i, R/P i → R/J`, `x ↦ ∑ i, φ i (x i)`. -/
noncomputable def Φ : ((i : ι) → R ⧸ P i) →ₗ[R] (R ⧸ (⨅ j, P j)) :=
  ∑ i, φ P hInc i ∘ₗ LinearMap.proj i

theorem Φ_apply (x : (i : ι) → R ⧸ P i) : Φ P hInc x = ∑ i, φ P hInc i (x i) := by
  rw [Φ, LinearMap.sum_apply]
  rfl

/-- Step 4: `Φ` is injective. -/
theorem Φ_injective (hP : ∀ i, (P i).IsPrime) : Function.Injective (Φ P hInc) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  choose r hr using fun i => Submodule.Quotient.mk_surjective (P i) (x i)
  have hxr : x = fun i => Submodule.Quotient.mk (r i) := funext fun i => (hr i).symm
  subst hxr
  rw [Φ_apply] at hx
  simp only [φ_mk] at hx
  have h0 : (Submodule.Quotient.mk (∑ i, w P hInc i * r i) : R ⧸ (⨅ j, P j)) = 0 := by
    rw [← hx]
    exact map_sum (Submodule.mkQ (⨅ j, P j)) _ _
  have hJ := (Submodule.Quotient.mk_eq_zero _).mp h0
  funext i
  simp only [Pi.zero_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  have hPi := (Submodule.mem_iInf _).mp hJ i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hPi
  have hrest : ∑ j ∈ Finset.univ.erase i, w P hInc j * r j ∈ P i :=
    Ideal.sum_mem _ fun j hj =>
      Ideal.mul_mem_right _ _ (w_mem P hInc (Finset.ne_of_mem_erase hj).symm)
  have hwi : w P hInc i * r i ∈ P i := (Ideal.add_mem_iff_left _ hrest).mp hPi
  exact ((hP i).mem_or_mem hwi).resolve_left (w_not_mem P hInc hP i)

end Defs

section Lengths

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- Step 6: `a • ⊤` in `Π i, M i` is the product of the `a • ⊤` (dependent version of lane 1's
`AnnihilatorLengthBound.smul_top_pi_eq`, same proof). -/
theorem smul_top_pi_eq {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (a : Ideal R) :
    (a • (⊤ : Submodule R ((i : ι) → M i))) =
      Submodule.pi Set.univ (fun i => a • (⊤ : Submodule R (M i))) := by
  classical
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
    have h1 : Pi.single i (x i) ∈ (a • (⊤ : Submodule R (M i))).map (LinearMap.single R M i) :=
      Submodule.mem_map_of_mem (hx i (Set.mem_univ i))
    rw [Submodule.map_smul''] at h1
    exact (smul_mono_right a (le_top : _ ≤ (⊤ : Submodule R ((i : ι) → M i)))) h1

/-- Step 6: `length ((Π M i)/a(Π M i)) = ∑ length (M i / a M i)`. -/
theorem length_quotient_pi_smul_top {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (a : Ideal R) :
    Module.length R (((i : ι) → M i) ⧸ (a • (⊤ : Submodule R ((i : ι) → M i)))) =
      ∑ i, Module.length R (M i ⧸ (a • (⊤ : Submodule R (M i)))) := by
  classical
  rw [ShiftedJetLength.length_quotient_congr (smul_top_pi_eq a),
    (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]

/-- Steps 6/7: `length ((R/I)/a(R/I)) = length (R/(I + a))`. -/
theorem length_quotient_ideal_smul_top (I a : Ideal R) :
    Module.length R ((R ⧸ I) ⧸ (a • (⊤ : Submodule R (R ⧸ I)))) =
      Module.length R (R ⧸ (I ⊔ a)) := by
  rw [ShiftedJetLength.length_quotient_quotient_smul_top, Ideal.smul_eq_mul, Ideal.mul_top]

end Lengths

/-- **Lower jet-length bound for finitely many branches.**  For a Noetherian ring `R`, an
ideal `m` and a finite family of pairwise incomparable primes `P i`, there is a fixed `c`
such that for every `N`, in `ℕ∞`,
`∑ i, length R/(P i + m^(N+1)) ≤ length R/(⋂ P i + m^(N+c+1))`. -/
theorem exists_sum_length_quotient_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} [Fintype ι] (m : Ideal R) (P : ι → Ideal R)
    (hP : ∀ i, (P i).IsPrime) (hInc : ∀ i j, i ≠ j → ¬ P i ≤ P j) :
    ∃ c : ℕ, ∀ N : ℕ,
      ∑ i, Module.length R (R ⧸ (P i ⊔ m ^ (N + 1))) ≤
        Module.length R (R ⧸ ((⨅ i, P i) ⊔ m ^ (N + c + 1))) := by
  classical
  obtain ⟨c, hc⟩ := ShiftedJetLength.exists_length_quotient_smul_le (E := R ⧸ (⨅ i, P i)) m
    (LinearMap.range (Φ P hInc))
  refine ⟨c, fun N => ?_⟩
  have h := hc N
  rw [← AnnihilatorLengthBound.length_quotient_smul_top_congr
      (LinearEquiv.ofInjective _ (Φ_injective P hInc hP)),
    length_quotient_pi_smul_top, length_quotient_ideal_smul_top] at h
  simp only [length_quotient_ideal_smul_top] at h
  exact h

/-- **Finset adapter**: `J = F.inf P`, sum over `F`; hypotheses only on members of `F`.
Derived from `exists_sum_length_quotient_le` on the subtype `{i // i ∈ F}`. -/
theorem exists_sum_length_quotient_le_finset {R : Type*} [CommRing R] [IsNoetherianRing R]
    {ι : Type*} (m : Ideal R) (P : ι → Ideal R) (F : Finset ι)
    (hP : ∀ i ∈ F, (P i).IsPrime) (hInc : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ¬ P i ≤ P j) :
    ∃ c : ℕ, ∀ N : ℕ,
      ∑ i ∈ F, Module.length R (R ⧸ (P i ⊔ m ^ (N + 1))) ≤
        Module.length R (R ⧸ (F.inf P ⊔ m ^ (N + c + 1))) := by
  obtain ⟨c, hc⟩ := exists_sum_length_quotient_le m (fun i : F => P i) (fun i => hP i i.2)
    (fun i j hij => hInc i i.2 j j.2 (fun h => hij (Subtype.ext h)))
  refine ⟨c, fun N => ?_⟩
  have hinf : (⨅ i : F, P i) = F.inf P := by
    rw [Finset.inf_eq_iInf, iInf_subtype']
  rw [← Finset.sum_coe_sort F, ← hinf]
  exact hc N

/-- Empty family: covered by the main theorem with no case split. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] {ι : Type*} [Fintype ι] [IsEmpty ι]
    (m : Ideal R) (P : ι → Ideal R) :
    ∃ c : ℕ, ∀ N : ℕ,
      ∑ i, Module.length R (R ⧸ (P i ⊔ m ^ (N + 1))) ≤
        Module.length R (R ⧸ ((⨅ i, P i) ⊔ m ^ (N + c + 1))) :=
  exists_sum_length_quotient_le m P (fun i => isEmptyElim i) (fun i => isEmptyElim i)

/-- Empty family: both sides are `0` (`⨅ ∅ = ⊤`, `⊤ ⊔ _ = ⊤`, `R/⊤ = 0`). -/
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [IsEmpty ι]
    (m : Ideal R) (P : ι → Ideal R) (N c : ℕ) :
    ∑ i, Module.length R (R ⧸ (P i ⊔ m ^ (N + 1))) = 0 ∧
      Module.length R (R ⧸ ((⨅ i, P i) ⊔ m ^ (N + c + 1))) = 0 := by
  refine ⟨by simp, ?_⟩
  rw [iInf_of_empty, top_sup_eq, Module.length_eq_zero_iff]
  infer_instance

/-- Consumer: four branches. -/
example {R : Type*} [CommRing R] [IsNoetherianRing R] (m : Ideal R) (P : Fin 4 → Ideal R)
    (hP : ∀ i, (P i).IsPrime) (hInc : ∀ i j, i ≠ j → ¬ P i ≤ P j) :
    ∃ c : ℕ, ∀ N : ℕ,
      ∑ i, Module.length R (R ⧸ (P i ⊔ m ^ (N + 1))) ≤
        Module.length R (R ⧸ ((⨅ i, P i) ⊔ m ^ (N + c + 1))) :=
  exists_sum_length_quotient_le m P hP hInc

end BranchJetLower

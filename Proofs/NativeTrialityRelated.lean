module

public import NativeTrialityClifford

/-!
# Related infinitesimal triples and the two triality projections

A related infinitesimal triple is a triple `(A, B, C)` of skew real-linear maps of the native
octonions with
`C (x y) = (A x) y + x (B y)`   (MASTER (6.9)).
Triples form a Lie algebra under the componentwise commutator (the commutator Lie algebra of the
associative product `Module.End × Module.End × Module.End`). For imaginary `u`, the seed
`(L_u, R_u, L_u + R_u)` is a related triple.

Main statements: the first projection `(A, B, C) ↦ A` and the second projection `(A, B, C) ↦ B` are
Lie equivalences onto the skew endomorphisms `skewEnd` of the eight-dimensional octonion space; the
related triples have dimension `28`.

Proof route: the 7 seeds and 21 half-commutators of seeds lift the Clifford basis of `skewEnd`
(surjectivity); if `A = 0` then `B = C = T` with `T` commuting with every `L_x`, so `T = 0`
(injectivity); symmetrically for the second projection with right multiplications.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Triples of real-linear octonion maps `(A, B, C)`, with componentwise composition. -/
abbrev EndTriple := Module.End ℝ Octonion × Module.End ℝ Octonion × Module.End ℝ Octonion

/-- The defining relation (6.9) of a related infinitesimal triple, together with skewness. -/
def IsRelatedTriple (t : EndTriple) : Prop :=
  t.1 ∈ skewEnd ∧ t.2.1 ∈ skewEnd ∧ t.2.2 ∈ skewEnd ∧
    ∀ x y, t.2.2 (octMul x y) = octMul (t.1 x) y + octMul x (t.2.1 y)

/-- Helper: zero in the left factor of the native product. -/
theorem octMul_zero_left' (y : Octonion) : octMul 0 y = 0 := (rightMul y).map_zero

/-- Helper: zero in the right factor of the native product. -/
theorem octMul_zero_right' (x : Octonion) : octMul x 0 = 0 := (leftMul x).map_zero

/-- Helper: subtraction in the left factor of the native product. -/
theorem octMul_sub_left' (x y z : Octonion) : octMul (x - y) z = octMul x z - octMul y z :=
  (rightMul z).map_sub x y

/-- Helper: subtraction in the right factor of the native product. -/
theorem octMul_sub_right' (x y z : Octonion) : octMul x (y - z) = octMul x y - octMul x z :=
  (leftMul x).map_sub y z

/-- Helper: the related-triple relation is preserved by componentwise commutators, stated with
`s * t - t * s` (the mixed terms cancel). -/
theorem isRelatedTriple_mul_sub {s t : EndTriple} (hs : IsRelatedTriple s) (ht : IsRelatedTriple t) :
    IsRelatedTriple (s * t - t * s) := by
  obtain ⟨hs1, hs2, hs3, hs⟩ := hs
  obtain ⟨ht1, ht2, ht3, ht⟩ := ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := skewEnd.lie_mem hs1 ht1
    rwa [Ring.lie_def] at this
  · have := skewEnd.lie_mem hs2 ht2
    rwa [Ring.lie_def] at this
  · have := skewEnd.lie_mem hs3 ht3
    rwa [Ring.lie_def] at this
  · intro x y
    show s.2.2 (t.2.2 (octMul x y)) - t.2.2 (s.2.2 (octMul x y)) =
      octMul (s.1 (t.1 x) - t.1 (s.1 x)) y + octMul x (s.2.1 (t.2.1 y) - t.2.1 (s.2.1 y))
    rw [ht, hs, map_add, map_add, hs, hs, ht, ht, octMul_sub_left', octMul_sub_right']
    abel

theorem isRelatedTriple_zero : IsRelatedTriple 0 := by
  refine ⟨skewEnd.zero_mem, skewEnd.zero_mem, skewEnd.zero_mem, fun x y => ?_⟩
  show (0 : Octonion) = octMul 0 y + octMul x 0
  rw [octMul_zero_left', octMul_zero_right', add_zero]

theorem IsRelatedTriple.add {s t : EndTriple} (hs : IsRelatedTriple s) (ht : IsRelatedTriple t) :
    IsRelatedTriple (s + t) := by
  obtain ⟨hs1, hs2, hs3, hs⟩ := hs
  obtain ⟨ht1, ht2, ht3, ht⟩ := ht
  refine ⟨skewEnd.add_mem hs1 ht1, skewEnd.add_mem hs2 ht2, skewEnd.add_mem hs3 ht3, fun x y => ?_⟩
  show s.2.2 (octMul x y) + t.2.2 (octMul x y) =
    octMul (s.1 x + t.1 x) y + octMul x (s.2.1 y + t.2.1 y)
  rw [hs, ht, octMul_add_left, octMul_add_right]
  abel

theorem IsRelatedTriple.smul (r : ℝ) {t : EndTriple} (ht : IsRelatedTriple t) :
    IsRelatedTriple (r • t) := by
  obtain ⟨ht1, ht2, ht3, ht⟩ := ht
  refine ⟨skewEnd.smul_mem r ht1, skewEnd.smul_mem r ht2, skewEnd.smul_mem r ht3, fun x y => ?_⟩
  show r • t.2.2 (octMul x y) = octMul (r • t.1 x) y + octMul x (r • t.2.1 y)
  rw [ht, octMul_smul_left, octMul_smul_right, smul_add]

/-- Componentwise commutators of related triples are related (the two mixed terms cancel). -/
theorem IsRelatedTriple.lie {s t : EndTriple} (hs : IsRelatedTriple s) (ht : IsRelatedTriple t) :
    IsRelatedTriple ⁅s, t⁆ := by
  rw [Ring.lie_def]
  exact isRelatedTriple_mul_sub hs ht

/-- The Lie algebra of related infinitesimal triples. -/
def relatedTriples : LieSubalgebra ℝ EndTriple where
  carrier := {t | IsRelatedTriple t}
  zero_mem' := isRelatedTriple_zero
  add_mem' hs ht := hs.add ht
  smul_mem' r _ ht := ht.smul r
  lie_mem' hs ht := hs.lie ht

theorem mem_relatedTriples {t : EndTriple} : t ∈ relatedTriples ↔ IsRelatedTriple t := Iff.rfl

/-- The first projection `(A, B, C) ↦ A`, a Lie homomorphism into `skewEnd`. -/
def firstProj : relatedTriples →ₗ⁅ℝ⁆ skewEnd where
  toFun t := ⟨(t : EndTriple).1, t.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := fun {_ _} => rfl

/-- The second projection `(A, B, C) ↦ B`, a Lie homomorphism into `skewEnd`. -/
def secondProj : relatedTriples →ₗ⁅ℝ⁆ skewEnd where
  toFun t := ⟨(t : EndTriple).2.1, t.2.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := fun {_ _} => rfl

@[simp] theorem firstProj_apply (t : relatedTriples) :
    (firstProj t : Module.End ℝ Octonion) = (t : EndTriple).1 := rfl
@[simp] theorem secondProj_apply (t : relatedTriples) :
    (secondProj t : Module.End ℝ Octonion) = (t : EndTriple).2.1 := rfl

/-! ### Helpers for the two projections -/

/-- Helper: the seed `(L_u, R_u, L_u + R_u)` is related (the linearized middle Moufang identity). -/
theorem isRelatedTriple_seed {u : Octonion} (hu : octRe u = 0) :
    IsRelatedTriple (leftMul u, rightMul u, leftMul u + rightMul u) := by
  refine ⟨leftMul_mem_skewEnd hu, rightMul_mem_skewEnd hu,
    skewEnd.add_mem (leftMul_mem_skewEnd hu) (rightMul_mem_skewEnd hu), fun x y => ?_⟩
  show octMul u (octMul x y) + octMul (octMul x y) u = octMul (octMul u x) y + octMul x (octMul y u)
  exact (seed_identity u x y).symm

/-- Helper: half-commutators of related triples are related. -/
theorem isRelatedTriple_halfComm {s t : EndTriple} (hs : IsRelatedTriple s) (ht : IsRelatedTriple t) :
    IsRelatedTriple ((1 / 2 : ℝ) • (s * t - t * s)) :=
  (isRelatedTriple_mul_sub hs ht).smul _

/-- Helper: for anticommuting `P = -Q`, the half-commutator `(P - Q)/2` is `P`. -/
theorem half_sub_of_anticomm {P Q : Module.End ℝ Octonion} (h : P = -Q) :
    (1 / 2 : ℝ) • (P - Q) = P := by
  have hQ : Q = -P := by rw [h, neg_neg]
  rw [hQ, sub_neg_eq_add, ← two_smul ℝ P, smul_smul]
  norm_num

/-- Helper: the first component of a related triple, as a linear map. -/
def firstLin : relatedTriples →ₗ[ℝ] Module.End ℝ Octonion where
  toFun t := (t : EndTriple).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Helper: the second component of a related triple, as a linear map. -/
def secondLin : relatedTriples →ₗ[ℝ] Module.End ℝ Octonion where
  toFun t := (t : EndTriple).2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstProj_bijective : Function.Bijective firstProj := by
  have hΓ := cliffordSeven_leftMul
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨⟨A, B, C⟩, ht⟩ h0
    obtain ⟨_, hB, _, hrel⟩ := mem_relatedTriples.mp ht
    have hA : A = 0 := congrArg Subtype.val h0
    subst hA
    have hCB : C = B := by
      refine LinearMap.ext fun y => ?_
      have := hrel (octScalar 1) y
      simpa only [octMul_scalar_left, one_smul, LinearMap.zero_apply, octMul_zero_left',
        zero_add] using this
    subst hCB
    have hcomm : ∀ i, leftMul (imagUnit i) * C = C * leftMul (imagUnit i) := by
      intro i
      refine LinearMap.ext fun y => ?_
      show octMul (imagUnit i) (C y) = C (octMul (imagUnit i) y)
      rw [hrel]
      simp only [LinearMap.zero_apply, octMul_zero_left', zero_add]
    have hC0 : C = 0 := hΓ.eq_zero_of_commute hB hcomm
    subst hC0
    rfl
  · intro T
    have hmem : (T : Module.End ℝ Octonion) ∈ LinearMap.range firstLin := by
      refine (Submodule.span_le.mpr ?_) (hΓ.mem_span_cliffordWord T.2)
      rintro _ ⟨k, rfl⟩
      rcases k with i | ⟨⟨a, b⟩, hab⟩
      · exact ⟨⟨_, isRelatedTriple_seed (octRe_imagUnit i)⟩, rfl⟩
      · refine ⟨⟨_, isRelatedTriple_halfComm (isRelatedTriple_seed (octRe_imagUnit a))
          (isRelatedTriple_seed (octRe_imagUnit b))⟩, ?_⟩
        show (1 / 2 : ℝ) • (leftMul (imagUnit a) * leftMul (imagUnit b) -
          leftMul (imagUnit b) * leftMul (imagUnit a)) = leftMul (imagUnit a) * leftMul (imagUnit b)
        exact half_sub_of_anticomm (hΓ.anticomm a b (ne_of_lt hab))
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, Subtype.ext ht⟩

theorem secondProj_bijective : Function.Bijective secondProj := by
  have hΓ := cliffordSeven_rightMul
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨⟨A, B, C⟩, ht⟩ h0
    obtain ⟨hA, _, _, hrel⟩ := mem_relatedTriples.mp ht
    have hB : B = 0 := congrArg Subtype.val h0
    subst hB
    have hCA : C = A := by
      refine LinearMap.ext fun x => ?_
      have := hrel x (octScalar 1)
      simpa only [octMul_scalar_right, one_smul, LinearMap.zero_apply, octMul_zero_right',
        add_zero] using this
    subst hCA
    have hcomm : ∀ i, rightMul (imagUnit i) * C = C * rightMul (imagUnit i) := by
      intro i
      refine LinearMap.ext fun x => ?_
      show octMul (C x) (imagUnit i) = C (octMul x (imagUnit i))
      rw [hrel]
      simp only [LinearMap.zero_apply, octMul_zero_right', add_zero]
    have hC0 : C = 0 := hΓ.eq_zero_of_commute hA hcomm
    subst hC0
    rfl
  · intro T
    have hmem : (T : Module.End ℝ Octonion) ∈ LinearMap.range secondLin := by
      refine (Submodule.span_le.mpr ?_) (hΓ.mem_span_cliffordWord T.2)
      rintro _ ⟨k, rfl⟩
      rcases k with i | ⟨⟨a, b⟩, hab⟩
      · exact ⟨⟨_, isRelatedTriple_seed (octRe_imagUnit i)⟩, rfl⟩
      · refine ⟨⟨_, isRelatedTriple_halfComm (isRelatedTriple_seed (octRe_imagUnit a))
          (isRelatedTriple_seed (octRe_imagUnit b))⟩, ?_⟩
        show (1 / 2 : ℝ) • (rightMul (imagUnit a) * rightMul (imagUnit b) -
          rightMul (imagUnit b) * rightMul (imagUnit a)) =
            rightMul (imagUnit a) * rightMul (imagUnit b)
        exact half_sub_of_anticomm (hΓ.anticomm a b (ne_of_lt hab))
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, Subtype.ext ht⟩

/-- The first projection of related triples is a Lie equivalence with the skew endomorphisms. -/
def firstProjEquiv : relatedTriples ≃ₗ⁅ℝ⁆ skewEnd := LieEquiv.ofBijective firstProj firstProj_bijective

/-- The second projection of related triples is a Lie equivalence with the skew endomorphisms. -/
def secondProjEquiv : relatedTriples ≃ₗ⁅ℝ⁆ skewEnd := LieEquiv.ofBijective secondProj secondProj_bijective

@[simp] theorem firstProjEquiv_apply (t : relatedTriples) : firstProjEquiv t = firstProj t := rfl
@[simp] theorem secondProjEquiv_apply (t : relatedTriples) : secondProjEquiv t = secondProj t := rfl

theorem finrank_relatedTriples : Module.finrank ℝ relatedTriples = 28 :=
  (firstProjEquiv.toLinearEquiv.finrank_eq).trans finrank_skewEnd

/-- The seed triple `T_u = (L_u, R_u, L_u + R_u)`. -/
def seedTriple (u : Octonion) : EndTriple := (leftMul u, rightMul u, leftMul u + rightMul u)

theorem seedTriple_mem {u : Octonion} (hu : octRe u = 0) : seedTriple u ∈ relatedTriples := by
  exact isRelatedTriple_seed hu

#print axioms isRelatedTriple_zero
#print axioms IsRelatedTriple.add
#print axioms IsRelatedTriple.smul
#print axioms IsRelatedTriple.lie
#print axioms firstProj_bijective
#print axioms secondProj_bijective
#print axioms finrank_relatedTriples
#print axioms seedTriple_mem

end CKM.NativeDerivationTriality

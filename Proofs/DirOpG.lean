module

public import BookSheetConjugation
public import BookAxisSparseSupport
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

@[expose] public section

/-! Ring-generic transcription of the accepted Q12 sheet operator (`q12SheetTransport ∘ q12RootCoordinates
∘ q12SheetInverse`, BookSheetConjugation/BookConjugationQ12), with the half `h` and the unit `I` as parameters.
Proved: equality with the accepted Q12 operator (`q12Op_eq_opG`), homogeneity in `h`, and naturality under ring
homomorphisms. This lets the JSON comparison run over the Gaussian integers (fast kernel `Int` arithmetic)
instead of `Q12` rationals. First-party. -/

set_option Elab.async false
namespace Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.BookHT.TangentCoordinates

section Generic
variable {R : Type*} [CommRing R]

def hidG (I : R) (x : Fin 27 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![-x 21 + I * x 22, -x 23 + I * x 24, -x 25 - I * x 26;
      x 13 - I * x 14,  x 15 - I * x 16,  x 17 + I * x 18;
     -x 5 + I * x 6,   -x 7 + I * x 8,   -x 9 - I * x 10]

def parG (I : R) (x : Fin 27 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![-x 21 - I * x 22, -x 23 - I * x 24, -x 25 + I * x 26;
      x 13 + I * x 14,  x 15 + I * x 16,  x 17 - I * x 18;
     -x 5 - I * x 6,   -x 7 - I * x 8,   -x 9 + I * x 10]

def hcG (h I : R) (B Bt : Matrix (Fin 3) (Fin 3) R) : Fin 27 → R :=
  ![0, 0, 0, 0, 0,
    -h*(B 2 0 + Bt 2 0), -I*h*(B 2 0 - Bt 2 0),
    -h*(B 2 1 + Bt 2 1), -I*h*(B 2 1 - Bt 2 1),
    -h*(B 2 2 + Bt 2 2), I*h*(B 2 2 - Bt 2 2), 0, 0,
     h*(B 1 0 + Bt 1 0), I*h*(B 1 0 - Bt 1 0),
     h*(B 1 1 + Bt 1 1), I*h*(B 1 1 - Bt 1 1),
     h*(B 1 2 + Bt 1 2), -I*h*(B 1 2 - Bt 1 2), 0, 0,
    -h*(B 0 0 + Bt 0 0), -I*h*(B 0 0 - Bt 0 0),
    -h*(B 0 1 + Bt 0 1), -I*h*(B 0 1 - Bt 0 1),
    -h*(B 0 2 + Bt 0 2), I*h*(B 0 2 - Bt 0 2)]

def rootHidG (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => (if i = a then B b j else 0) - (if j = b then B i a else 0)

def rootCoordsG (h I : R) (a b : Fin 3) (x : Fin 27 → R) : Fin 27 → R :=
  hcG h I (rootHidG a b (hidG I x)) (-rootHidG b a (parG I x))

def transG (s : Fin 4) : (Fin 27 → R) → Fin 27 → R :=
  ![id, TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s,
    TitsS.sgnPerm TitsS.Transport.T2p TitsS.Transport.T2s,
    TitsS.sgnPerm TitsS.Transport.T3p TitsS.Transport.T3s] s

def invG (s : Fin 4) : (Fin 27 → R) → Fin 27 → R :=
  ![id, TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si,
    TitsS.sgnPerm TitsS.Transport.T2pinv TitsS.Transport.T2si,
    TitsS.sgnPerm TitsS.Transport.T3pinv TitsS.Transport.T3si] s

def opG (h I : R) (b : Fin 24) (x : Fin 27 → R) : Fin 27 → R :=
  transG (d6Sheet b)
    (rootCoordsG h I (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 (invG (d6Sheet b) x))

theorem hcG_smul (h I : R) (B Bt : Matrix (Fin 3) (Fin 3) R) (k : Fin 27) :
    hcG h I B Bt k = h * hcG 1 I B Bt k := by
  fin_cases k <;> simp [hcG] <;> ring

theorem transG_smul (s : Fin 4) (h : R) (v : Fin 27 → R) (k : Fin 27) :
    transG s (fun m => h * v m) k = h * transG s v k := by
  fin_cases s <;> simp [transG, TitsS.sgnPerm] <;> ring

theorem opG_smul (h I : R) (b : Fin 24) (x : Fin 27 → R) (k : Fin 27) :
    opG h I b x k = h * opG 1 I b x k := by
  unfold opG rootCoordsG
  rw [← transG_smul]
  congr 1
  funext m
  exact hcG_smul _ _ _ _ m

variable {S : Type*} [CommRing S] (φ : R →+* S)

theorem hidG_map (I : R) (x : Fin 27 → R) : hidG (φ I) (fun m => φ (x m)) = (hidG I x).map φ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hidG]

theorem parG_map (I : R) (x : Fin 27 → R) : parG (φ I) (fun m => φ (x m)) = (parG I x).map φ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [parG]

theorem rootHidG_map (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) R) :
    rootHidG a b (B.map φ) = (rootHidG a b B).map φ := by
  ext i j; simp only [rootHidG, Matrix.map_apply]; split_ifs <;> simp

theorem hcG_map (h I : R) (B Bt : Matrix (Fin 3) (Fin 3) R) (k : Fin 27) :
    hcG (φ h) (φ I) (B.map φ) (Bt.map φ) k = φ (hcG h I B Bt k) := by
  fin_cases k <;> simp [hcG]

theorem hcG_map' (h I : R) (B Bt : Matrix (Fin 3) (Fin 3) R) :
    hcG (φ h) (φ I) (B.map φ) (Bt.map φ) = fun k => φ (hcG h I B Bt k) :=
  funext (hcG_map φ h I B Bt)

theorem transG_map (s : Fin 4) (v : Fin 27 → R) (k : Fin 27) :
    transG s (fun m => φ (v m)) k = φ (transG s v k) := by
  fin_cases s <;> simp [transG, TitsS.sgnPerm]

theorem invG_map (s : Fin 4) (v : Fin 27 → R) :
    invG s (fun m => φ (v m)) = fun k => φ (invG s v k) := by
  funext k; fin_cases s <;> simp [invG, TitsS.sgnPerm]

theorem opG_map (I : R) (b : Fin 24) (x : Fin 27 → R) (k : Fin 27) :
    opG 1 (φ I) b (fun m => φ (x m)) k = φ (opG 1 I b x k) := by
  unfold opG rootCoordsG
  rw [invG_map, hidG_map, parG_map, rootHidG_map, rootHidG_map, ← Matrix.map_neg _ (map_neg φ),
    ← map_one φ]
  rw [hcG_map']
  exact transG_map φ _ _ k

end Generic

/-- The accepted Lean Q12 sheet operator of D6 column `b`. -/
def q12Op (b : Fin 24) (x : Fin 27 → Q12) : Fin 27 → Q12 :=
  q12SheetTransport (d6Sheet b)
    (q12RootCoordinates (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 (q12SheetInverse (d6Sheet b) x))

theorem q12Op_eq_opG (b : Fin 24) (x : Fin 27 → Q12) :
    q12Op b x = opG (Q12.ofRat (1/2)) Q12.I b x := by
  rfl

end Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.HTPhaseComplete
#print axioms opG_smul
#print axioms opG_map
#print axioms q12Op_eq_opG

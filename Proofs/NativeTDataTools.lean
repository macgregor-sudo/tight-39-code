module

public import NativeHWeights
public import Mathlib.Data.List.Sort

@[expose] public section

set_option Elab.async false
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices

def originalRows (es : List Entry) : List (Fin 2184) :=
  es.map (fun e => fNumber e.label)

/-- Adjacent original-row ordering suffices for uniqueness; no coefficient is evaluated. -/
theorem originalRows_nodup_of_chain (es : List Entry)
    (h : ((originalRows es).map Fin.val).IsChain (· < ·)) :
    (originalRows es).Nodup := by
  apply List.Nodup.of_map Fin.val
  exact (List.sortedLT_iff_isChain.mpr h).nodup

end Option2.NativeStress.NativeT

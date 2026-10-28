module

public import NativeTData11
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda12_rows_chain :
    ((originalRows lambda12).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda12_rows_nodup : (originalRows lambda12).Nodup :=
  originalRows_nodup_of_chain lambda12 lambda12_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda12_rows_nodup

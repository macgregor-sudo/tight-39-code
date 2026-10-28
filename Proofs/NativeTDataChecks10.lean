module

public import NativeTData10
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda6_rows_chain :
    ((originalRows lambda6).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda6_rows_nodup : (originalRows lambda6).Nodup :=
  originalRows_nodup_of_chain lambda6 lambda6_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda6_rows_nodup

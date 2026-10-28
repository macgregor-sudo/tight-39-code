module

public import NativeTData00
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda42_rows_chain :
    ((originalRows lambda42).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda42_rows_nodup : (originalRows lambda42).Nodup :=
  originalRows_nodup_of_chain lambda42 lambda42_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda42_rows_nodup

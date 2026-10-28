module

public import NativeTData01
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda43_rows_chain :
    ((originalRows lambda43).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda43_rows_nodup : (originalRows lambda43).Nodup :=
  originalRows_nodup_of_chain lambda43 lambda43_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda43_rows_nodup

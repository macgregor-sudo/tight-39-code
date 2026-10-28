module

public import NativeTData30
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda3_rows_chain :
    ((originalRows lambda3).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda3_rows_nodup : (originalRows lambda3).Nodup :=
  originalRows_nodup_of_chain lambda3 lambda3_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda3_rows_nodup

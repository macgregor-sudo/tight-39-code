module

public import NativeTData32
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda19_rows_chain :
    ((originalRows lambda19).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda19_rows_nodup : (originalRows lambda19).Nodup :=
  originalRows_nodup_of_chain lambda19 lambda19_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda19_rows_nodup

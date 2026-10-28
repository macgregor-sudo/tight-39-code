module

public import NativeTData22
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda17_rows_chain :
    ((originalRows lambda17).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda17_rows_nodup : (originalRows lambda17).Nodup :=
  originalRows_nodup_of_chain lambda17 lambda17_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda17_rows_nodup

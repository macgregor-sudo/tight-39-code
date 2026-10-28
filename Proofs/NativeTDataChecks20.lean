module

public import NativeTData20
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda7_rows_chain :
    ((originalRows lambda7).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda7_rows_nodup : (originalRows lambda7).Nodup :=
  originalRows_nodup_of_chain lambda7 lambda7_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda7_rows_nodup

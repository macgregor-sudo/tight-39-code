module

public import NativeTData12
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda16_rows_chain :
    ((originalRows lambda16).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda16_rows_nodup : (originalRows lambda16).Nodup :=
  originalRows_nodup_of_chain lambda16 lambda16_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda16_rows_nodup

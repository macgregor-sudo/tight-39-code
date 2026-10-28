module

public import NativeTData31
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda13_rows_chain :
    ((originalRows lambda13).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda13_rows_nodup : (originalRows lambda13).Nodup :=
  originalRows_nodup_of_chain lambda13 lambda13_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda13_rows_nodup

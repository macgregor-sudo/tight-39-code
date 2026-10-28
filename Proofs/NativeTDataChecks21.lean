module

public import NativeTData21
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda9_rows_chain :
    ((originalRows lambda9).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda9_rows_nodup : (originalRows lambda9).Nodup :=
  originalRows_nodup_of_chain lambda9 lambda9_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda9_rows_nodup

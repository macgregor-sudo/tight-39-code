module

public import NativeTData02
public import NativeTDataTools

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT

private theorem lambda45_rows_chain :
    ((originalRows lambda45).map Fin.val).IsChain (· < ·) := by
  decide +kernel

theorem lambda45_rows_nodup : (originalRows lambda45).Nodup :=
  originalRows_nodup_of_chain lambda45 lambda45_rows_chain

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.lambda45_rows_nodup

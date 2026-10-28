module

public import NativeHWeights

@[expose] public section

/-! Exact source λ3; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda3 : List Entry := [
  idEntry 0 0 ⟨-77, -36, 0, 0, 255, by decide⟩, -- source row 0
  idEntry 0 1 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 1
  idEntry 0 2 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 2
  idEntry 1 0 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-77, -36, 0, 0, 255, by decide⟩, -- source row 28
  idEntry 1 2 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 29
  idEntry 2 0 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 55
  idEntry 2 2 ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 56
  idEntry 2 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 63
  idEntry 2 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 64
  idEntry 3 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 81
  idEntry 3 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 82
  idEntry 3 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 83
  idEntry 3 3 ⟨0, 0, 0, -2, 3, by decide⟩, -- source row 84
  idEntry 3 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 86
  idEntry 3 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 87
  idEntry 3 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 90
  idEntry 3 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 91
  idEntry 4 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 108
  idEntry 4 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-3, 0, 0, 1, 6, by decide⟩, -- source row 111
  idEntry 4 4 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 112
  idEntry 4 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 113
  idEntry 4 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 114
  idEntry 4 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 117
  idEntry 4 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 118
  idEntry 5 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 140
  idEntry 5 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 141
  idEntry 5 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 144
  idEntry 5 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 145
  idEntry 6 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 162
  idEntry 6 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 163
  idEntry 6 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 164
  idEntry 6 3 ⟨0, 0, 0, -2, 3, by decide⟩, -- source row 165
  idEntry 6 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 167
  idEntry 6 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 168
  idEntry 6 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 171
  idEntry 6 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 172
  idEntry 7 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 189
  idEntry 7 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-3, 0, 0, 1, 6, by decide⟩, -- source row 192
  idEntry 7 4 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 193
  idEntry 7 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 194
  idEntry 7 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 195
  idEntry 7 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 198
  idEntry 7 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 199
  idEntry 8 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 221
  idEntry 8 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 222
  idEntry 8 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 225
  idEntry 8 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 226
  idEntry 9 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 243
  idEntry 9 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 245
  idEntry 9 3 ⟨0, 0, 0, -2, 3, by decide⟩, -- source row 246
  idEntry 9 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 248
  idEntry 9 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 249
  idEntry 9 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 252
  idEntry 9 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 253
  idEntry 10 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 270
  idEntry 10 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-3, 0, 0, 1, 6, by decide⟩, -- source row 273
  idEntry 10 4 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 274
  idEntry 10 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 275
  idEntry 10 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 276
  idEntry 10 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 279
  idEntry 10 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 280
  idEntry 11 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 302
  idEntry 11 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 303
  idEntry 11 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 306
  idEntry 11 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 307
  idEntry 12 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 324
  idEntry 12 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 325
  idEntry 12 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 326
  idEntry 12 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 327
  idEntry 12 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 328
  idEntry 12 5 ⟨0, 0, 0, 2, 3, by decide⟩, -- source row 329
  idEntry 12 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 333
  idEntry 12 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 334
  idEntry 13 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 351
  idEntry 13 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 353
  idEntry 13 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 354
  idEntry 13 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 355
  idEntry 13 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 357
  idEntry 13 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 360
  idEntry 13 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 361
  idEntry 14 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 381
  idEntry 14 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 382
  idEntry 14 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 387
  idEntry 14 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 388
  idEntry 15 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 405
  idEntry 15 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 406
  idEntry 15 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 407
  idEntry 15 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 408
  idEntry 15 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 409
  idEntry 15 5 ⟨0, 0, 0, 2, 3, by decide⟩, -- source row 410
  idEntry 15 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 414
  idEntry 15 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 415
  idEntry 16 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 432
  idEntry 16 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 434
  idEntry 16 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 435
  idEntry 16 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 436
  idEntry 16 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 437
  idEntry 16 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 438
  idEntry 16 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 441
  idEntry 16 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 442
  idEntry 17 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 462
  idEntry 17 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 463
  idEntry 17 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 468
  idEntry 17 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 469
  idEntry 18 0 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 486
  idEntry 18 1 ⟨0, 0, 0, -1, 6, by decide⟩, -- source row 487
  idEntry 18 2 ⟨0, 0, 0, 1, 2, by decide⟩, -- source row 488
  idEntry 18 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 489
  idEntry 18 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 490
  idEntry 18 5 ⟨0, 0, 0, 2, 3, by decide⟩, -- source row 491
  idEntry 18 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 495
  idEntry 18 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 496
  idEntry 19 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 513
  idEntry 19 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 515
  idEntry 19 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 516
  idEntry 19 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 517
  idEntry 19 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 518
  idEntry 19 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 519
  idEntry 19 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 522
  idEntry 19 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 523
  idEntry 20 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 543
  idEntry 20 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 544
  idEntry 20 9 ⟨3, 4, -4, 3, 20, by decide⟩, -- source row 549
  idEntry 20 10 ⟨-4, 3, -3, -4, 20, by decide⟩, -- source row 550
  idEntry 21 9 ⟨-1167, 908, -676, 507, 3380, by decide⟩, -- source row 576
  idEntry 21 10 ⟨-444, 2181, -507, -676, 3380, by decide⟩, -- source row 577
  idEntry 22 9 ⟨-1167, 908, -676, 507, 3380, by decide⟩, -- source row 603
  idEntry 22 10 ⟨-444, 2181, -507, -676, 3380, by decide⟩, -- source row 604
  idEntry 23 9 ⟨-1167, 908, -676, 507, 3380, by decide⟩, -- source row 630
  idEntry 23 10 ⟨-444, 2181, -507, -676, 3380, by decide⟩, -- source row 631
  idEntry 24 9 ⟨672, 280, -396, -165, 1690, by decide⟩, -- source row 657
  idEntry 24 10 ⟨-396, -165, -672, -280, 1690, by decide⟩, -- source row 658
  idEntry 25 9 ⟨672, 280, -396, -165, 1690, by decide⟩, -- source row 684
  idEntry 25 10 ⟨-396, -165, -672, -280, 1690, by decide⟩, -- source row 685
  idEntry 26 9 ⟨672, 280, -396, -165, 1690, by decide⟩, -- source row 711
  idEntry 26 10 ⟨-396, -165, -672, -280, 1690, by decide⟩, -- source row 712
  idEntry 27 9 ⟨336, 140, -140, 336, 845, by decide⟩, -- source row 738
  idEntry 27 10 ⟨-396, -165, 165, -396, 1690, by decide⟩, -- source row 739
  idEntry 28 9 ⟨336, 140, -140, 336, 845, by decide⟩, -- source row 765
  idEntry 28 10 ⟨-396, -165, 165, -396, 1690, by decide⟩, -- source row 766
  idEntry 29 9 ⟨336, 140, -140, 336, 845, by decide⟩, -- source row 792
  idEntry 29 10 ⟨-396, -165, 165, -396, 1690, by decide⟩, -- source row 793
  idEntry 30 0 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 810
  idEntry 30 1 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 811
  idEntry 30 2 ⟨154, 72, 36, -77, 510, by decide⟩, -- source row 812
  idEntry 30 9 ⟨154, 72, 0, 0, 289, by decide⟩, -- source row 819
  idEntry 30 10 ⟨-1232, -576, 0, 0, 4335, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 838
  idEntry 31 2 ⟨154, 72, -36, 77, 510, by decide⟩, -- source row 839
  idEntry 31 9 ⟨-1155, -540, -616, -288, 4335, by decide⟩, -- source row 846
  idEntry 31 10 ⟨616, 288, -1155, -540, 4335, by decide⟩, -- source row 847
  idEntry 32 0 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 864
  idEntry 32 1 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 865
  idEntry 32 2 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 866
  idEntry 33 0 ⟨77, 36, -36, 77, 1020, by decide⟩, -- source row 891
  idEntry 33 1 ⟨77, 36, -36, 77, 1020, by decide⟩, -- source row 892
  idEntry 33 2 ⟨-77, -36, 36, -77, 510, by decide⟩, -- source row 893
  idEntry 34 0 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 919
  idEntry 34 2 ⟨154, 72, -36, 77, 510, by decide⟩, -- source row 920
  idEntry 34 9 ⟨-1155, -540, -616, -288, 4335, by decide⟩, -- source row 927
  idEntry 34 10 ⟨616, 288, -1155, -540, 4335, by decide⟩, -- source row 928
  idEntry 35 2 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 947
  idEntry 35 9 ⟨1155, 540, -616, -288, 4335, by decide⟩, -- source row 954
  idEntry 35 10 ⟨-616, -288, -1155, -540, 4335, by decide⟩, -- source row 955
  idEntry 36 0 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 973
  idEntry 36 2 ⟨0, 0, 36, -77, 510, by decide⟩, -- source row 974
  idEntry 36 9 ⟨77, 36, 0, 0, 289, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-616, -288, 0, 0, 4335, by decide⟩, -- source row 982
  idEntry 37 0 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 999
  idEntry 37 1 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨0, 0, -36, 77, 510, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨-77, -36, 0, 0, 289, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨616, 288, 0, 0, 4335, by decide⟩, -- source row 1009
  idEntry 38 9 ⟨0, 0, -616, -288, 4335, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨0, 0, -77, -36, 289, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨4911, 4548, -2236, 3177, 17340, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨-4700, 2025, -291, -2388, 17340, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨0, 0, 308, 144, 4437, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨0, 0, -539, -252, 7395, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨11935, 5580, -12012, -5616, 251430, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨-108108, -50544, -11935, -5580, 754290, by decide⟩, -- source row 1116
  sumEntry 1 5 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1125
  sumEntry 1 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1128
  sumEntry 1 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1129
  sumEntry 1 13 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1133
  sumEntry 1 17 ⟨-3, -4, -4, 3, 60, by decide⟩, -- source row 1136
  sumEntry 1 18 ⟨4, -3, -3, -4, 60, by decide⟩, -- source row 1137
  sumEntry 1 21 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1141
  sumEntry 1 25 ⟨-3, -4, 0, 0, 30, by decide⟩, -- source row 1144
  sumEntry 1 26 ⟨4, -3, 0, 0, 30, by decide⟩, -- source row 1145
  sumEntry 2 5 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1152
  sumEntry 2 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1155
  sumEntry 2 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1156
  sumEntry 2 13 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1160
  sumEntry 2 17 ⟨-3, -4, 4, -3, 60, by decide⟩, -- source row 1163
  sumEntry 2 18 ⟨4, -3, 3, 4, 60, by decide⟩, -- source row 1164
  sumEntry 2 21 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1168
  sumEntry 2 25 ⟨3, 4, 4, -3, 60, by decide⟩, -- source row 1171
  sumEntry 2 26 ⟨-4, 3, 3, 4, 60, by decide⟩, -- source row 1172
  sumEntry 3 5 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1179
  sumEntry 3 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1182
  sumEntry 3 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1183
  sumEntry 3 13 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1187
  sumEntry 3 17 ⟨3, 4, 0, 0, 30, by decide⟩, -- source row 1190
  sumEntry 3 18 ⟨-4, 3, 0, 0, 30, by decide⟩, -- source row 1191
  sumEntry 3 21 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1195
  sumEntry 3 25 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1198
  sumEntry 3 26 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1199
  sumEntry 4 3 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1204
  sumEntry 4 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1209
  sumEntry 4 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1210
  sumEntry 4 11 ⟨3, 4, 0, 0, 30, by decide⟩, -- source row 1211
  sumEntry 4 12 ⟨4, -3, 0, 0, 30, by decide⟩, -- source row 1212
  sumEntry 4 17 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1218
  sumEntry 4 21 ⟨3, 4, 4, -3, 60, by decide⟩, -- source row 1221
  sumEntry 4 22 ⟨-4, 3, 3, 4, 60, by decide⟩, -- source row 1222
  sumEntry 4 23 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1231
  sumEntry 5 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1236
  sumEntry 5 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1237
  sumEntry 5 11 ⟨-3, -4, -4, 3, 60, by decide⟩, -- source row 1238
  sumEntry 5 12 ⟨-4, 3, 3, 4, 60, by decide⟩, -- source row 1239
  sumEntry 5 17 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1245
  sumEntry 5 21 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1248
  sumEntry 5 22 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1249
  sumEntry 5 23 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1258
  sumEntry 6 9 ⟨3, 4, -4, 3, 60, by decide⟩, -- source row 1263
  sumEntry 6 10 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1264
  sumEntry 6 11 ⟨-3, -4, 4, -3, 60, by decide⟩, -- source row 1265
  sumEntry 6 12 ⟨-4, 3, -3, -4, 60, by decide⟩, -- source row 1266
  sumEntry 6 17 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1272
  sumEntry 6 21 ⟨-3, -4, 0, 0, 30, by decide⟩, -- source row 1275
  sumEntry 6 22 ⟨4, -3, 0, 0, 30, by decide⟩, -- source row 1276
  sumEntry 6 23 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1278
  sumEntry 7 9 ⟨-1167, 908, -676, 507, 10140, by decide⟩, -- source row 1290
  sumEntry 7 10 ⟨-444, 2181, -507, -676, 10140, by decide⟩, -- source row 1291
  sumEntry 7 16 ⟨12, 5, 5, -12, 78, by decide⟩, -- source row 1297
  sumEntry 7 19 ⟨-93, 88, -56, 33, 780, by decide⟩, -- source row 1300
  sumEntry 7 20 ⟨-24, 159, -33, -56, 780, by decide⟩, -- source row 1301
  sumEntry 8 9 ⟨672, 280, -396, -165, 5070, by decide⟩, -- source row 1317
  sumEntry 8 10 ⟨-396, -165, -672, -280, 5070, by decide⟩, -- source row 1318
  sumEntry 8 16 ⟨-12, -5, 0, 0, 39, by decide⟩, -- source row 1324
  sumEntry 8 19 ⟨48, 20, 36, 15, 390, by decide⟩, -- source row 1327
  sumEntry 8 20 ⟨-36, -15, 48, 20, 390, by decide⟩, -- source row 1328
  sumEntry 9 9 ⟨336, 140, -140, 336, 2535, by decide⟩, -- source row 1344
  sumEntry 9 10 ⟨-132, -55, 55, -132, 1690, by decide⟩, -- source row 1345
  sumEntry 9 16 ⟨12, 5, -5, 12, 78, by decide⟩, -- source row 1351
  sumEntry 9 19 ⟨-3, -128, -16, -63, 780, by decide⟩, -- source row 1354
  sumEntry 9 20 ⟨96, -129, -63, 16, 780, by decide⟩, -- source row 1355
  sumEntry 10 0 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1362
  sumEntry 10 2 ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨0, 0, -616, -288, 13005, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨0, 0, -77, -36, 867, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨0, 0, 308, 144, 4437, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨0, 0, -539, -252, 7395, by decide⟩, -- source row 1376
  sumEntry 11 0 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1389
  sumEntry 11 1 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1390
  sumEntry 11 9 ⟨0, 0, -616, -288, 13005, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨0, 0, -77, -36, 867, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨4851, 2268, -1540, -720, 44370, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨1540, 720, 539, 252, 14790, by decide⟩, -- source row 1403
  sumEntry 12 1 ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1417
  sumEntry 12 9 ⟨-1155, -540, -616, -288, 8670, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨616, 288, -1155, -540, 8670, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨-1617, -756, -1540, -720, 14790, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨-1540, -720, 1617, 756, 14790, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨385, 180, -36, 77, 1020, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 1474
  pairEntry 0 33 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 1475
  pairEntry 0 34 (by decide) ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 1476
  pairEntry 0 36 (by decide) ⟨77, 36, -36, 77, 1020, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1480
  pairEntry 1 30 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 1509
  pairEntry 1 31 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 1510
  pairEntry 1 33 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 1512
  pairEntry 1 34 (by decide) ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 1513
  pairEntry 1 36 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 1515
  pairEntry 1 37 (by decide) ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨-77, -36, 0, 0, 255, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 1552
  pairEntry 3 12 (by decide) ⟨-1, -8, 0, 5, 60, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨4, 2, 2, 1, 30, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨2, 1, -1, 2, 15, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1569
  pairEntry 3 21 (by decide) ⟨-3, -128, 16, 63, 780, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨93, -88, 56, -33, 780, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨48, 20, -36, -15, 390, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨-48, -20, -36, -15, 390, by decide⟩, -- source row 1575
  pairEntry 3 27 (by decide) ⟨-93, 88, 56, -33, 780, by decide⟩, -- source row 1577
  pairEntry 3 28 (by decide) ⟨3, 128, 16, 63, 780, by decide⟩, -- source row 1578
  pairEntry 4 12 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨-7, 4, -4, 3, 60, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨-4, -2, 0, 0, 15, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨-7, 4, 4, -3, 60, by decide⟩, -- source row 1603
  pairEntry 4 21 (by decide) ⟨-24, -10, -10, 24, 195, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨-3, -128, 16, 63, 780, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨48, 20, 0, 0, 195, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨48, 20, -36, -15, 390, by decide⟩, -- source row 1609
  pairEntry 4 27 (by decide) ⟨-24, -10, 10, -24, 195, by decide⟩, -- source row 1611
  pairEntry 4 28 (by decide) ⟨-93, 88, 56, -33, 780, by decide⟩, -- source row 1612
  pairEntry 6 12 (by decide) ⟨4, 2, 2, 1, 30, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨2, 1, -1, 2, 15, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-1, -8, 0, 5, 60, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1668
  pairEntry 6 21 (by decide) ⟨-93, 88, -56, 33, 780, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨-24, -10, -10, 24, 195, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨48, 20, 36, 15, 390, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨48, 20, 0, 0, 195, by decide⟩, -- source row 1674
  pairEntry 6 27 (by decide) ⟨-3, -128, -16, -63, 780, by decide⟩, -- source row 1676
  pairEntry 6 28 (by decide) ⟨-24, -10, 10, -24, 195, by decide⟩, -- source row 1677
  pairEntry 7 12 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨-4, -2, 0, 0, 15, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨-7, 4, 4, -3, 60, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-7, 4, -4, 3, 60, by decide⟩, -- source row 1699
  pairEntry 7 21 (by decide) ⟨3, 128, -16, -63, 780, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨-93, 88, -56, 33, 780, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨-48, -20, 36, 15, 390, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨48, 20, 36, 15, 390, by decide⟩, -- source row 1705
  pairEntry 7 27 (by decide) ⟨93, -88, -56, 33, 780, by decide⟩, -- source row 1707
  pairEntry 7 28 (by decide) ⟨-3, -128, -16, -63, 780, by decide⟩, -- source row 1708
  pairEntry 9 12 (by decide) ⟨2, 1, -1, 2, 15, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨-1, -8, 0, 5, 60, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨4, 2, 2, 1, 30, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1758
  pairEntry 9 21 (by decide) ⟨24, 10, 10, -24, 195, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨3, 128, -16, -63, 780, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨-48, -20, 0, 0, 195, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨-48, -20, 36, 15, 390, by decide⟩, -- source row 1764
  pairEntry 9 27 (by decide) ⟨24, 10, -10, 24, 195, by decide⟩, -- source row 1766
  pairEntry 9 28 (by decide) ⟨93, -88, -56, 33, 780, by decide⟩, -- source row 1767
  pairEntry 10 12 (by decide) ⟨1, 8, 0, 5, 60, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨-7, 4, 4, -3, 60, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨-2, -1, -1, 2, 15, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨-7, 4, -4, 3, 60, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨-4, -2, 2, 1, 30, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨-4, -2, 0, 0, 15, by decide⟩, -- source row 1786
  pairEntry 10 21 (by decide) ⟨93, -88, 56, -33, 780, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨24, 10, 10, -24, 195, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨-48, -20, -36, -15, 390, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨-48, -20, 0, 0, 195, by decide⟩, -- source row 1792
  pairEntry 10 27 (by decide) ⟨3, 128, 16, 63, 780, by decide⟩, -- source row 1794
  pairEntry 10 28 (by decide) ⟨24, 10, -10, 24, 195, by decide⟩, -- source row 1795
  pairEntry 12 22 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1842
  pairEntry 12 25 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1845
  pairEntry 12 28 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1848
  pairEntry 13 21 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1873
  pairEntry 15 21 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1913
  pairEntry 15 24 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1916
  pairEntry 15 27 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1919
  pairEntry 16 22 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1936
  pairEntry 16 25 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1939
  pairEntry 16 28 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1942
  pairEntry 18 21 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1983
  pairEntry 19 21 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1995
  pairEntry 19 24 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1998
  pairEntry 19 27 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 2001
  pairEntry 30 33 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨77, 36, -36, 77, 1020, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨77, 36, -36, 77, 1020, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩ -- source row 2178
]

end Option2.NativeStress.NativeT

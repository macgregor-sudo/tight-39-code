module

public import NativeHWeights

@[expose] public section

/-! Exact source λ9; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda9 : List Entry := [
  idEntry 0 0 ⟨77, 36, 0, 0, 255, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-77, -36, 0, 0, 255, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-77, -36, 0, 0, 255, by decide⟩, -- source row 2
  idEntry 1 0 ⟨-77, -36, 0, 0, 340, by decide⟩, -- source row 27
  idEntry 1 1 ⟨77, 36, 0, 0, 340, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-77, -36, 0, 0, 340, by decide⟩, -- source row 29
  idEntry 2 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 61
  idEntry 2 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 62
  idEntry 3 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 81
  idEntry 3 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 83
  idEntry 3 3 ⟨3, 0, 0, -1, 3, by decide⟩, -- source row 84
  idEntry 3 5 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 86
  idEntry 3 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 87
  idEntry 3 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 88
  idEntry 3 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 89
  idEntry 4 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 108
  idEntry 4 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 111
  idEntry 4 4 ⟨0, -1, -1, 0, 2, by decide⟩, -- source row 112
  idEntry 4 5 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 113
  idEntry 4 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 114
  idEntry 4 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 115
  idEntry 4 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 116
  idEntry 5 5 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 140
  idEntry 5 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 141
  idEntry 5 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 142
  idEntry 5 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 143
  idEntry 6 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 162
  idEntry 6 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 163
  idEntry 6 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 164
  idEntry 6 3 ⟨3, 0, 0, -1, 3, by decide⟩, -- source row 165
  idEntry 6 5 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 167
  idEntry 6 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 168
  idEntry 6 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 169
  idEntry 6 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 170
  idEntry 7 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 189
  idEntry 7 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 192
  idEntry 7 4 ⟨0, -1, -1, 0, 2, by decide⟩, -- source row 193
  idEntry 7 5 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 194
  idEntry 7 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 195
  idEntry 7 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 196
  idEntry 7 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 197
  idEntry 8 5 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 221
  idEntry 8 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 222
  idEntry 8 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 223
  idEntry 8 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 224
  idEntry 9 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 243
  idEntry 9 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 244
  idEntry 9 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 245
  idEntry 9 3 ⟨3, 0, 0, -1, 3, by decide⟩, -- source row 246
  idEntry 9 5 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 248
  idEntry 9 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 249
  idEntry 9 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 250
  idEntry 9 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 251
  idEntry 10 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 270
  idEntry 10 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-3, 0, 0, -1, 6, by decide⟩, -- source row 273
  idEntry 10 4 ⟨0, -1, -1, 0, 2, by decide⟩, -- source row 274
  idEntry 10 5 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 275
  idEntry 10 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 276
  idEntry 10 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 277
  idEntry 10 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 278
  idEntry 11 5 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 302
  idEntry 11 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 303
  idEntry 11 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 304
  idEntry 11 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 305
  idEntry 12 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 324
  idEntry 12 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 325
  idEntry 12 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 326
  idEntry 12 3 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 327
  idEntry 12 4 ⟨0, 1, 0, 0, 2, by decide⟩, -- source row 328
  idEntry 12 5 ⟨-3, 0, 0, -1, 3, by decide⟩, -- source row 329
  idEntry 12 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 331
  idEntry 12 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 332
  idEntry 13 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 351
  idEntry 13 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 353
  idEntry 13 3 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 354
  idEntry 13 4 ⟨0, -1, 1, 0, 4, by decide⟩, -- source row 355
  idEntry 13 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 357
  idEntry 13 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 358
  idEntry 13 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 359
  idEntry 14 3 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 381
  idEntry 14 4 ⟨0, -1, -1, 0, 4, by decide⟩, -- source row 382
  idEntry 14 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 385
  idEntry 14 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 386
  idEntry 15 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 405
  idEntry 15 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 406
  idEntry 15 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 407
  idEntry 15 3 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 408
  idEntry 15 4 ⟨0, 1, 0, 0, 2, by decide⟩, -- source row 409
  idEntry 15 5 ⟨-3, 0, 0, -1, 3, by decide⟩, -- source row 410
  idEntry 15 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 412
  idEntry 15 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 413
  idEntry 16 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 432
  idEntry 16 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 434
  idEntry 16 3 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 435
  idEntry 16 4 ⟨0, -1, 1, 0, 4, by decide⟩, -- source row 436
  idEntry 16 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 437
  idEntry 16 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 438
  idEntry 16 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 439
  idEntry 16 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 440
  idEntry 17 3 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 462
  idEntry 17 4 ⟨0, -1, -1, 0, 4, by decide⟩, -- source row 463
  idEntry 17 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 466
  idEntry 17 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 467
  idEntry 18 0 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 486
  idEntry 18 1 ⟨3, 0, 0, 1, 12, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-3, 0, 0, -1, 4, by decide⟩, -- source row 488
  idEntry 18 3 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 489
  idEntry 18 4 ⟨0, 1, 0, 0, 2, by decide⟩, -- source row 490
  idEntry 18 5 ⟨-3, 0, 0, -1, 3, by decide⟩, -- source row 491
  idEntry 18 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 493
  idEntry 18 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 494
  idEntry 19 0 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 513
  idEntry 19 1 ⟨3, 0, 0, -1, 12, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-3, 0, 0, 1, 4, by decide⟩, -- source row 515
  idEntry 19 3 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 516
  idEntry 19 4 ⟨0, -1, 1, 0, 4, by decide⟩, -- source row 517
  idEntry 19 5 ⟨3, 0, 0, -1, 6, by decide⟩, -- source row 518
  idEntry 19 6 ⟨0, 1, -1, 0, 2, by decide⟩, -- source row 519
  idEntry 19 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 520
  idEntry 19 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 521
  idEntry 20 3 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 543
  idEntry 20 4 ⟨0, -1, -1, 0, 4, by decide⟩, -- source row 544
  idEntry 20 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 547
  idEntry 20 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 548
  idEntry 21 0 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 568
  idEntry 21 2 ⟨77, 36, 36, -77, 510, by decide⟩, -- source row 569
  idEntry 22 0 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 594
  idEntry 22 1 ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 595
  idEntry 22 2 ⟨77, 36, -36, 77, 510, by decide⟩, -- source row 596
  idEntry 23 0 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 621
  idEntry 23 1 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 622
  idEntry 23 2 ⟨-77, -36, 0, 0, 1020, by decide⟩, -- source row 623
  idEntry 23 7 ⟨-231, -108, 308, 144, 2550, by decide⟩, -- source row 628
  idEntry 23 8 ⟨-308, -144, -231, -108, 2550, by decide⟩, -- source row 629
  idEntry 24 0 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 648
  idEntry 24 1 ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 649
  idEntry 24 2 ⟨77, 36, 36, -77, 510, by decide⟩, -- source row 650
  idEntry 25 0 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 675
  idEntry 25 1 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 676
  idEntry 25 2 ⟨-154, -72, -36, 77, 510, by decide⟩, -- source row 677
  idEntry 25 7 ⟨231, 108, 308, 144, 1275, by decide⟩, -- source row 682
  idEntry 25 8 ⟨308, 144, -231, -108, 1275, by decide⟩, -- source row 683
  idEntry 26 2 ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 704
  idEntry 26 7 ⟨-231, -108, 308, 144, 1275, by decide⟩, -- source row 709
  idEntry 26 8 ⟨-308, -144, -231, -108, 1275, by decide⟩, -- source row 710
  idEntry 27 0 ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 729
  idEntry 27 1 ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 730
  idEntry 27 2 ⟨231, 108, 36, -77, 510, by decide⟩, -- source row 731
  idEntry 27 7 ⟨231, 108, 0, 0, 850, by decide⟩, -- source row 736
  idEntry 27 8 ⟨154, 72, 0, 0, 425, by decide⟩, -- source row 737
  idEntry 28 0 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 756
  idEntry 28 1 ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-231, -108, -72, 154, 1020, by decide⟩, -- source row 758
  idEntry 28 7 ⟨231, 108, 616, 288, 2550, by decide⟩, -- source row 763
  idEntry 28 8 ⟨154, 72, -231, -108, 1275, by decide⟩, -- source row 764
  idEntry 29 0 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 783
  idEntry 29 1 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 784
  idEntry 29 7 ⟨-231, -108, 154, 72, 1275, by decide⟩, -- source row 790
  idEntry 29 8 ⟨-616, -288, -231, -108, 2550, by decide⟩, -- source row 791
  idEntry 30 7 ⟨-405, 32584, 6728, 12615, 57188, by decide⟩, -- source row 817
  idEntry 30 8 ⟨19128, -24825, -12615, 6728, 57188, by decide⟩, -- source row 818
  idEntry 31 7 ⟨-405, 32584, 6728, 12615, 57188, by decide⟩, -- source row 844
  idEntry 31 8 ⟨19128, -24825, -12615, 6728, 57188, by decide⟩, -- source row 845
  idEntry 32 7 ⟨-405, 32584, 6728, 12615, 57188, by decide⟩, -- source row 871
  idEntry 32 8 ⟨19128, -24825, -12615, 6728, 57188, by decide⟩, -- source row 872
  idEntry 33 7 ⟨-4680, -1550, -1550, 4680, 14297, by decide⟩, -- source row 898
  idEntry 33 8 ⟨-9828, -3255, -3255, 9828, 28594, by decide⟩, -- source row 899
  idEntry 34 7 ⟨-4680, -1550, -1550, 4680, 14297, by decide⟩, -- source row 925
  idEntry 34 8 ⟨-9828, -3255, -3255, 9828, 28594, by decide⟩, -- source row 926
  idEntry 35 7 ⟨-4680, -1550, -1550, 4680, 14297, by decide⟩, -- source row 952
  idEntry 35 8 ⟨-9828, -3255, -3255, 9828, 28594, by decide⟩, -- source row 953
  idEntry 36 7 ⟨-9360, -3100, 9828, 3255, 28594, by decide⟩, -- source row 979
  idEntry 36 8 ⟨-9828, -3255, -9360, -3100, 28594, by decide⟩, -- source row 980
  idEntry 37 7 ⟨-9360, -3100, 9828, 3255, 28594, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨-9828, -3255, -9360, -3100, 28594, by decide⟩, -- source row 1007
  idEntry 38 7 ⟨-9360, -3100, 9828, 3255, 28594, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨-9828, -3255, -9360, -3100, 28594, by decide⟩, -- source row 1034
  sumEntry 0 7 ⟨-894, 708, 292, 981, 5100, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨-292, -981, -894, 708, 5100, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨2541, 1188, 4312, 2016, 66300, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨4312, 2016, -2541, -1188, 66300, by decide⟩, -- source row 1114
  sumEntry 1 5 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1125
  sumEntry 1 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1126
  sumEntry 1 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1127
  sumEntry 1 13 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1133
  sumEntry 1 15 ⟨15, -8, 8, 15, 204, by decide⟩, -- source row 1134
  sumEntry 1 16 ⟨8, 15, -15, 8, 204, by decide⟩, -- source row 1135
  sumEntry 1 21 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1141
  sumEntry 1 23 ⟨15, -8, 0, 0, 102, by decide⟩, -- source row 1142
  sumEntry 1 24 ⟨8, 15, 0, 0, 102, by decide⟩, -- source row 1143
  sumEntry 2 5 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1152
  sumEntry 2 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1153
  sumEntry 2 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1154
  sumEntry 2 13 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1160
  sumEntry 2 15 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1161
  sumEntry 2 16 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1162
  sumEntry 2 21 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1168
  sumEntry 2 23 ⟨-15, 8, -8, -15, 204, by decide⟩, -- source row 1169
  sumEntry 2 24 ⟨-8, -15, 15, -8, 204, by decide⟩, -- source row 1170
  sumEntry 3 5 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1179
  sumEntry 3 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1180
  sumEntry 3 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1181
  sumEntry 3 13 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1187
  sumEntry 3 15 ⟨-15, 8, 0, 0, 102, by decide⟩, -- source row 1188
  sumEntry 3 16 ⟨-8, -15, 0, 0, 102, by decide⟩, -- source row 1189
  sumEntry 3 21 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1195
  sumEntry 3 23 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1196
  sumEntry 3 24 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1197
  sumEntry 4 3 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1204
  sumEntry 4 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1207
  sumEntry 4 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1208
  sumEntry 4 13 ⟨-15, 8, -8, -15, 204, by decide⟩, -- source row 1213
  sumEntry 4 14 ⟨8, 15, -15, 8, 204, by decide⟩, -- source row 1214
  sumEntry 4 17 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1218
  sumEntry 4 19 ⟨15, -8, 0, 0, 102, by decide⟩, -- source row 1219
  sumEntry 4 20 ⟨8, 15, 0, 0, 102, by decide⟩, -- source row 1220
  sumEntry 4 23 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1231
  sumEntry 5 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1234
  sumEntry 5 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1235
  sumEntry 5 13 ⟨15, -8, 0, 0, 102, by decide⟩, -- source row 1240
  sumEntry 5 14 ⟨-8, -15, 0, 0, 102, by decide⟩, -- source row 1241
  sumEntry 5 17 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1245
  sumEntry 5 19 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1246
  sumEntry 5 20 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1247
  sumEntry 5 23 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1258
  sumEntry 6 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1261
  sumEntry 6 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1262
  sumEntry 6 13 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1267
  sumEntry 6 14 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1268
  sumEntry 6 17 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1272
  sumEntry 6 19 ⟨-15, 8, -8, -15, 204, by decide⟩, -- source row 1273
  sumEntry 6 20 ⟨-8, -15, 15, -8, 204, by decide⟩, -- source row 1274
  sumEntry 6 23 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1278
  sumEntry 7 0 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨0, 0, 308, 144, 3825, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨0, 0, -77, -36, 1275, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨0, 0, -308, -144, 3315, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨0, 0, -77, -36, 1989, by decide⟩, -- source row 1299
  sumEntry 8 0 ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 1308
  sumEntry 8 1 ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 1309
  sumEntry 8 7 ⟨0, 0, 308, 144, 3825, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨0, 0, -77, -36, 1275, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨-385, -180, 308, 144, 6630, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨2772, 1296, 385, 180, 19890, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1335
  sumEntry 9 7 ⟨-231, -108, 308, 144, 5100, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨-308, -144, -231, -108, 5100, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨77, 36, 0, 0, 1326, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨-154, -72, 0, 0, 1105, by decide⟩, -- source row 1353
  sumEntry 10 7 ⟨-405, 32584, 6728, 12615, 171564, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨19128, -24825, -12615, 6728, 171564, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨-3231, 22300, 5780, 6069, 100572, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨-10740, 8907, 6069, -5780, 100572, by decide⟩, -- source row 1374
  sumEntry 10 26 ⟨-468, -155, 155, -468, 2958, by decide⟩, -- source row 1388
  sumEntry 11 7 ⟨-4680, -1550, -1550, 4680, 42891, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨-3276, -1085, -1085, 3276, 28594, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨10719, -19820, 8260, -1419, 100572, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨-3300, -13557, 1419, 8260, 100572, by decide⟩, -- source row 1401
  sumEntry 11 26 ⟨-468, -155, -155, 468, 2958, by decide⟩, -- source row 1415
  sumEntry 12 7 ⟨-9360, -3100, 9828, 3255, 85782, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨-9828, -3255, -9360, -3100, 85782, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨-3744, -1240, -7020, -2325, 50286, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨7020, 2325, -3744, -1240, 50286, by decide⟩, -- source row 1428
  sumEntry 12 26 ⟨468, 155, 0, 0, 1479, by decide⟩, -- source row 1442
  pairEntry 0 21 (by decide) ⟨-154, -72, -36, 77, 1020, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 1464
  pairEntry 0 24 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 1466
  pairEntry 0 25 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 1467
  pairEntry 0 27 (by decide) ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨-154, -72, 36, -77, 1020, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨-154, -72, -36, 77, 1020, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 1501
  pairEntry 1 24 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 1503
  pairEntry 1 25 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 1504
  pairEntry 1 27 (by decide) ⟨0, 0, -36, 77, 1020, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨-77, -36, 36, -77, 1020, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨-77, -36, 0, 0, 1020, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨-77, -36, 0, 0, 1020, by decide⟩, -- source row 1544
  pairEntry 3 12 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨-47, 16, 0, 17, 204, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨-1, -4, -4, 1, 102, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨-1, -4, 4, 16, 102, by decide⟩, -- source row 1569
  pairEntry 3 30 (by decide) ⟨3231, -22300, -5780, -6069, 100572, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-1872, -620, 620, -1872, 25143, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨-10719, 19820, -8260, 1419, 100572, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨-1872, -620, -620, 1872, 25143, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨3744, 1240, 7020, 2325, 50286, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨3744, 1240, 0, 0, 25143, by decide⟩, -- source row 1587
  pairEntry 4 12 (by decide) ⟨-1, -4, 4, -1, 102, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨-47, 16, 0, -17, 204, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨-1, -4, -4, -16, 102, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1603
  pairEntry 4 30 (by decide) ⟨-1872, -620, 620, -1872, 25143, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨-10719, 19820, 8260, -1419, 100572, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨-1872, -620, -620, 1872, 25143, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨3231, -22300, 5780, 6069, 100572, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨3744, 1240, 0, 0, 25143, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨3744, 1240, -7020, -2325, 50286, by decide⟩, -- source row 1621
  pairEntry 6 12 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨-1, -4, 4, 16, 102, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨-47, 16, 0, 17, 204, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-1, -4, -4, 1, 102, by decide⟩, -- source row 1668
  pairEntry 6 30 (by decide) ⟨1872, 620, -620, 1872, 25143, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨10719, -19820, -8260, 1419, 100572, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨1872, 620, 620, -1872, 25143, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨-3231, 22300, -5780, -6069, 100572, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨-3744, -1240, 0, 0, 25143, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨-3744, -1240, 7020, 2325, 50286, by decide⟩, -- source row 1686
  pairEntry 7 12 (by decide) ⟨-1, -4, -4, -16, 102, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨-1, -4, 4, -1, 102, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-47, 16, 0, -17, 204, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1699
  pairEntry 7 30 (by decide) ⟨10719, -19820, -8260, 1419, 100572, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨3231, -22300, -5780, -6069, 100572, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨-3231, 22300, -5780, -6069, 100572, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨-10719, 19820, -8260, 1419, 100572, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨-3744, -1240, 7020, 2325, 50286, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨3744, 1240, 7020, 2325, 50286, by decide⟩, -- source row 1717
  pairEntry 9 12 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨-1, -4, -4, 1, 102, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨-1, -4, 4, 16, 102, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨-47, 16, 0, 17, 204, by decide⟩, -- source row 1758
  pairEntry 9 30 (by decide) ⟨-10719, 19820, 8260, -1419, 100572, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨-3231, 22300, 5780, 6069, 100572, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨3231, -22300, 5780, 6069, 100572, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨10719, -19820, 8260, -1419, 100572, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨3744, 1240, -7020, -2325, 50286, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨-3744, -1240, -7020, -2325, 50286, by decide⟩, -- source row 1776
  pairEntry 10 12 (by decide) ⟨-47, 16, 0, -17, 204, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨-49, 8, -8, -15, 204, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨-1, -4, -4, -16, 102, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨-1, -4, 0, 0, 51, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨-1, -4, 4, -1, 102, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨-49, 8, 8, 15, 204, by decide⟩, -- source row 1786
  pairEntry 10 30 (by decide) ⟨-3231, 22300, 5780, 6069, 100572, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨1872, 620, -620, 1872, 25143, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨10719, -19820, 8260, -1419, 100572, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨1872, 620, 620, -1872, 25143, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨-3744, -1240, -7020, -2325, 50286, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨-3744, -1240, 0, 0, 25143, by decide⟩, -- source row 1804
  pairEntry 12 31 (by decide) ⟨-465, 1404, 468, 155, 5916, by decide⟩, -- source row 1851
  pairEntry 12 34 (by decide) ⟨465, -1404, 468, 155, 5916, by decide⟩, -- source row 1854
  pairEntry 12 37 (by decide) ⟨0, 0, -468, -155, 2958, by decide⟩, -- source row 1857
  pairEntry 13 30 (by decide) ⟨-465, 1404, 468, 155, 5916, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨-465, 1404, 468, 155, 5916, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨465, -1404, 468, 155, 5916, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨465, -1404, 468, 155, 5916, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨0, 0, -468, -155, 2958, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨0, 0, -468, -155, 2958, by decide⟩, -- source row 1882
  pairEntry 15 30 (by decide) ⟨465, -1404, -468, -155, 5916, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨465, -1404, -468, -155, 5916, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨-465, 1404, -468, -155, 5916, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨-465, 1404, -468, -155, 5916, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨0, 0, 468, 155, 2958, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨0, 0, 468, 155, 2958, by decide⟩, -- source row 1929
  pairEntry 16 30 (by decide) ⟨465, -1404, -468, -155, 5916, by decide⟩, -- source row 1944
  pairEntry 16 33 (by decide) ⟨-465, 1404, -468, -155, 5916, by decide⟩, -- source row 1947
  pairEntry 16 36 (by decide) ⟨0, 0, 468, 155, 2958, by decide⟩, -- source row 1950
  pairEntry 18 30 (by decide) ⟨-465, 1404, 468, 155, 5916, by decide⟩, -- source row 1985
  pairEntry 18 33 (by decide) ⟨465, -1404, 468, 155, 5916, by decide⟩, -- source row 1988
  pairEntry 18 36 (by decide) ⟨0, 0, -468, -155, 2958, by decide⟩, -- source row 1991
  pairEntry 19 31 (by decide) ⟨465, -1404, -468, -155, 5916, by decide⟩, -- source row 2005
  pairEntry 19 34 (by decide) ⟨-465, 1404, -468, -155, 5916, by decide⟩, -- source row 2008
  pairEntry 19 37 (by decide) ⟨0, 0, 468, 155, 2958, by decide⟩, -- source row 2011
  pairEntry 21 24 (by decide) ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨-77, -36, 0, 0, 1020, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨0, 0, -36, 77, 1020, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨77, 36, 0, 0, 1020, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨77, 36, 36, -77, 1020, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨-77, -36, 0, 0, 510, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨-77, -36, -36, 77, 1020, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨77, 36, 0, 0, 510, by decide⟩ -- source row 2106
]

end Option2.NativeStress.NativeT

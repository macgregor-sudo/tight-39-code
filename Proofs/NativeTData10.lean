module

public import NativeHWeights

@[expose] public section

/-! Exact source λ6; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda6 : List Entry := [
  idEntry 0 25 ⟨63, -16, -16, -63, 260, by decide⟩, -- source row 25
  idEntry 0 26 ⟨-16, -63, -63, 16, 260, by decide⟩, -- source row 26
  idEntry 1 0 ⟨63, -16, 16, 63, 390, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-63, 16, -16, -63, 390, by decide⟩, -- source row 28
  idEntry 1 2 ⟨63, -16, 16, 63, 390, by decide⟩, -- source row 29
  idEntry 3 0 ⟨3219, 792, 2032, -2399, 13260, by decide⟩, -- source row 81
  idEntry 3 1 ⟨3219, 792, 2032, -2399, 13260, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-3219, -792, -2032, 2399, 4420, by decide⟩, -- source row 83
  idEntry 3 3 ⟨3219, 792, 2032, -2399, 3315, by decide⟩, -- source row 84
  idEntry 3 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 88
  idEntry 3 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 89
  idEntry 3 9 ⟨63, -16, -16, -63, 260, by decide⟩, -- source row 90
  idEntry 3 10 ⟨-16, -63, -63, 16, 260, by decide⟩, -- source row 91
  idEntry 4 0 ⟨1989, 2652, 1412, -2809, 13260, by decide⟩, -- source row 108
  idEntry 4 1 ⟨1989, 2652, 1412, -2809, 13260, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-1989, -2652, -1412, 2809, 4420, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-1989, -2652, -1412, 2809, 6630, by decide⟩, -- source row 111
  idEntry 4 4 ⟨-1412, 2809, -663, -884, 2210, by decide⟩, -- source row 112
  idEntry 4 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 115
  idEntry 4 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 116
  idEntry 4 9 ⟨-63, 16, 0, 0, 130, by decide⟩, -- source row 117
  idEntry 4 10 ⟨16, 63, 0, 0, 130, by decide⟩, -- source row 118
  idEntry 5 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 142
  idEntry 5 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 143
  idEntry 5 9 ⟨63, -16, 16, 63, 260, by decide⟩, -- source row 144
  idEntry 5 10 ⟨-16, -63, 63, -16, 260, by decide⟩, -- source row 145
  idEntry 6 0 ⟨0, 0, 62, 41, 663, by decide⟩, -- source row 162
  idEntry 6 1 ⟨0, 0, 62, 41, 663, by decide⟩, -- source row 163
  idEntry 6 2 ⟨0, 0, -62, -41, 221, by decide⟩, -- source row 164
  idEntry 6 3 ⟨0, 0, 248, 164, 663, by decide⟩, -- source row 165
  idEntry 6 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 169
  idEntry 6 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 170
  idEntry 6 9 ⟨63, -16, 16, 63, 260, by decide⟩, -- source row 171
  idEntry 6 10 ⟨-16, -63, 63, -16, 260, by decide⟩, -- source row 172
  idEntry 7 0 ⟨2604, 1722, 310, 205, 6630, by decide⟩, -- source row 189
  idEntry 7 1 ⟨2604, 1722, 310, 205, 6630, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-2604, -1722, -310, -205, 2210, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-2604, -1722, -310, -205, 3315, by decide⟩, -- source row 192
  idEntry 7 4 ⟨-310, -205, -868, -574, 1105, by decide⟩, -- source row 193
  idEntry 7 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 196
  idEntry 7 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 197
  idEntry 7 9 ⟨63, -16, -16, -63, 260, by decide⟩, -- source row 198
  idEntry 7 10 ⟨-16, -63, -63, 16, 260, by decide⟩, -- source row 199
  idEntry 8 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 223
  idEntry 8 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 224
  idEntry 8 9 ⟨-63, 16, 0, 0, 130, by decide⟩, -- source row 225
  idEntry 8 10 ⟨16, 63, 0, 0, 130, by decide⟩, -- source row 226
  idEntry 9 0 ⟨-3219, -792, 2032, -2399, 13260, by decide⟩, -- source row 243
  idEntry 9 1 ⟨-3219, -792, 2032, -2399, 13260, by decide⟩, -- source row 244
  idEntry 9 2 ⟨3219, 792, -2032, 2399, 4420, by decide⟩, -- source row 245
  idEntry 9 3 ⟨-3219, -792, 2032, -2399, 3315, by decide⟩, -- source row 246
  idEntry 9 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 250
  idEntry 9 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 251
  idEntry 9 9 ⟨-63, 16, 0, 0, 130, by decide⟩, -- source row 252
  idEntry 9 10 ⟨16, 63, 0, 0, 130, by decide⟩, -- source row 253
  idEntry 10 0 ⟨-123, 186, 62, 41, 1326, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-123, 186, 62, 41, 1326, by decide⟩, -- source row 271
  idEntry 10 2 ⟨123, -186, -62, -41, 442, by decide⟩, -- source row 272
  idEntry 10 3 ⟨123, -186, -62, -41, 663, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-62, -41, 41, -62, 221, by decide⟩, -- source row 274
  idEntry 10 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 277
  idEntry 10 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 278
  idEntry 10 9 ⟨63, -16, 16, 63, 260, by decide⟩, -- source row 279
  idEntry 10 10 ⟨-16, -63, 63, -16, 260, by decide⟩, -- source row 280
  idEntry 11 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 304
  idEntry 11 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 305
  idEntry 11 9 ⟨63, -16, -16, -63, 260, by decide⟩, -- source row 306
  idEntry 11 10 ⟨-16, -63, -63, 16, 260, by decide⟩, -- source row 307
  idEntry 12 0 ⟨-819, 208, 176, 693, 2340, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-126, 32, 16, 63, 1170, by decide⟩, -- source row 325
  idEntry 12 2 ⟨63, -16, -16, -63, 260, by decide⟩, -- source row 326
  idEntry 12 5 ⟨819, -208, -176, -693, 2340, by decide⟩, -- source row 329
  idEntry 12 6 ⟨-48, -189, -63, 16, 780, by decide⟩, -- source row 330
  idEntry 13 0 ⟨63, -16, -80, -315, 1170, by decide⟩, -- source row 351
  idEntry 13 1 ⟨693, -176, -16, -63, 2340, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-189, 48, 16, 63, 390, by decide⟩, -- source row 353
  idEntry 13 5 ⟨63, -16, 16, 63, 2340, by decide⟩, -- source row 356
  idEntry 13 6 ⟨240, 945, -1197, 304, 2340, by decide⟩, -- source row 357
  idEntry 14 0 ⟨441, -112, 16, 63, 1170, by decide⟩, -- source row 378
  idEntry 14 1 ⟨-126, 32, 16, 63, 1170, by decide⟩, -- source row 379
  idEntry 14 2 ⟨0, 0, -16, -63, 390, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-693, 176, 208, 819, 2340, by decide⟩, -- source row 383
  idEntry 14 6 ⟨48, 189, 63, -16, 2340, by decide⟩, -- source row 384
  idEntry 15 0 ⟨567, -144, 16, 63, 1170, by decide⟩, -- source row 405
  idEntry 15 1 ⟨0, 0, 16, 63, 1170, by decide⟩, -- source row 406
  idEntry 15 2 ⟨-189, 48, 16, 63, 780, by decide⟩, -- source row 407
  idEntry 15 5 ⟨-567, 144, 16, 63, 2340, by decide⟩, -- source row 410
  idEntry 15 6 ⟨-16, -63, -63, 16, 260, by decide⟩, -- source row 411
  idEntry 16 0 ⟨-189, 48, 64, 252, 1170, by decide⟩, -- source row 432
  idEntry 16 1 ⟨189, -48, -16, -63, 2340, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-63, 16, -16, -63, 130, by decide⟩, -- source row 434
  idEntry 16 5 ⟨945, -240, 208, 819, 2340, by decide⟩, -- source row 437
  idEntry 16 6 ⟨-112, -441, -189, 48, 780, by decide⟩, -- source row 438
  idEntry 17 0 ⟨-189, 48, -112, -441, 2340, by decide⟩, -- source row 459
  idEntry 17 1 ⟨189, -48, 16, 63, 1170, by decide⟩, -- source row 460
  idEntry 17 2 ⟨0, 0, 16, 63, 390, by decide⟩, -- source row 461
  idEntry 17 5 ⟨1323, -336, 112, 441, 2340, by decide⟩, -- source row 464
  idEntry 17 6 ⟨-80, -315, -63, 16, 780, by decide⟩, -- source row 465
  idEntry 18 0 ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 486
  idEntry 18 1 ⟨63, -16, 16, 63, 390, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 488
  idEntry 18 5 ⟨-63, 16, -16, -63, 260, by decide⟩, -- source row 491
  idEntry 18 6 ⟨48, 189, 63, -16, 780, by decide⟩, -- source row 492
  idEntry 19 0 ⟨189, -48, 16, 63, 780, by decide⟩, -- source row 513
  idEntry 19 1 ⟨-189, 48, 16, 63, 780, by decide⟩, -- source row 514
  idEntry 19 2 ⟨63, -16, -16, -63, 390, by decide⟩, -- source row 515
  idEntry 19 5 ⟨-63, 16, 48, 189, 780, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-16, -63, 63, -16, 260, by decide⟩, -- source row 519
  idEntry 20 0 ⟨-63, 16, 16, 63, 260, by decide⟩, -- source row 540
  idEntry 20 2 ⟨63, -16, -48, -189, 390, by decide⟩, -- source row 542
  idEntry 20 5 ⟨-63, 16, 48, 189, 780, by decide⟩, -- source row 545
  idEntry 20 6 ⟨144, 567, -63, 16, 780, by decide⟩, -- source row 546
  idEntry 21 0 ⟨-3, -4, 4, -3, 20, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-3, -4, 4, -3, 20, by decide⟩, -- source row 568
  idEntry 21 2 ⟨9, 12, -12, 9, 20, by decide⟩, -- source row 569
  idEntry 21 3 ⟨9, 12, 4, -3, 20, by decide⟩, -- source row 570
  idEntry 21 4 ⟨12, -9, -3, -4, 20, by decide⟩, -- source row 571
  idEntry 21 7 ⟨9, 12, -12, 9, 25, by decide⟩, -- source row 574
  idEntry 21 8 ⟨12, 16, -16, 12, 25, by decide⟩, -- source row 575
  idEntry 22 0 ⟨3, 4, 4, -3, 20, by decide⟩, -- source row 594
  idEntry 22 1 ⟨3, 4, 4, -3, 20, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-9, -12, -12, 9, 20, by decide⟩, -- source row 596
  idEntry 22 3 ⟨0, 0, -4, 3, 10, by decide⟩, -- source row 597
  idEntry 22 4 ⟨0, 0, 3, 4, 10, by decide⟩, -- source row 598
  idEntry 22 7 ⟨57, -24, 24, 7, 50, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-24, 43, 7, -24, 50, by decide⟩, -- source row 602
  idEntry 23 3 ⟨-9, -12, 4, -3, 20, by decide⟩, -- source row 624
  idEntry 23 4 ⟨-12, 9, -3, -4, 20, by decide⟩, -- source row 625
  idEntry 24 0 ⟨3, 4, 4, -3, 20, by decide⟩, -- source row 648
  idEntry 24 1 ⟨3, 4, 4, -3, 20, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-9, -12, -12, 9, 20, by decide⟩, -- source row 650
  idEntry 24 3 ⟨9, 12, -4, 3, 20, by decide⟩, -- source row 651
  idEntry 24 4 ⟨12, -9, 3, 4, 20, by decide⟩, -- source row 652
  idEntry 24 7 ⟨-9, -12, -12, 9, 25, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-12, -16, -16, 12, 25, by decide⟩, -- source row 656
  idEntry 25 0 ⟨3, 4, 0, 0, 10, by decide⟩, -- source row 675
  idEntry 25 1 ⟨3, 4, 0, 0, 10, by decide⟩, -- source row 676
  idEntry 25 2 ⟨-9, -12, 0, 0, 10, by decide⟩, -- source row 677
  idEntry 25 3 ⟨-9, -12, -4, 3, 20, by decide⟩, -- source row 678
  idEntry 25 4 ⟨-12, 9, 3, 4, 20, by decide⟩, -- source row 679
  idEntry 25 7 ⟨9, 12, 12, 16, 25, by decide⟩, -- source row 682
  idEntry 25 8 ⟨12, 16, -9, -12, 25, by decide⟩, -- source row 683
  idEntry 26 3 ⟨0, 0, 4, -3, 10, by decide⟩, -- source row 705
  idEntry 26 4 ⟨0, 0, -3, -4, 10, by decide⟩, -- source row 706
  idEntry 30 0 ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 810
  idEntry 30 1 ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-405, -1056, 352, -135, 1508, by decide⟩, -- source row 812
  idEntry 30 5 ⟨-6105, -12928, 0, 0, 28594, by decide⟩, -- source row 815
  idEntry 30 6 ⟨12928, -6105, 0, 0, 28594, by decide⟩, -- source row 816
  idEntry 30 7 ⟨1003, -1596, -1596, -1003, 7540, by decide⟩, -- source row 817
  idEntry 30 8 ⟨-1596, -1003, -1003, 1596, 7540, by decide⟩, -- source row 818
  idEntry 30 9 ⟨-2025, -5280, 1760, -675, 6409, by decide⟩, -- source row 819
  idEntry 30 10 ⟨3240, 8448, -2816, 1080, 19227, by decide⟩, -- source row 820
  idEntry 31 0 ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 837
  idEntry 31 1 ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-405, -1056, -352, 135, 1508, by decide⟩, -- source row 839
  idEntry 31 5 ⟨-6105, -12928, 0, 0, 28594, by decide⟩, -- source row 842
  idEntry 31 6 ⟨12928, -6105, 0, 0, 28594, by decide⟩, -- source row 843
  idEntry 31 7 ⟨-1003, 1596, 0, 0, 3770, by decide⟩, -- source row 844
  idEntry 31 8 ⟨1596, 1003, 0, 0, 3770, by decide⟩, -- source row 845
  idEntry 31 9 ⟨4841, 4200, 2840, 2141, 12818, by decide⟩, -- source row 846
  idEntry 31 10 ⟨12600, -14523, 3259, 16920, 38454, by decide⟩, -- source row 847
  idEntry 32 5 ⟨-6105, -12928, 0, 0, 28594, by decide⟩, -- source row 869
  idEntry 32 6 ⟨12928, -6105, 0, 0, 28594, by decide⟩, -- source row 870
  idEntry 32 7 ⟨1003, -1596, 1596, 1003, 7540, by decide⟩, -- source row 871
  idEntry 32 8 ⟨-1596, -1003, 1003, -1596, 7540, by decide⟩, -- source row 872
  idEntry 33 0 ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 891
  idEntry 33 1 ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 892
  idEntry 33 2 ⟨0, 0, -352, 135, 754, by decide⟩, -- source row 893
  idEntry 33 5 ⟨6105, 12928, 12928, -6105, 57188, by decide⟩, -- source row 896
  idEntry 33 6 ⟨-12928, 6105, 6105, 12928, 57188, by decide⟩, -- source row 897
  idEntry 33 7 ⟨-1003, 1596, 0, 0, 3770, by decide⟩, -- source row 898
  idEntry 33 8 ⟨1596, 1003, 0, 0, 3770, by decide⟩, -- source row 899
  idEntry 33 9 ⟨0, 0, -3520, 1350, 6409, by decide⟩, -- source row 900
  idEntry 33 10 ⟨0, 0, 5632, -2160, 19227, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-405, -1056, 352, -135, 4524, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-405, -1056, 352, -135, 4524, by decide⟩, -- source row 919
  idEntry 34 2 ⟨405, 1056, -352, 135, 1508, by decide⟩, -- source row 920
  idEntry 34 5 ⟨6105, 12928, 12928, -6105, 57188, by decide⟩, -- source row 923
  idEntry 34 6 ⟨-12928, 6105, 6105, 12928, 57188, by decide⟩, -- source row 924
  idEntry 34 7 ⟨1003, -1596, 1596, 1003, 7540, by decide⟩, -- source row 925
  idEntry 34 8 ⟨-1596, -1003, 1003, -1596, 7540, by decide⟩, -- source row 926
  idEntry 34 9 ⟨791, -6360, 680, -3491, 12818, by decide⟩, -- source row 927
  idEntry 34 10 ⟨19080, 2373, -8891, -14760, 38454, by decide⟩, -- source row 928
  idEntry 35 5 ⟨6105, 12928, 12928, -6105, 57188, by decide⟩, -- source row 950
  idEntry 35 6 ⟨-12928, 6105, 6105, 12928, 57188, by decide⟩, -- source row 951
  idEntry 35 7 ⟨1003, -1596, -1596, -1003, 7540, by decide⟩, -- source row 952
  idEntry 35 8 ⟨-1596, -1003, -1003, 1596, 7540, by decide⟩, -- source row 953
  idEntry 36 0 ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 973
  idEntry 36 2 ⟨405, 1056, 352, -135, 1508, by decide⟩, -- source row 974
  idEntry 36 5 ⟨6105, 12928, -12928, 6105, 57188, by decide⟩, -- source row 977
  idEntry 36 6 ⟨-12928, 6105, -6105, -12928, 57188, by decide⟩, -- source row 978
  idEntry 36 7 ⟨1003, -1596, 1596, 1003, 7540, by decide⟩, -- source row 979
  idEntry 36 8 ⟨-1596, -1003, 1003, -1596, 7540, by decide⟩, -- source row 980
  idEntry 36 9 ⟨2025, 5280, 1760, -675, 6409, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-3240, -8448, -2816, 1080, 19227, by decide⟩, -- source row 982
  idEntry 37 0 ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 999
  idEntry 37 1 ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨0, 0, 352, -135, 754, by decide⟩, -- source row 1001
  idEntry 37 5 ⟨6105, 12928, -12928, 6105, 57188, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨-12928, 6105, -6105, -12928, 57188, by decide⟩, -- source row 1005
  idEntry 37 7 ⟨1003, -1596, -1596, -1003, 7540, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨-1596, -1003, -1003, 1596, 7540, by decide⟩, -- source row 1007
  idEntry 37 9 ⟨-2816, 1080, -1760, 675, 6409, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-15840, 6075, 2816, -1080, 19227, by decide⟩, -- source row 1009
  idEntry 38 5 ⟨6105, 12928, -12928, 6105, 57188, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨-12928, 6105, -6105, -12928, 57188, by decide⟩, -- source row 1032
  idEntry 38 7 ⟨-1003, 1596, 0, 0, 3770, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨1596, 1003, 0, 0, 3770, by decide⟩, -- source row 1034
  sumEntry 0 5 ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨16, 63, -63, 16, 780, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨0, 0, -63, 16, 1170, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨63, -16, -16, -63, 390, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨-48, -189, -63, 16, 1170, by decide⟩, -- source row 1118
  sumEntry 1 7 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1126
  sumEntry 1 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1127
  sumEntry 1 9 ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1128
  sumEntry 1 10 ⟨-16, -63, 63, -16, 780, by decide⟩, -- source row 1129
  sumEntry 1 15 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1134
  sumEntry 1 16 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1135
  sumEntry 1 17 ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1136
  sumEntry 1 18 ⟨-16, -63, 0, 0, 390, by decide⟩, -- source row 1137
  sumEntry 1 23 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1142
  sumEntry 1 24 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1143
  sumEntry 1 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1144
  sumEntry 1 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1145
  sumEntry 2 7 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1153
  sumEntry 2 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1154
  sumEntry 2 9 ⟨-63, 16, 0, 0, 390, by decide⟩, -- source row 1155
  sumEntry 2 10 ⟨16, 63, 0, 0, 390, by decide⟩, -- source row 1156
  sumEntry 2 15 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1161
  sumEntry 2 16 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1162
  sumEntry 2 17 ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1163
  sumEntry 2 18 ⟨-16, -63, 0, 0, 390, by decide⟩, -- source row 1164
  sumEntry 2 23 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1169
  sumEntry 2 24 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1170
  sumEntry 2 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1171
  sumEntry 2 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1172
  sumEntry 3 7 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1180
  sumEntry 3 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1181
  sumEntry 3 9 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1182
  sumEntry 3 10 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1183
  sumEntry 3 15 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1188
  sumEntry 3 16 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1189
  sumEntry 3 17 ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1190
  sumEntry 3 18 ⟨-16, -63, 0, 0, 390, by decide⟩, -- source row 1191
  sumEntry 3 23 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1196
  sumEntry 3 24 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1197
  sumEntry 3 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1198
  sumEntry 3 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1199
  sumEntry 4 0 ⟨63, -16, 16, 63, 2340, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨63, -16, -80, -315, 2340, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨-63, 16, -16, -63, 1170, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-189, 48, 16, 63, 780, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨-48, -189, -63, 16, 2340, by decide⟩, -- source row 1206
  sumEntry 4 15 ⟨-63, 16, 16, 63, 390, by decide⟩, -- source row 1215
  sumEntry 4 16 ⟨-48, -189, -63, 16, 1170, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨0, 0, -16, -63, 1170, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨-189, 48, 16, 63, 2340, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨189, -48, 16, 63, 2340, by decide⟩, -- source row 1229
  sumEntry 5 5 ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1232
  sumEntry 5 6 ⟨0, 0, -63, 16, 1170, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨144, 567, 315, -80, 2340, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨-63, 16, -16, -63, 390, by decide⟩, -- source row 1252
  sumEntry 6 1 ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 1255
  sumEntry 6 5 ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨-48, -189, -63, 16, 2340, by decide⟩, -- source row 1260
  sumEntry 6 15 ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1269
  sumEntry 6 16 ⟨48, 189, 63, -16, 2340, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨-63, 16, -16, -63, 390, by decide⟩, -- source row 1279
  sumEntry 7 3 ⟨-9, -12, 4, -3, 60, by decide⟩, -- source row 1284
  sumEntry 7 4 ⟨-12, 9, -3, -4, 60, by decide⟩, -- source row 1285
  sumEntry 7 13 ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1294
  sumEntry 7 14 ⟨0, 0, 5, -12, 78, by decide⟩, -- source row 1295
  sumEntry 7 25 ⟨189, -48, -16, -63, 780, by decide⟩, -- source row 1306
  sumEntry 7 26 ⟨-48, -189, -63, 16, 780, by decide⟩, -- source row 1307
  sumEntry 8 3 ⟨0, 0, 4, -3, 30, by decide⟩, -- source row 1311
  sumEntry 8 4 ⟨0, 0, -3, -4, 30, by decide⟩, -- source row 1312
  sumEntry 8 13 ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1321
  sumEntry 8 14 ⟨-36, -15, 5, -12, 156, by decide⟩, -- source row 1322
  sumEntry 8 25 ⟨0, 0, -16, -63, 390, by decide⟩, -- source row 1333
  sumEntry 8 26 ⟨0, 0, -63, 16, 390, by decide⟩, -- source row 1334
  sumEntry 10 5 ⟨-6105, -12928, 0, 0, 85782, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨12928, -6105, 0, 0, 85782, by decide⟩, -- source row 1368
  sumEntry 10 7 ⟨1003, -1596, 1596, 1003, 22620, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨-1596, -1003, 1003, -1596, 22620, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨1073, 264, 0, 0, 6630, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨264, -1073, 0, 0, 6630, by decide⟩, -- source row 1374
  sumEntry 10 17 ⟨-21, 20, 20, 21, 348, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨-20, -21, -21, 20, 348, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨-155, 468, -468, -155, 5916, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨-468, -155, 155, -468, 5916, by decide⟩, -- source row 1382
  sumEntry 10 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1387
  sumEntry 10 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1388
  sumEntry 11 5 ⟨6105, 12928, 12928, -6105, 171564, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨-12928, 6105, 6105, 12928, 171564, by decide⟩, -- source row 1395
  sumEntry 11 7 ⟨1003, -1596, -1596, -1003, 22620, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨-1596, -1003, -1003, 1596, 22620, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨1073, 264, 0, 0, 6630, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨264, -1073, 0, 0, 6630, by decide⟩, -- source row 1401
  sumEntry 11 17 ⟨21, -20, 0, 0, 174, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨20, 21, 0, 0, 174, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨-155, 468, 468, 155, 5916, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨-468, -155, -155, 468, 5916, by decide⟩, -- source row 1409
  sumEntry 11 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1414
  sumEntry 11 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1415
  sumEntry 12 5 ⟨6105, 12928, -12928, 6105, 171564, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨-12928, 6105, -6105, -12928, 171564, by decide⟩, -- source row 1422
  sumEntry 12 7 ⟨-1003, 1596, 0, 0, 11310, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨1596, 1003, 0, 0, 11310, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨1073, 264, 0, 0, 6630, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨264, -1073, 0, 0, 6630, by decide⟩, -- source row 1428
  sumEntry 12 17 ⟨-21, 20, -20, -21, 348, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨-20, -21, 21, -20, 348, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨155, -468, 0, 0, 2958, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨468, 155, 0, 0, 2958, by decide⟩, -- source row 1436
  sumEntry 12 25 ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1441
  sumEntry 12 26 ⟨-16, -63, -63, 16, 780, by decide⟩, -- source row 1442
  pairEntry 0 13 (by decide) ⟨-189, 48, -16, -63, 780, by decide⟩, -- source row 1455
  pairEntry 0 14 (by decide) ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-63, 16, 16, 63, 390, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨63, -16, 16, 63, 390, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨-63, 16, 0, 0, 390, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1535
  pairEntry 3 21 (by decide) ⟨9, 12, -4, 3, 60, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1575
  pairEntry 3 30 (by decide) ⟨-10967, -68496, -7656, 31117, 384540, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-52159, -45732, 30420, 10075, 384540, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨-20596, 11382, -19038, 10521, 192270, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨-52159, -45732, -30420, -10075, 384540, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨-10298, 5691, 5691, 10298, 96135, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨-20596, 11382, 0, 0, 96135, by decide⟩, -- source row 1587
  pairEntry 4 21 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨-9, -12, 4, -3, 60, by decide⟩, -- source row 1609
  pairEntry 4 30 (by decide) ⟨20596, -11382, -19038, 10521, 192270, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨-10967, -68496, -7656, 31117, 384540, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨10967, 68496, -7656, 31117, 384540, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨-20596, 11382, -19038, 10521, 192270, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨10298, -5691, 5691, 10298, 96135, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨-10298, 5691, 5691, 10298, 96135, by decide⟩, -- source row 1621
  pairEntry 6 21 (by decide) ⟨9, 12, -4, 3, 60, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1674
  pairEntry 6 30 (by decide) ⟨-10298, 5691, -5691, -10298, 96135, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨10298, -5691, -5691, -10298, 96135, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨-20596, 11382, 19038, -10521, 192270, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨10967, 68496, 7656, -31117, 384540, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨-10967, -68496, 7656, -31117, 384540, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨20596, -11382, 19038, -10521, 192270, by decide⟩, -- source row 1686
  pairEntry 7 21 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨-9, -12, 4, -3, 60, by decide⟩, -- source row 1705
  pairEntry 7 30 (by decide) ⟨-20596, 11382, 0, 0, 96135, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨-10298, 5691, -5691, -10298, 96135, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨-52159, -45732, 30420, 10075, 384540, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨-20596, 11382, 19038, -10521, 192270, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨-52159, -45732, -30420, -10075, 384540, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨-10967, -68496, 7656, -31117, 384540, by decide⟩, -- source row 1717
  pairEntry 9 21 (by decide) ⟨9, 12, -4, 3, 60, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1764
  pairEntry 9 30 (by decide) ⟨52159, 45732, 30420, 10075, 384540, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨10967, 68496, -7656, 31117, 384540, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨20596, -11382, 0, 0, 96135, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨10298, -5691, 5691, 10298, 96135, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨52159, 45732, -30420, -10075, 384540, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨20596, -11382, -19038, 10521, 192270, by decide⟩, -- source row 1776
  pairEntry 10 21 (by decide) ⟨0, 0, -4, 3, 30, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨-9, -12, -4, 3, 60, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨-9, -12, 4, -3, 60, by decide⟩, -- source row 1792
  pairEntry 10 30 (by decide) ⟨20596, -11382, 19038, -10521, 192270, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨52159, 45732, 30420, 10075, 384540, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨10298, -5691, -5691, -10298, 96135, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨20596, -11382, 0, 0, 96135, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨10967, 68496, 7656, -31117, 384540, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨52159, 45732, -30420, -10075, 384540, by decide⟩, -- source row 1804
  pairEntry 12 15 (by decide) ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨63, -16, 16, 63, 780, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨-63, 16, 16, 63, 780, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨63, -16, -16, -63, 780, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨63, -16, 0, 0, 390, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨-63, 16, -16, -63, 390, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨-63, 16, -16, -63, 390, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨-189, 48, -16, -63, 780, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨-63, 16, -16, -63, 780, by decide⟩, -- source row 1953
  pairEntry 21 30 (by decide) ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨-405, -1056, 352, -135, 4524, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨-405, -1056, 352, -135, 4524, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 2062
  pairEntry 24 30 (by decide) ⟨-405, -1056, 352, -135, 4524, by decide⟩, -- source row 2084
  pairEntry 24 31 (by decide) ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 2085
  pairEntry 24 33 (by decide) ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 2087
  pairEntry 24 34 (by decide) ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 2088
  pairEntry 24 36 (by decide) ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 2090
  pairEntry 24 37 (by decide) ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨-405, -1056, -352, 135, 4524, by decide⟩, -- source row 2097
  pairEntry 25 31 (by decide) ⟨0, 0, -352, 135, 2262, by decide⟩, -- source row 2098
  pairEntry 25 33 (by decide) ⟨405, 1056, -352, 135, 4524, by decide⟩, -- source row 2100
  pairEntry 25 34 (by decide) ⟨405, 1056, 352, -135, 4524, by decide⟩, -- source row 2101
  pairEntry 25 36 (by decide) ⟨0, 0, 352, -135, 2262, by decide⟩, -- source row 2103
  pairEntry 25 37 (by decide) ⟨-405, -1056, 352, -135, 4524, by decide⟩ -- source row 2104
]

end Option2.NativeStress.NativeT

module

public import NativeHWeights

@[expose] public section

/-! Exact source λ16; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda16 : List Entry := [
  idEntry 1 0 ⟨-1615, -180, 36, -323, 3900, by decide⟩, -- source row 27
  idEntry 1 1 ⟨1615, 180, -36, 323, 3900, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-1615, -180, 36, -323, 3900, by decide⟩, -- source row 29
  idEntry 1 15 ⟨-323, -36, -36, 323, 1300, by decide⟩, -- source row 42
  idEntry 1 16 ⟨36, -323, -323, -36, 1300, by decide⟩, -- source row 43
  idEntry 3 0 ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 81
  idEntry 3 1 ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-99, -168, 56, -33, 260, by decide⟩, -- source row 83
  idEntry 3 3 ⟨99, 168, -56, 33, 195, by decide⟩, -- source row 84
  idEntry 3 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 86
  idEntry 3 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 87
  idEntry 3 7 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 88
  idEntry 3 8 ⟨-36, 323, 323, 36, 1300, by decide⟩, -- source row 89
  idEntry 4 0 ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 108
  idEntry 4 1 ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 109
  idEntry 4 2 ⟨0, 0, 56, -33, 130, by decide⟩, -- source row 110
  idEntry 4 3 ⟨0, 0, 56, -33, 195, by decide⟩, -- source row 111
  idEntry 4 4 ⟨56, -33, 0, 0, 65, by decide⟩, -- source row 112
  idEntry 4 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 113
  idEntry 4 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 114
  idEntry 4 7 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 115
  idEntry 4 8 ⟨-36, 323, -323, -36, 1300, by decide⟩, -- source row 116
  idEntry 5 5 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 140
  idEntry 5 6 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 141
  idEntry 5 7 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 142
  idEntry 5 8 ⟨36, -323, 0, 0, 650, by decide⟩, -- source row 143
  idEntry 6 0 ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 163
  idEntry 6 2 ⟨99, 168, 56, -33, 260, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-99, -168, -56, 33, 195, by decide⟩, -- source row 165
  idEntry 6 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 167
  idEntry 6 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 168
  idEntry 6 7 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 169
  idEntry 6 8 ⟨-36, 323, -323, -36, 1300, by decide⟩, -- source row 170
  idEntry 7 0 ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 190
  idEntry 7 2 ⟨99, 168, -56, 33, 260, by decide⟩, -- source row 191
  idEntry 7 3 ⟨99, 168, -56, 33, 390, by decide⟩, -- source row 192
  idEntry 7 4 ⟨-56, 33, 33, 56, 130, by decide⟩, -- source row 193
  idEntry 7 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 194
  idEntry 7 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 195
  idEntry 7 7 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 196
  idEntry 7 8 ⟨36, -323, 0, 0, 650, by decide⟩, -- source row 197
  idEntry 8 5 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 221
  idEntry 8 6 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 222
  idEntry 8 7 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 223
  idEntry 8 8 ⟨-36, 323, 323, 36, 1300, by decide⟩, -- source row 224
  idEntry 9 0 ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 243
  idEntry 9 1 ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, -56, 33, 130, by decide⟩, -- source row 245
  idEntry 9 3 ⟨0, 0, 112, -66, 195, by decide⟩, -- source row 246
  idEntry 9 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 248
  idEntry 9 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 249
  idEntry 9 7 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 250
  idEntry 9 8 ⟨36, -323, 0, 0, 650, by decide⟩, -- source row 251
  idEntry 10 0 ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 270
  idEntry 10 1 ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-99, -168, -56, 33, 260, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-99, -168, -56, 33, 390, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-56, 33, -33, -56, 130, by decide⟩, -- source row 274
  idEntry 10 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 275
  idEntry 10 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 276
  idEntry 10 7 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 277
  idEntry 10 8 ⟨-36, 323, 323, 36, 1300, by decide⟩, -- source row 278
  idEntry 11 5 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 302
  idEntry 11 6 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 303
  idEntry 11 7 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 304
  idEntry 11 8 ⟨-36, 323, -323, -36, 1300, by decide⟩, -- source row 305
  idEntry 12 0 ⟨-1292, -144, -108, 969, 5850, by decide⟩, -- source row 324
  idEntry 12 1 ⟨323, 36, 108, -969, 11700, by decide⟩, -- source row 325
  idEntry 12 5 ⟨1292, 144, 108, -969, 5850, by decide⟩, -- source row 329
  idEntry 12 6 ⟨0, 0, -323, -36, 1950, by decide⟩, -- source row 330
  idEntry 13 0 ⟨-1615, -180, 108, -969, 11700, by decide⟩, -- source row 351
  idEntry 13 1 ⟨646, 72, -108, 969, 5850, by decide⟩, -- source row 352
  idEntry 13 2 ⟨0, 0, 36, -323, 1950, by decide⟩, -- source row 353
  idEntry 13 5 ⟨-2584, -288, -108, 969, 5850, by decide⟩, -- source row 356
  idEntry 13 6 ⟨0, 0, -323, -36, 5850, by decide⟩, -- source row 357
  idEntry 14 0 ⟨323, 36, 0, 0, 1170, by decide⟩, -- source row 378
  idEntry 14 1 ⟨-646, -72, 0, 0, 2925, by decide⟩, -- source row 379
  idEntry 14 2 ⟨969, 108, 36, -323, 3900, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-646, -72, -108, 969, 5850, by decide⟩, -- source row 383
  idEntry 14 6 ⟨0, 0, 323, 36, 5850, by decide⟩, -- source row 384
  idEntry 15 0 ⟨-969, -108, 144, -1292, 5850, by decide⟩, -- source row 405
  idEntry 15 1 ⟨969, 108, -36, 323, 11700, by decide⟩, -- source row 406
  idEntry 15 5 ⟨969, 108, -144, 1292, 5850, by decide⟩, -- source row 410
  idEntry 15 6 ⟨-72, 646, 323, 36, 650, by decide⟩, -- source row 411
  idEntry 16 0 ⟨2907, 324, -36, 323, 11700, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-2907, -324, -36, 323, 11700, by decide⟩, -- source row 433
  idEntry 16 2 ⟨2907, 324, -252, 2261, 3900, by decide⟩, -- source row 434
  idEntry 16 5 ⟨0, 0, 36, -323, 1170, by decide⟩, -- source row 437
  idEntry 16 6 ⟨-180, 1615, 646, 72, 1950, by decide⟩, -- source row 438
  idEntry 17 0 ⟨-1938, -216, 36, -323, 5850, by decide⟩, -- source row 459
  idEntry 17 1 ⟨-969, -108, 396, -3553, 11700, by decide⟩, -- source row 460
  idEntry 17 2 ⟨0, 0, -36, 323, 1950, by decide⟩, -- source row 461
  idEntry 17 5 ⟨-3876, -432, 396, -3553, 5850, by decide⟩, -- source row 464
  idEntry 17 6 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 465
  idEntry 18 0 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 486
  idEntry 18 1 ⟨-323, -36, 0, 0, 975, by decide⟩, -- source row 487
  idEntry 18 2 ⟨323, 36, 36, -323, 3900, by decide⟩, -- source row 488
  idEntry 18 5 ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 491
  idEntry 18 6 ⟨108, -969, -323, -36, 3900, by decide⟩, -- source row 492
  idEntry 19 0 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 513
  idEntry 19 1 ⟨323, 36, 108, -969, 3900, by decide⟩, -- source row 514
  idEntry 19 2 ⟨323, 36, -108, 969, 3900, by decide⟩, -- source row 515
  idEntry 19 5 ⟨-323, -36, 36, -323, 1300, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-108, 969, 323, 36, 3900, by decide⟩, -- source row 519
  idEntry 20 0 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 540
  idEntry 20 1 ⟨323, 36, -108, 969, 3900, by decide⟩, -- source row 541
  idEntry 20 2 ⟨646, 72, 36, -323, 1950, by decide⟩, -- source row 542
  idEntry 20 5 ⟨-969, -108, -36, 323, 3900, by decide⟩, -- source row 545
  idEntry 20 6 ⟨-36, 323, -323, -36, 1300, by decide⟩, -- source row 546
  idEntry 21 0 ⟨-13, 84, -84, -13, 340, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-13, 84, -84, -13, 340, by decide⟩, -- source row 568
  idEntry 21 2 ⟨39, -252, 252, 39, 340, by decide⟩, -- source row 569
  idEntry 21 7 ⟨39, -252, 252, 39, 425, by decide⟩, -- source row 574
  idEntry 21 8 ⟨52, -336, 336, 52, 425, by decide⟩, -- source row 575
  idEntry 21 9 ⟨9, -12, -4, -3, 20, by decide⟩, -- source row 576
  idEntry 21 10 ⟨12, 9, 3, -4, 20, by decide⟩, -- source row 577
  idEntry 22 0 ⟨-13, 84, 0, 0, 170, by decide⟩, -- source row 594
  idEntry 22 1 ⟨-13, 84, 0, 0, 170, by decide⟩, -- source row 595
  idEntry 22 2 ⟨39, -252, 0, 0, 170, by decide⟩, -- source row 596
  idEntry 22 7 ⟨-39, 252, -52, 336, 425, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-52, 336, 39, -252, 425, by decide⟩, -- source row 602
  idEntry 22 9 ⟨-9, 12, -4, -3, 20, by decide⟩, -- source row 603
  idEntry 22 10 ⟨-12, -9, 3, -4, 20, by decide⟩, -- source row 604
  idEntry 23 9 ⟨0, 0, 4, 3, 10, by decide⟩, -- source row 630
  idEntry 23 10 ⟨0, 0, -3, 4, 10, by decide⟩, -- source row 631
  idEntry 24 0 ⟨13, -84, -84, -13, 340, by decide⟩, -- source row 648
  idEntry 24 1 ⟨13, -84, -84, -13, 340, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-39, 252, 252, 39, 340, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-39, 252, 252, 39, 425, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-52, 336, 336, 52, 425, by decide⟩, -- source row 656
  idEntry 24 9 ⟨9, -12, 4, 3, 20, by decide⟩, -- source row 657
  idEntry 24 10 ⟨12, 9, -3, 4, 20, by decide⟩, -- source row 658
  idEntry 25 0 ⟨-13, 84, -84, -13, 340, by decide⟩, -- source row 675
  idEntry 25 1 ⟨-13, 84, -84, -13, 340, by decide⟩, -- source row 676
  idEntry 25 2 ⟨39, -252, 252, 39, 340, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-1047, 96, -304, 297, 850, by decide⟩, -- source row 682
  idEntry 25 8 ⟨704, 453, -297, -304, 850, by decide⟩, -- source row 683
  idEntry 25 9 ⟨0, 0, -4, -3, 10, by decide⟩, -- source row 684
  idEntry 25 10 ⟨0, 0, 3, -4, 10, by decide⟩, -- source row 685
  idEntry 26 9 ⟨-9, 12, 4, 3, 20, by decide⟩, -- source row 711
  idEntry 26 10 ⟨-12, -9, -3, 4, 20, by decide⟩, -- source row 712
  idEntry 30 0 ⟨0, 0, -151962, -45709, 480675, by decide⟩, -- source row 810
  idEntry 30 1 ⟨0, 0, -151962, -45709, 480675, by decide⟩, -- source row 811
  idEntry 30 2 ⟨0, 0, 151962, 45709, 160225, by decide⟩, -- source row 812
  idEntry 30 3 ⟨-66913, 145584, 145584, 66913, 640900, by decide⟩, -- source row 813
  idEntry 30 4 ⟨-145584, -66913, -66913, 145584, 640900, by decide⟩, -- source row 814
  idEntry 30 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 817
  idEntry 30 8 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 818
  idEntry 30 9 ⟨0, 0, 607848, 182836, 544765, by decide⟩, -- source row 819
  idEntry 30 10 ⟨0, 0, -4862784, -1462688, 8171475, by decide⟩, -- source row 820
  idEntry 31 0 ⟨63612, 19134, -151962, -45709, 961350, by decide⟩, -- source row 837
  idEntry 31 1 ⟨63612, 19134, -151962, -45709, 961350, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-63612, -19134, 151962, 45709, 320450, by decide⟩, -- source row 839
  idEntry 31 3 ⟨-66913, 145584, -145584, -66913, 640900, by decide⟩, -- source row 840
  idEntry 31 4 ⟨-145584, -66913, 66913, -145584, 640900, by decide⟩, -- source row 841
  idEntry 31 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 844
  idEntry 31 8 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 845
  idEntry 31 9 ⟨-897636, -270002, -590178, -177521, 2723825, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-7347186, -2209977, 2169876, 652682, 8171475, by decide⟩, -- source row 847
  idEntry 32 3 ⟨66913, -145584, 0, 0, 320450, by decide⟩, -- source row 867
  idEntry 32 4 ⟨145584, 66913, 0, 0, 320450, by decide⟩, -- source row 868
  idEntry 32 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 871
  idEntry 32 8 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 872
  idEntry 33 0 ⟨-200739, 436752, -171096, 17903, 1922700, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-200739, 436752, -171096, 17903, 1922700, by decide⟩, -- source row 892
  idEntry 33 2 ⟨200739, -436752, 171096, -17903, 640900, by decide⟩, -- source row 893
  idEntry 33 3 ⟨66913, -145584, 0, 0, 320450, by decide⟩, -- source row 894
  idEntry 33 4 ⟨145584, 66913, 0, 0, 320450, by decide⟩, -- source row 895
  idEntry 33 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 898
  idEntry 33 8 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 899
  idEntry 33 9 ⟨200739, -436752, 171096, -17903, 544765, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-1605912, 3494016, -1368768, 143224, 8171475, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-137127, 455886, -151962, -45709, 961350, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-137127, 455886, -151962, -45709, 961350, by decide⟩, -- source row 919
  idEntry 34 2 ⟨137127, -455886, 151962, 45709, 320450, by decide⟩, -- source row 920
  idEntry 34 3 ⟨-66913, 145584, 145584, 66913, 640900, by decide⟩, -- source row 921
  idEntry 34 4 ⟨-145584, -66913, -66913, 145584, 640900, by decide⟩, -- source row 922
  idEntry 34 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 925
  idEntry 34 8 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 926
  idEntry 34 9 ⟨-1901331, 1913758, -1125482, 987151, 2723825, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-5741274, -5703993, -841209, 7203962, 8171475, by decide⟩, -- source row 928
  idEntry 35 3 ⟨-66913, 145584, -145584, -66913, 640900, by decide⟩, -- source row 948
  idEntry 35 4 ⟨-145584, -66913, 66913, -145584, 640900, by decide⟩, -- source row 949
  idEntry 35 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 952
  idEntry 35 8 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 953
  idEntry 36 0 ⟨200739, -436752, -171096, 17903, 1922700, by decide⟩, -- source row 972
  idEntry 36 1 ⟨200739, -436752, -171096, 17903, 1922700, by decide⟩, -- source row 973
  idEntry 36 2 ⟨-200739, 436752, 171096, -17903, 640900, by decide⟩, -- source row 974
  idEntry 36 3 ⟨-66913, 145584, -145584, -66913, 640900, by decide⟩, -- source row 975
  idEntry 36 4 ⟨-145584, -66913, 66913, -145584, 640900, by decide⟩, -- source row 976
  idEntry 36 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 979
  idEntry 36 8 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 980
  idEntry 36 9 ⟨-200739, 436752, 171096, -17903, 544765, by decide⟩, -- source row 981
  idEntry 36 10 ⟨1605912, -3494016, -1368768, 143224, 8171475, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-73515, 475020, 132828, 109321, 1922700, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-73515, 475020, 132828, 109321, 1922700, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨73515, -475020, -132828, -109321, 640900, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨66913, -145584, 0, 0, 320450, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨145584, 66913, 0, 0, 320450, by decide⟩, -- source row 1003
  idEntry 37 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 1007
  idEntry 37 9 ⟨695049, 3249668, 468100, 1813325, 5447650, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨6565380, 1119285, -2165349, 6250732, 16342950, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨-66913, 145584, 145584, 66913, 640900, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨-145584, -66913, -66913, 145584, 640900, by decide⟩, -- source row 1030
  idEntry 38 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 1034
  sumEntry 0 5 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨108, -969, -323, -36, 11700, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨-108, 969, 1615, 180, 11700, by decide⟩, -- source row 1118
  sumEntry 1 5 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1125
  sumEntry 1 7 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1126
  sumEntry 1 8 ⟨36, -323, 0, 0, 1950, by decide⟩, -- source row 1127
  sumEntry 1 13 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1133
  sumEntry 1 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1134
  sumEntry 1 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1135
  sumEntry 1 21 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1141
  sumEntry 1 23 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1142
  sumEntry 1 24 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1143
  sumEntry 2 5 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1152
  sumEntry 2 7 ⟨323, 36, 36, -323, 3900, by decide⟩, -- source row 1153
  sumEntry 2 8 ⟨-36, 323, 323, 36, 3900, by decide⟩, -- source row 1154
  sumEntry 2 13 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1160
  sumEntry 2 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1161
  sumEntry 2 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1162
  sumEntry 2 21 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1168
  sumEntry 2 23 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1169
  sumEntry 2 24 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1170
  sumEntry 3 5 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1179
  sumEntry 3 7 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1180
  sumEntry 3 8 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1181
  sumEntry 3 13 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1187
  sumEntry 3 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1188
  sumEntry 3 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1189
  sumEntry 3 21 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1195
  sumEntry 3 23 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1196
  sumEntry 3 24 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1197
  sumEntry 4 0 ⟨323, 36, 0, 0, 5850, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨-323, -36, 108, -969, 11700, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨-323, -36, 108, -969, 11700, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨0, 0, -323, -36, 5850, by decide⟩, -- source row 1206
  sumEntry 4 15 ⟨-323, -36, -36, 323, 1950, by decide⟩, -- source row 1215
  sumEntry 4 16 ⟨0, 0, -323, -36, 2925, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨-969, -108, 36, -323, 11700, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨969, 108, -36, 323, 5850, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨-969, -108, 36, -323, 11700, by decide⟩, -- source row 1229
  sumEntry 5 5 ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1232
  sumEntry 5 6 ⟨-108, 969, 323, 36, 2340, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨-1615, -180, 36, -323, 3900, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨108, -969, -323, -36, 2340, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨323, 36, -36, 323, 1950, by decide⟩, -- source row 1252
  sumEntry 6 0 ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1254
  sumEntry 6 1 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1255
  sumEntry 6 5 ⟨-969, -108, 36, -323, 3900, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨108, -969, 323, 36, 11700, by decide⟩, -- source row 1260
  sumEntry 6 15 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1269
  sumEntry 6 16 ⟨108, -969, -646, -72, 5850, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨323, 36, -36, 323, 1950, by decide⟩, -- source row 1279
  sumEntry 7 9 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 1290
  sumEntry 7 10 ⟨0, 0, -3, 4, 30, by decide⟩, -- source row 1291
  sumEntry 7 15 ⟨-969, -108, -36, 323, 3900, by decide⟩, -- source row 1296
  sumEntry 7 16 ⟨108, -969, -323, -36, 3900, by decide⟩, -- source row 1297
  sumEntry 7 19 ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1300
  sumEntry 7 20 ⟨168, -99, 33, 56, 780, by decide⟩, -- source row 1301
  sumEntry 8 9 ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 1317
  sumEntry 8 10 ⟨-12, -9, -3, 4, 60, by decide⟩, -- source row 1318
  sumEntry 8 15 ⟨0, 0, -36, 323, 1950, by decide⟩, -- source row 1323
  sumEntry 8 16 ⟨0, 0, -323, -36, 1950, by decide⟩, -- source row 1324
  sumEntry 8 19 ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1327
  sumEntry 8 20 ⟨168, -99, -33, -56, 780, by decide⟩, -- source row 1328
  sumEntry 10 3 ⟨66913, -145584, 0, 0, 961350, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨145584, 66913, 0, 0, 961350, by decide⟩, -- source row 1366
  sumEntry 10 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨21, 20, -20, 21, 348, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨20, -21, 21, 20, 348, by decide⟩, -- source row 1374
  sumEntry 10 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1378
  sumEntry 10 21 ⟨-5133, 2044, -2044, -5133, 66300, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨2044, 5133, -5133, 2044, 66300, by decide⟩, -- source row 1384
  sumEntry 10 25 ⟨475, 132, 0, 0, 2958, by decide⟩, -- source row 1387
  sumEntry 10 26 ⟨132, -475, 0, 0, 2958, by decide⟩, -- source row 1388
  sumEntry 11 3 ⟨-66913, 145584, -145584, -66913, 1922700, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨-145584, -66913, 66913, -145584, 1922700, by decide⟩, -- source row 1393
  sumEntry 11 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨-21, -20, 0, 0, 174, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨-20, 21, 0, 0, 174, by decide⟩, -- source row 1401
  sumEntry 11 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1405
  sumEntry 11 21 ⟨-5133, 2044, -2044, -5133, 66300, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨2044, 5133, -5133, 2044, 66300, by decide⟩, -- source row 1411
  sumEntry 11 25 ⟨-475, -132, -132, 475, 5916, by decide⟩, -- source row 1414
  sumEntry 11 26 ⟨-132, 475, 475, 132, 5916, by decide⟩, -- source row 1415
  sumEntry 12 3 ⟨-66913, 145584, 145584, 66913, 1922700, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨-145584, -66913, -66913, 145584, 1922700, by decide⟩, -- source row 1420
  sumEntry 12 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨21, 20, 20, -21, 348, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨20, -21, -21, -20, 348, by decide⟩, -- source row 1428
  sumEntry 12 15 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1432
  sumEntry 12 21 ⟨-5133, 2044, -2044, -5133, 66300, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨2044, 5133, -5133, 2044, 66300, by decide⟩, -- source row 1438
  sumEntry 12 25 ⟨-475, -132, 132, -475, 5916, by decide⟩, -- source row 1441
  sumEntry 12 26 ⟨-132, 475, -475, -132, 5916, by decide⟩, -- source row 1442
  pairEntry 0 13 (by decide) ⟨-969, -108, 36, -323, 3900, by decide⟩, -- source row 1455
  pairEntry 0 14 (by decide) ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨-323, -36, 0, 0, 975, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨-323, -36, 36, -323, 1950, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨-1615, -180, 36, -323, 3900, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1535
  pairEntry 3 21 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1575
  pairEntry 3 30 (by decide) ⟨-298963, -75416, 145584, 66913, 1922700, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-249851, 180668, 110500, -116025, 1922700, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨249851, -180668, 110500, -116025, 1922700, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨298963, 75416, 145584, 66913, 1922700, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨12278, 64021, -64021, 12278, 480675, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨-12278, -64021, -64021, 12278, 480675, by decide⟩, -- source row 1587
  pairEntry 4 21 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1609
  pairEntry 4 30 (by decide) ⟨-24556, -128042, 17542, 91469, 961350, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨-298963, -75416, 145584, 66913, 1922700, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨-24556, -128042, -17542, -91469, 961350, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨249851, -180668, 110500, -116025, 1922700, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨24556, 128042, 0, 0, 480675, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨12278, 64021, -64021, 12278, 480675, by decide⟩, -- source row 1621
  pairEntry 6 21 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1674
  pairEntry 6 30 (by decide) ⟨12278, 64021, 64021, -12278, 480675, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨24556, 128042, 0, 0, 480675, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨249851, -180668, -110500, 116025, 1922700, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨-24556, -128042, 17542, 91469, 961350, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨-298963, -75416, -145584, -66913, 1922700, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨-24556, -128042, -17542, -91469, 961350, by decide⟩, -- source row 1686
  pairEntry 7 21 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1705
  pairEntry 7 30 (by decide) ⟨-12278, -64021, 64021, -12278, 480675, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨12278, 64021, 64021, -12278, 480675, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨298963, 75416, -145584, -66913, 1922700, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨249851, -180668, -110500, 116025, 1922700, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨-249851, 180668, -110500, 116025, 1922700, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨-298963, -75416, -145584, -66913, 1922700, by decide⟩, -- source row 1717
  pairEntry 9 21 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1764
  pairEntry 9 30 (by decide) ⟨24556, 128042, 17542, 91469, 961350, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨-249851, 180668, -110500, 116025, 1922700, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨-24556, -128042, 0, 0, 480675, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨-12278, -64021, 64021, -12278, 480675, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨24556, 128042, -17542, -91469, 961350, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨298963, 75416, -145584, -66913, 1922700, by decide⟩, -- source row 1776
  pairEntry 10 21 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1792
  pairEntry 10 30 (by decide) ⟨298963, 75416, 145584, 66913, 1922700, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨24556, 128042, 17542, 91469, 961350, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨-12278, -64021, -64021, 12278, 480675, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨-24556, -128042, 0, 0, 480675, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨-249851, 180668, 110500, -116025, 1922700, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨24556, 128042, -17542, -91469, 961350, by decide⟩, -- source row 1804
  pairEntry 12 15 (by decide) ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨323, 36, 36, -323, 3900, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨323, 36, -36, 323, 1950, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨323, 36, -36, 323, 1950, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨969, 108, -36, 323, 3900, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1953
  pairEntry 21 30 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨39, -252, -84, -13, 1020, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨39, -252, -84, -13, 1020, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨39, -252, -84, -13, 1020, by decide⟩, -- source row 2062
  pairEntry 24 30 (by decide) ⟨-39, 252, 84, 13, 1020, by decide⟩, -- source row 2084
  pairEntry 24 31 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2085
  pairEntry 24 33 (by decide) ⟨-39, 252, 84, 13, 1020, by decide⟩, -- source row 2087
  pairEntry 24 34 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2088
  pairEntry 24 36 (by decide) ⟨-39, 252, 84, 13, 1020, by decide⟩, -- source row 2090
  pairEntry 24 37 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2097
  pairEntry 25 31 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2098
  pairEntry 25 33 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2100
  pairEntry 25 34 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩, -- source row 2101
  pairEntry 25 36 (by decide) ⟨0, 0, 84, 13, 510, by decide⟩, -- source row 2103
  pairEntry 25 37 (by decide) ⟨39, -252, 84, 13, 1020, by decide⟩ -- source row 2104
]

end Option2.NativeStress.NativeT

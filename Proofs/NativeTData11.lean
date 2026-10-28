module

public import NativeHWeights

@[expose] public section

/-! Exact source λ12; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda12 : List Entry := [
  idEntry 1 0 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 27
  idEntry 1 1 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 29
  idEntry 2 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 59
  idEntry 2 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 60
  idEntry 3 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 82
  idEntry 3 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-45, 24, 8, 15, 51, by decide⟩, -- source row 84
  idEntry 3 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 86
  idEntry 3 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 87
  idEntry 3 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 90
  idEntry 3 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 91
  idEntry 4 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 108
  idEntry 4 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 109
  idEntry 4 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 110
  idEntry 4 3 ⟨45, -24, 8, 15, 102, by decide⟩, -- source row 111
  idEntry 4 4 ⟨8, 15, 15, -8, 34, by decide⟩, -- source row 112
  idEntry 4 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 113
  idEntry 4 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 114
  idEntry 4 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 117
  idEntry 4 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 118
  idEntry 5 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 140
  idEntry 5 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 141
  idEntry 5 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 144
  idEntry 5 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 145
  idEntry 6 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 163
  idEntry 6 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-45, 24, 8, 15, 51, by decide⟩, -- source row 165
  idEntry 6 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 167
  idEntry 6 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 168
  idEntry 6 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 171
  idEntry 6 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 172
  idEntry 7 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 190
  idEntry 7 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 191
  idEntry 7 3 ⟨45, -24, 8, 15, 102, by decide⟩, -- source row 192
  idEntry 7 4 ⟨8, 15, 15, -8, 34, by decide⟩, -- source row 193
  idEntry 7 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 194
  idEntry 7 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 195
  idEntry 7 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 198
  idEntry 7 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 199
  idEntry 8 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 221
  idEntry 8 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 222
  idEntry 8 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 225
  idEntry 8 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 226
  idEntry 9 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 243
  idEntry 9 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 244
  idEntry 9 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 245
  idEntry 9 3 ⟨-45, 24, 8, 15, 51, by decide⟩, -- source row 246
  idEntry 9 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 248
  idEntry 9 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 249
  idEntry 9 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 252
  idEntry 9 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 253
  idEntry 10 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 271
  idEntry 10 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 272
  idEntry 10 3 ⟨45, -24, 8, 15, 102, by decide⟩, -- source row 273
  idEntry 10 4 ⟨8, 15, 15, -8, 34, by decide⟩, -- source row 274
  idEntry 10 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 275
  idEntry 10 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 276
  idEntry 10 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 279
  idEntry 10 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 280
  idEntry 11 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 302
  idEntry 11 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 303
  idEntry 11 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 306
  idEntry 11 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 307
  idEntry 12 0 ⟨-837, 116, -116, -837, 6084, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-837, 116, -116, -837, 6084, by decide⟩, -- source row 325
  idEntry 12 2 ⟨837, -116, 116, 837, 3380, by decide⟩, -- source row 326
  idEntry 12 5 ⟨837, -116, 116, 837, 6084, by decide⟩, -- source row 329
  idEntry 12 6 ⟨348, 2511, 837, -116, 10140, by decide⟩, -- source row 330
  idEntry 13 0 ⟨5859, -812, 812, 5859, 30420, by decide⟩, -- source row 351
  idEntry 13 1 ⟨5859, -812, 812, 5859, 30420, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-2511, 348, -232, -1674, 5070, by decide⟩, -- source row 353
  idEntry 13 5 ⟨14229, -1972, 580, 4185, 30420, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-1740, -12555, -14229, 1972, 30420, by decide⟩, -- source row 357
  idEntry 14 0 ⟨1674, -232, -116, -837, 15210, by decide⟩, -- source row 378
  idEntry 14 1 ⟨1674, -232, -116, -837, 15210, by decide⟩, -- source row 379
  idEntry 14 2 ⟨-2511, 348, 116, 837, 10140, by decide⟩, -- source row 380
  idEntry 14 5 ⟨-5859, 812, -812, -5859, 30420, by decide⟩, -- source row 383
  idEntry 14 6 ⟨-348, -2511, -837, 116, 30420, by decide⟩, -- source row 384
  idEntry 15 0 ⟨-2511, 348, -116, -837, 30420, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-2511, 348, -116, -837, 30420, by decide⟩, -- source row 406
  idEntry 15 2 ⟨0, 0, 116, 837, 5070, by decide⟩, -- source row 407
  idEntry 15 5 ⟨-2511, 348, -116, -837, 15210, by decide⟩, -- source row 410
  idEntry 15 6 ⟨-116, -837, 0, 0, 845, by decide⟩, -- source row 411
  idEntry 16 0 ⟨-2511, 348, 116, 837, 15210, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-2511, 348, 116, 837, 15210, by decide⟩, -- source row 433
  idEntry 16 2 ⟨2511, -348, -464, -3348, 5070, by decide⟩, -- source row 434
  idEntry 16 5 ⟨-2511, 348, 116, 837, 7605, by decide⟩, -- source row 437
  idEntry 16 6 ⟨-580, -4185, 837, -116, 5070, by decide⟩, -- source row 438
  idEntry 17 0 ⟨7533, -1044, 580, 4185, 30420, by decide⟩, -- source row 459
  idEntry 17 1 ⟨7533, -1044, 580, 4185, 30420, by decide⟩, -- source row 460
  idEntry 17 2 ⟨-837, 116, 0, 0, 1690, by decide⟩, -- source row 461
  idEntry 17 5 ⟨0, 0, 464, 3348, 7605, by decide⟩, -- source row 464
  idEntry 17 6 ⟨-116, -837, 837, -116, 5070, by decide⟩, -- source row 465
  idEntry 18 2 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 488
  idEntry 18 5 ⟨-4185, 580, -348, -2511, 10140, by decide⟩, -- source row 491
  idEntry 18 6 ⟨348, 2511, -837, 116, 10140, by decide⟩, -- source row 492
  idEntry 19 0 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 513
  idEntry 19 1 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 514
  idEntry 19 2 ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 515
  idEntry 19 5 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 518
  idEntry 19 6 ⟨348, 2511, -837, 116, 10140, by decide⟩, -- source row 519
  idEntry 20 0 ⟨4185, -580, -116, -837, 10140, by decide⟩, -- source row 540
  idEntry 20 1 ⟨4185, -580, -116, -837, 10140, by decide⟩, -- source row 541
  idEntry 20 2 ⟨-9207, 1276, 116, 837, 10140, by decide⟩, -- source row 542
  idEntry 20 5 ⟨4185, -580, -116, -837, 10140, by decide⟩, -- source row 545
  idEntry 20 6 ⟨-348, -2511, 4185, -580, 10140, by decide⟩, -- source row 546
  idEntry 21 5 ⟨-2511, 348, -116, -837, 3380, by decide⟩, -- source row 572
  idEntry 21 6 ⟨348, 2511, -837, 116, 3380, by decide⟩, -- source row 573
  idEntry 22 5 ⟨-2511, 348, -116, -837, 3380, by decide⟩, -- source row 599
  idEntry 22 6 ⟨348, 2511, -837, 116, 3380, by decide⟩, -- source row 600
  idEntry 23 5 ⟨-2511, 348, -116, -837, 3380, by decide⟩, -- source row 626
  idEntry 23 6 ⟨348, 2511, -837, 116, 3380, by decide⟩, -- source row 627
  idEntry 24 5 ⟨0, 0, -116, -837, 1690, by decide⟩, -- source row 653
  idEntry 24 6 ⟨0, 0, -837, 116, 1690, by decide⟩, -- source row 654
  idEntry 25 5 ⟨0, 0, -116, -837, 1690, by decide⟩, -- source row 680
  idEntry 25 6 ⟨0, 0, -837, 116, 1690, by decide⟩, -- source row 681
  idEntry 26 5 ⟨0, 0, -116, -837, 1690, by decide⟩, -- source row 707
  idEntry 26 6 ⟨0, 0, -837, 116, 1690, by decide⟩, -- source row 708
  idEntry 30 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 810
  idEntry 30 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 811
  idEntry 30 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 812
  idEntry 30 3 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 813
  idEntry 30 4 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 814
  idEntry 30 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 815
  idEntry 30 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 816
  idEntry 30 9 ⟨225, -120, 40, 75, 289, by decide⟩, -- source row 819
  idEntry 30 10 ⟨-360, 192, -64, -120, 867, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 838
  idEntry 31 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 839
  idEntry 31 3 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 840
  idEntry 31 4 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 841
  idEntry 31 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 842
  idEntry 31 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 843
  idEntry 31 9 ⟨-161, 240, -80, 139, 578, by decide⟩, -- source row 846
  idEntry 31 10 ⟨720, 483, -739, 240, 1734, by decide⟩, -- source row 847
  idEntry 32 3 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 867
  idEntry 32 4 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 868
  idEntry 32 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 869
  idEntry 32 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 870
  idEntry 33 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 892
  idEntry 33 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 893
  idEntry 33 3 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 894
  idEntry 33 4 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 895
  idEntry 33 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 896
  idEntry 33 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 897
  idEntry 33 9 ⟨225, -120, 40, 75, 289, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-360, 192, -64, -120, 867, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 919
  idEntry 34 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 920
  idEntry 34 3 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 921
  idEntry 34 4 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 922
  idEntry 34 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 923
  idEntry 34 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 924
  idEntry 34 9 ⟨-161, 240, -80, 139, 578, by decide⟩, -- source row 927
  idEntry 34 10 ⟨720, 483, -739, 240, 1734, by decide⟩, -- source row 928
  idEntry 35 3 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 948
  idEntry 35 4 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 949
  idEntry 35 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 950
  idEntry 35 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 951
  idEntry 36 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 973
  idEntry 36 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 974
  idEntry 36 3 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 975
  idEntry 36 4 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 976
  idEntry 36 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 977
  idEntry 36 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 978
  idEntry 36 9 ⟨225, -120, 40, 75, 289, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-360, 192, -64, -120, 867, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 1003
  idEntry 37 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 1005
  idEntry 37 9 ⟨-161, 240, -80, 139, 578, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨720, 483, -739, 240, 1734, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 1030
  idEntry 38 5 ⟨-837, 116, -116, -837, 3380, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 1032
  sumEntry 0 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1097
  sumEntry 0 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1098
  sumEntry 0 15 ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1107
  sumEntry 0 16 ⟨-348, -2511, -837, 116, 30420, by decide⟩, -- source row 1108
  sumEntry 0 25 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1117
  sumEntry 0 26 ⟨0, 0, 837, -116, 15210, by decide⟩, -- source row 1118
  sumEntry 1 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1125
  sumEntry 1 9 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1128
  sumEntry 1 10 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1129
  sumEntry 1 13 ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨-116, -837, -837, 116, 10140, by decide⟩, -- source row 1133
  sumEntry 1 17 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1136
  sumEntry 1 18 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1137
  sumEntry 1 21 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨-116, -837, 0, 0, 5070, by decide⟩, -- source row 1141
  sumEntry 1 25 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1144
  sumEntry 1 26 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1145
  sumEntry 2 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1152
  sumEntry 2 9 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1155
  sumEntry 2 10 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1156
  sumEntry 2 13 ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨-116, -837, 837, -116, 10140, by decide⟩, -- source row 1160
  sumEntry 2 17 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1163
  sumEntry 2 18 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1164
  sumEntry 2 21 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨116, 837, 837, -116, 10140, by decide⟩, -- source row 1168
  sumEntry 2 25 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1171
  sumEntry 2 26 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1172
  sumEntry 3 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1179
  sumEntry 3 9 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1182
  sumEntry 3 10 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1183
  sumEntry 3 13 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1187
  sumEntry 3 17 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1190
  sumEntry 3 18 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1191
  sumEntry 3 21 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1195
  sumEntry 3 25 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1198
  sumEntry 3 26 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1199
  sumEntry 4 0 ⟨-837, 116, -116, -837, 30420, by decide⟩, -- source row 1200
  sumEntry 4 1 ⟨837, -116, 116, 837, 15210, by decide⟩, -- source row 1201
  sumEntry 4 2 ⟨-837, 116, -116, -837, 30420, by decide⟩, -- source row 1202
  sumEntry 4 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1205
  sumEntry 4 6 ⟨348, 2511, 837, -116, 30420, by decide⟩, -- source row 1206
  sumEntry 4 16 ⟨348, 2511, 837, -116, 15210, by decide⟩, -- source row 1216
  sumEntry 5 0 ⟨2511, -348, 116, 837, 30420, by decide⟩, -- source row 1227
  sumEntry 5 1 ⟨0, 0, -116, -837, 15210, by decide⟩, -- source row 1228
  sumEntry 5 2 ⟨-2511, 348, 116, 837, 30420, by decide⟩, -- source row 1229
  sumEntry 5 6 ⟨-348, -2511, -837, 116, 7605, by decide⟩, -- source row 1233
  sumEntry 5 15 ⟨0, 0, 116, 837, 5070, by decide⟩, -- source row 1242
  sumEntry 5 16 ⟨696, 5022, -837, 116, 15210, by decide⟩, -- source row 1243
  sumEntry 5 25 ⟨837, -116, -116, -837, 5070, by decide⟩, -- source row 1252
  sumEntry 6 0 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1254
  sumEntry 6 5 ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1259
  sumEntry 6 6 ⟨0, 0, -837, 116, 15210, by decide⟩, -- source row 1260
  sumEntry 6 16 ⟨0, 0, -837, 116, 7605, by decide⟩, -- source row 1270
  sumEntry 6 25 ⟨837, -116, -116, -837, 5070, by decide⟩, -- source row 1279
  sumEntry 7 5 ⟨-2511, 348, -116, -837, 10140, by decide⟩, -- source row 1286
  sumEntry 7 6 ⟨348, 2511, -837, 116, 10140, by decide⟩, -- source row 1287
  sumEntry 7 11 ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1292
  sumEntry 7 12 ⟨-36, -15, -5, 12, 156, by decide⟩, -- source row 1293
  sumEntry 7 23 ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1304
  sumEntry 7 24 ⟨0, 0, -33, -56, 390, by decide⟩, -- source row 1305
  sumEntry 8 5 ⟨0, 0, -116, -837, 5070, by decide⟩, -- source row 1313
  sumEntry 8 6 ⟨0, 0, -837, 116, 5070, by decide⟩, -- source row 1314
  sumEntry 8 11 ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1319
  sumEntry 8 12 ⟨36, 15, 5, -12, 156, by decide⟩, -- source row 1320
  sumEntry 8 23 ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1331
  sumEntry 8 24 ⟨0, 0, 33, 56, 390, by decide⟩, -- source row 1332
  sumEntry 10 3 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1366
  sumEntry 10 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1368
  sumEntry 10 15 ⟨-1419, -8260, 0, 0, 50286, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨-8260, 1419, 0, 0, 50286, by decide⟩, -- source row 1378
  sumEntry 10 17 ⟨-75447, 409696, 409696, 75447, 4999020, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨409696, 75447, 75447, -409696, 4999020, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨15257, -19176, 0, 0, 147030, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨-19176, -15257, 0, 0, 147030, by decide⟩, -- source row 1382
  sumEntry 10 21 ⟨-155, 468, -468, -155, 5916, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨-468, -155, 155, -468, 5916, by decide⟩, -- source row 1384
  sumEntry 11 3 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1393
  sumEntry 11 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1395
  sumEntry 11 15 ⟨1419, 8260, -8260, 1419, 100572, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨8260, -1419, 1419, 8260, 100572, by decide⟩, -- source row 1405
  sumEntry 11 17 ⟨75447, -409696, 0, 0, 2499510, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨-409696, -75447, 0, 0, 2499510, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨-15257, 19176, -19176, -15257, 294060, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨19176, 15257, -15257, 19176, 294060, by decide⟩, -- source row 1409
  sumEntry 11 21 ⟨-155, 468, 468, 155, 5916, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨-468, -155, -155, 468, 5916, by decide⟩, -- source row 1411
  sumEntry 12 3 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1420
  sumEntry 12 5 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1422
  sumEntry 12 15 ⟨1419, 8260, 8260, -1419, 100572, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨8260, -1419, -1419, -8260, 100572, by decide⟩, -- source row 1432
  sumEntry 12 17 ⟨-75447, 409696, -409696, -75447, 4999020, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨409696, 75447, -75447, 409696, 4999020, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨-15257, 19176, 19176, 15257, 294060, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨19176, 15257, 15257, -19176, 294060, by decide⟩, -- source row 1436
  sumEntry 12 21 ⟨155, -468, 0, 0, 2958, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨468, 155, 0, 0, 2958, by decide⟩, -- source row 1438
  pairEntry 0 14 (by decide) ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1456
  pairEntry 0 15 (by decide) ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1457
  pairEntry 0 16 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1458
  pairEntry 0 19 (by decide) ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1461
  pairEntry 1 12 (by decide) ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1491
  pairEntry 1 13 (by decide) ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1492
  pairEntry 1 14 (by decide) ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1493
  pairEntry 1 16 (by decide) ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1495
  pairEntry 1 17 (by decide) ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1496
  pairEntry 1 18 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1497
  pairEntry 1 19 (by decide) ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1498
  pairEntry 1 20 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1499
  pairEntry 2 12 (by decide) ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1527
  pairEntry 2 13 (by decide) ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1528
  pairEntry 2 15 (by decide) ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1530
  pairEntry 2 16 (by decide) ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1531
  pairEntry 2 18 (by decide) ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1533
  pairEntry 2 20 (by decide) ⟨-837, 116, 0, 0, 2535, by decide⟩, -- source row 1535
  pairEntry 3 21 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1575
  pairEntry 3 30 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-151163, 455944, -196040, -367575, 4999020, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨313472, -261016, 64976, -54103, 2499510, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨156736, -130508, -130508, -156736, 1249755, by decide⟩, -- source row 1587
  pairEntry 4 21 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1609
  pairEntry 4 30 (by decide) ⟨313472, -261016, -64976, 54103, 2499510, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨-151163, 455944, 196040, 367575, 4999020, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨156736, -130508, 130508, 156736, 1249755, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1621
  pairEntry 6 21 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1674
  pairEntry 6 30 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨156736, -130508, -130508, -156736, 1249755, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨-151163, 455944, -196040, -367575, 4999020, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨313472, -261016, 64976, -54103, 2499510, by decide⟩, -- source row 1686
  pairEntry 7 21 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1705
  pairEntry 7 30 (by decide) ⟨156736, -130508, 130508, 156736, 1249755, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨313472, -261016, -64976, 54103, 2499510, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨-151163, 455944, 196040, 367575, 4999020, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1717
  pairEntry 9 21 (by decide) ⟨15, -36, 12, 5, 156, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨-15, 36, -12, -5, 156, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1764
  pairEntry 9 30 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨313472, -261016, 64976, -54103, 2499510, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨156736, -130508, -130508, -156736, 1249755, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨-151163, 455944, -196040, -367575, 4999020, by decide⟩, -- source row 1776
  pairEntry 10 21 (by decide) ⟨15, -36, -12, -5, 156, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨0, 0, -12, -5, 78, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨-15, 36, 12, 5, 156, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨0, 0, 12, 5, 78, by decide⟩, -- source row 1792
  pairEntry 10 30 (by decide) ⟨-151163, 455944, 196040, 367575, 4999020, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨475781, -66088, 325992, 259369, 4999020, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨156736, -130508, 130508, 156736, 1249755, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨313472, -261016, 0, 0, 1249755, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨313472, -261016, -64976, 54103, 2499510, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨475781, -66088, -325992, -259369, 4999020, by decide⟩, -- source row 1804
  pairEntry 12 15 (by decide) ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1835
  pairEntry 13 15 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1860
  pairEntry 13 16 (by decide) ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1861
  pairEntry 13 17 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1862
  pairEntry 13 18 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1863
  pairEntry 13 20 (by decide) ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1865
  pairEntry 14 17 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1886
  pairEntry 14 19 (by decide) ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1888
  pairEntry 14 20 (by decide) ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1889
  pairEntry 15 19 (by decide) ⟨-837, 116, 0, 0, 5070, by decide⟩, -- source row 1911
  pairEntry 16 18 (by decide) ⟨837, -116, -116, -837, 5070, by decide⟩, -- source row 1932
  pairEntry 16 19 (by decide) ⟨837, -116, -116, -837, 5070, by decide⟩, -- source row 1933
  pairEntry 16 20 (by decide) ⟨2511, -348, -116, -837, 10140, by decide⟩, -- source row 1934
  pairEntry 17 18 (by decide) ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1953
  pairEntry 21 30 (by decide) ⟨0, 0, 6764, 31323, 192270, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨-93969, 20292, 6764, 31323, 384540, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨93969, -20292, -6764, -31323, 384540, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨93969, -20292, 6764, 31323, 384540, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨-93969, 20292, -6764, -31323, 384540, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨0, 0, -6764, -31323, 192270, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨-93969, 20292, 6764, 31323, 384540, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨-93969, 20292, -6764, -31323, 384540, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨93969, -20292, 6764, 31323, 384540, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨0, 0, 6764, 31323, 192270, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨0, 0, -6764, -31323, 192270, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨93969, -20292, -6764, -31323, 384540, by decide⟩, -- source row 2062
  pairEntry 24 30 (by decide) ⟨0, 0, -6764, -31323, 192270, by decide⟩, -- source row 2084
  pairEntry 24 31 (by decide) ⟨93969, -20292, -6764, -31323, 384540, by decide⟩, -- source row 2085
  pairEntry 24 33 (by decide) ⟨-93969, 20292, 6764, 31323, 384540, by decide⟩, -- source row 2087
  pairEntry 24 34 (by decide) ⟨-93969, 20292, -6764, -31323, 384540, by decide⟩, -- source row 2088
  pairEntry 24 36 (by decide) ⟨93969, -20292, 6764, 31323, 384540, by decide⟩, -- source row 2090
  pairEntry 24 37 (by decide) ⟨0, 0, 6764, 31323, 192270, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨93969, -20292, -6764, -31323, 384540, by decide⟩, -- source row 2097
  pairEntry 25 31 (by decide) ⟨93969, -20292, 6764, 31323, 384540, by decide⟩, -- source row 2098
  pairEntry 25 33 (by decide) ⟨-93969, 20292, -6764, -31323, 384540, by decide⟩, -- source row 2100
  pairEntry 25 34 (by decide) ⟨0, 0, -6764, -31323, 192270, by decide⟩, -- source row 2101
  pairEntry 25 36 (by decide) ⟨0, 0, 6764, 31323, 192270, by decide⟩, -- source row 2103
  pairEntry 25 37 (by decide) ⟨-93969, 20292, 6764, 31323, 384540, by decide⟩ -- source row 2104
]

end Option2.NativeStress.NativeT

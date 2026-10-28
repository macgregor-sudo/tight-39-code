module

public import NativeHWeights

@[expose] public section

/-! Exact source λ17; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda17 : List Entry := [
  idEntry 0 0 ⟨-8127, -16936, -16936, 8127, 225420, by decide⟩, -- source row 0
  idEntry 0 1 ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 1
  idEntry 0 2 ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 2
  idEntry 0 21 ⟨161, -240, 240, 161, 1156, by decide⟩, -- source row 21
  idEntry 0 22 ⟨-240, -161, 161, -240, 1156, by decide⟩, -- source row 22
  idEntry 1 0 ⟨8127, 16936, 16936, -8127, 150280, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-8127, -16936, -16936, 8127, 150280, by decide⟩, -- source row 28
  idEntry 1 2 ⟨8127, 16936, 16936, -8127, 150280, by decide⟩, -- source row 29
  idEntry 3 0 ⟨483, -720, 240, 161, 3468, by decide⟩, -- source row 81
  idEntry 3 1 ⟨483, -720, 240, 161, 3468, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-483, 720, -240, -161, 1156, by decide⟩, -- source row 83
  idEntry 3 3 ⟨483, -720, 240, 161, 867, by decide⟩, -- source row 84
  idEntry 3 5 ⟨161, -240, 240, 161, 1156, by decide⟩, -- source row 86
  idEntry 3 6 ⟨-240, -161, 161, -240, 1156, by decide⟩, -- source row 87
  idEntry 3 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 88
  idEntry 3 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 89
  idEntry 4 0 ⟨0, 0, 240, 161, 1734, by decide⟩, -- source row 108
  idEntry 4 1 ⟨0, 0, 240, 161, 1734, by decide⟩, -- source row 109
  idEntry 4 2 ⟨0, 0, -240, -161, 578, by decide⟩, -- source row 110
  idEntry 4 3 ⟨0, 0, -240, -161, 867, by decide⟩, -- source row 111
  idEntry 4 4 ⟨-240, -161, 0, 0, 289, by decide⟩, -- source row 112
  idEntry 4 5 ⟨-161, 240, 0, 0, 578, by decide⟩, -- source row 113
  idEntry 4 6 ⟨240, 161, 0, 0, 578, by decide⟩, -- source row 114
  idEntry 4 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 115
  idEntry 4 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 116
  idEntry 5 5 ⟨161, -240, -240, -161, 1156, by decide⟩, -- source row 140
  idEntry 5 6 ⟨-240, -161, -161, 240, 1156, by decide⟩, -- source row 141
  idEntry 5 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 142
  idEntry 5 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 143
  idEntry 6 0 ⟨0, 0, -240, -161, 1734, by decide⟩, -- source row 162
  idEntry 6 1 ⟨0, 0, -240, -161, 1734, by decide⟩, -- source row 163
  idEntry 6 2 ⟨0, 0, 240, 161, 578, by decide⟩, -- source row 164
  idEntry 6 3 ⟨0, 0, -480, -322, 867, by decide⟩, -- source row 165
  idEntry 6 5 ⟨161, -240, -240, -161, 1156, by decide⟩, -- source row 167
  idEntry 6 6 ⟨-240, -161, -161, 240, 1156, by decide⟩, -- source row 168
  idEntry 6 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 169
  idEntry 6 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 170
  idEntry 7 0 ⟨483, -720, -240, -161, 3468, by decide⟩, -- source row 189
  idEntry 7 1 ⟨483, -720, -240, -161, 3468, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-483, 720, 240, 161, 1156, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-483, 720, 240, 161, 1734, by decide⟩, -- source row 192
  idEntry 7 4 ⟨240, 161, -161, 240, 578, by decide⟩, -- source row 193
  idEntry 7 5 ⟨161, -240, 240, 161, 1156, by decide⟩, -- source row 194
  idEntry 7 6 ⟨-240, -161, 161, -240, 1156, by decide⟩, -- source row 195
  idEntry 7 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 196
  idEntry 7 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 197
  idEntry 8 5 ⟨-161, 240, 0, 0, 578, by decide⟩, -- source row 221
  idEntry 8 6 ⟨240, 161, 0, 0, 578, by decide⟩, -- source row 222
  idEntry 8 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 223
  idEntry 8 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 224
  idEntry 9 0 ⟨-483, 720, 240, 161, 3468, by decide⟩, -- source row 243
  idEntry 9 1 ⟨-483, 720, 240, 161, 3468, by decide⟩, -- source row 244
  idEntry 9 2 ⟨483, -720, -240, -161, 1156, by decide⟩, -- source row 245
  idEntry 9 3 ⟨-483, 720, 240, 161, 867, by decide⟩, -- source row 246
  idEntry 9 5 ⟨-161, 240, 0, 0, 578, by decide⟩, -- source row 248
  idEntry 9 6 ⟨240, 161, 0, 0, 578, by decide⟩, -- source row 249
  idEntry 9 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 250
  idEntry 9 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 251
  idEntry 10 0 ⟨-483, 720, -240, -161, 3468, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-483, 720, -240, -161, 3468, by decide⟩, -- source row 271
  idEntry 10 2 ⟨483, -720, 240, 161, 1156, by decide⟩, -- source row 272
  idEntry 10 3 ⟨483, -720, 240, 161, 1734, by decide⟩, -- source row 273
  idEntry 10 4 ⟨240, 161, 161, -240, 578, by decide⟩, -- source row 274
  idEntry 10 5 ⟨161, -240, -240, -161, 1156, by decide⟩, -- source row 275
  idEntry 10 6 ⟨-240, -161, -161, 240, 1156, by decide⟩, -- source row 276
  idEntry 10 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 277
  idEntry 10 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 278
  idEntry 11 5 ⟨161, -240, 240, 161, 1156, by decide⟩, -- source row 302
  idEntry 11 6 ⟨-240, -161, 161, -240, 1156, by decide⟩, -- source row 303
  idEntry 11 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 304
  idEntry 11 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 305
  idEntry 12 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 325
  idEntry 12 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 326
  idEntry 12 5 ⟨45, -24, 8, 15, 51, by decide⟩, -- source row 329
  idEntry 12 9 ⟨739, -240, 240, 161, 1156, by decide⟩, -- source row 333
  idEntry 12 10 ⟨-240, 417, 161, -240, 1156, by decide⟩, -- source row 334
  idEntry 13 0 ⟨-45, 24, -8, -15, 102, by decide⟩, -- source row 351
  idEntry 13 1 ⟨-45, 24, -8, -15, 102, by decide⟩, -- source row 352
  idEntry 13 2 ⟨45, -24, 8, 15, 34, by decide⟩, -- source row 353
  idEntry 13 5 ⟨-45, 24, -8, -15, 51, by decide⟩, -- source row 356
  idEntry 13 6 ⟨8, 15, 15, -8, 17, by decide⟩, -- source row 357
  idEntry 13 9 ⟨-611, 480, 0, -289, 1156, by decide⟩, -- source row 360
  idEntry 13 10 ⟨480, 33, 289, 0, 1156, by decide⟩, -- source row 361
  idEntry 14 9 ⟨-32, -60, -60, 32, 289, by decide⟩, -- source row 387
  idEntry 14 10 ⟨-120, -225, -225, 120, 578, by decide⟩, -- source row 388
  idEntry 15 0 ⟨0, 0, -8, -15, 51, by decide⟩, -- source row 405
  idEntry 15 1 ⟨0, 0, -8, -15, 51, by decide⟩, -- source row 406
  idEntry 15 2 ⟨0, 0, 8, 15, 17, by decide⟩, -- source row 407
  idEntry 15 5 ⟨0, 0, 32, 60, 51, by decide⟩, -- source row 410
  idEntry 15 9 ⟨64, 120, 0, 0, 289, by decide⟩, -- source row 414
  idEntry 15 10 ⟨120, 225, 0, 0, 289, by decide⟩, -- source row 415
  idEntry 16 0 ⟨0, 0, -8, -15, 102, by decide⟩, -- source row 432
  idEntry 16 1 ⟨0, 0, -8, -15, 102, by decide⟩, -- source row 433
  idEntry 16 2 ⟨0, 0, 8, 15, 34, by decide⟩, -- source row 434
  idEntry 16 5 ⟨0, 0, -8, -15, 51, by decide⟩, -- source row 437
  idEntry 16 6 ⟨8, 15, 0, 0, 17, by decide⟩, -- source row 438
  idEntry 16 9 ⟨-64, -120, -120, -225, 578, by decide⟩, -- source row 441
  idEntry 16 10 ⟨-120, -225, 64, 120, 578, by decide⟩, -- source row 442
  idEntry 17 9 ⟨-64, -120, 120, 225, 578, by decide⟩, -- source row 468
  idEntry 17 10 ⟨-120, -225, -64, -120, 578, by decide⟩, -- source row 469
  idEntry 18 0 ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 486
  idEntry 18 1 ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-45, 24, 8, 15, 68, by decide⟩, -- source row 488
  idEntry 18 5 ⟨-45, 24, 8, 15, 51, by decide⟩, -- source row 491
  idEntry 18 9 ⟨739, -240, -240, -161, 1156, by decide⟩, -- source row 495
  idEntry 18 10 ⟨-240, 417, -161, 240, 1156, by decide⟩, -- source row 496
  idEntry 19 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 513
  idEntry 19 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 514
  idEntry 19 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 515
  idEntry 19 5 ⟨-45, 24, 8, 15, 102, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-8, -15, 15, -8, 34, by decide⟩, -- source row 519
  idEntry 19 9 ⟨-32, -60, 60, -32, 289, by decide⟩, -- source row 522
  idEntry 19 10 ⟨-120, -225, 225, -120, 578, by decide⟩, -- source row 523
  idEntry 20 9 ⟨-611, 480, 0, 289, 1156, by decide⟩, -- source row 549
  idEntry 20 10 ⟨480, 33, -289, 0, 1156, by decide⟩, -- source row 550
  idEntry 21 0 ⟨-24381, -50808, 16936, -8127, 225420, by decide⟩, -- source row 567
  idEntry 21 1 ⟨0, 0, -16936, 8127, 112710, by decide⟩, -- source row 568
  idEntry 21 2 ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 569
  idEntry 21 7 ⟨75871, -15572, 83316, 43363, 375700, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-119916, 140887, 130089, -249948, 1127100, by decide⟩, -- source row 575
  idEntry 22 0 ⟨-8127, -16936, -16936, 8127, 75140, by decide⟩, -- source row 594
  idEntry 22 2 ⟨8127, 16936, 50808, -24381, 225420, by decide⟩, -- source row 596
  idEntry 22 7 ⟨-325137, -156516, -119916, 140887, 1127100, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-10116, -411863, -227613, 46716, 1127100, by decide⟩, -- source row 602
  idEntry 23 0 ⟨89397, 186296, 50808, -24381, 450840, by decide⟩, -- source row 621
  idEntry 23 1 ⟨-8127, -16936, 50808, -24381, 450840, by decide⟩, -- source row 622
  idEntry 23 2 ⟨-8127, -16936, -84680, 40635, 450840, by decide⟩, -- source row 623
  idEntry 23 7 ⟨-67744, 32508, 16936, -8127, 187850, by decide⟩, -- source row 628
  idEntry 23 8 ⟨152424, -73143, 67744, -32508, 563550, by decide⟩, -- source row 629
  idEntry 24 0 ⟨24381, 50808, 16936, -8127, 225420, by decide⟩, -- source row 648
  idEntry 24 1 ⟨-24381, -50808, 16936, -8127, 225420, by decide⟩, -- source row 649
  idEntry 24 2 ⟨8127, 16936, -16936, 8127, 225420, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-51490, 66380, -16936, 8127, 187850, by decide⟩, -- source row 655
  idEntry 24 8 ⟨217440, 62345, -67744, 32508, 563550, by decide⟩, -- source row 656
  idEntry 25 0 ⟨-8127, -16936, 16936, -8127, 112710, by decide⟩, -- source row 675
  idEntry 25 1 ⟨8127, 16936, -16936, 8127, 225420, by decide⟩, -- source row 676
  idEntry 25 2 ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-67744, 32508, 16936, -8127, 187850, by decide⟩, -- source row 682
  idEntry 25 8 ⟨152424, -73143, 67744, -32508, 563550, by decide⟩, -- source row 683
  idEntry 26 0 ⟨-8127, -16936, -50808, 24381, 225420, by decide⟩, -- source row 702
  idEntry 26 1 ⟨8127, 16936, 0, 0, 112710, by decide⟩, -- source row 703
  idEntry 26 2 ⟨-8127, -16936, 0, 0, 112710, by decide⟩, -- source row 704
  idEntry 26 7 ⟨24381, 50808, -32508, -67744, 563550, by decide⟩, -- source row 709
  idEntry 26 8 ⟨32508, 67744, 24381, 50808, 563550, by decide⟩, -- source row 710
  idEntry 27 0 ⟨-8127, -16936, -50808, 24381, 225420, by decide⟩, -- source row 729
  idEntry 27 1 ⟨8127, 16936, 0, 0, 112710, by decide⟩, -- source row 730
  idEntry 27 2 ⟨0, 0, 16936, -8127, 112710, by decide⟩, -- source row 731
  idEntry 27 7 ⟨25745, -33190, 682, -41999, 187850, by decide⟩, -- source row 736
  idEntry 27 8 ⟨-217440, -62345, 208631, 87408, 1127100, by decide⟩, -- source row 737
  idEntry 28 0 ⟨8127, 16936, 0, 0, 56355, by decide⟩, -- source row 756
  idEntry 28 1 ⟨-8127, -16936, 0, 0, 112710, by decide⟩, -- source row 757
  idEntry 28 2 ⟨24381, 50808, -16936, 8127, 450840, by decide⟩, -- source row 758
  idEntry 28 7 ⟨41999, 682, -33190, -25745, 187850, by decide⟩, -- source row 763
  idEntry 28 8 ⟨-87408, 208631, -62345, 217440, 1127100, by decide⟩, -- source row 764
  idEntry 29 0 ⟨-56889, -118552, 84680, -40635, 450840, by decide⟩, -- source row 783
  idEntry 29 1 ⟨-8127, -16936, -16936, 8127, 450840, by decide⟩, -- source row 784
  idEntry 29 7 ⟨-8127, -16936, -16936, 8127, 375700, by decide⟩, -- source row 790
  idEntry 29 8 ⟨-8127, -16936, -16936, 8127, 281775, by decide⟩, -- source row 791
  idEntry 30 0 ⟨1419, 8260, 124, -5403, 33524, by decide⟩, -- source row 810
  idEntry 30 1 ⟨1419, 8260, 124, -5403, 33524, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-4257, -24780, -372, 16209, 33524, by decide⟩, -- source row 812
  idEntry 30 3 ⟨-1419, -8260, 8260, -1419, 33524, by decide⟩, -- source row 813
  idEntry 30 4 ⟨8260, -1419, 1419, 8260, 33524, by decide⟩, -- source row 814
  idEntry 30 5 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 815
  idEntry 30 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 816
  idEntry 30 9 ⟨-21285, -123900, -1860, 81045, 142477, by decide⟩, -- source row 819
  idEntry 30 10 ⟨11352, 66080, 992, -43224, 142477, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-7395, 3944, 4192, -3411, 33524, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-7395, 3944, 4192, -3411, 33524, by decide⟩, -- source row 838
  idEntry 31 2 ⟨22185, -11832, -12576, 10233, 33524, by decide⟩, -- source row 839
  idEntry 31 3 ⟨-1419, -8260, -8260, 1419, 33524, by decide⟩, -- source row 840
  idEntry 31 4 ⟨8260, -1419, -1419, -8260, 33524, by decide⟩, -- source row 841
  idEntry 31 5 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 842
  idEntry 31 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 843
  idEntry 31 9 ⟨-10317, -22704, 3720, -19613, 284954, by decide⟩, -- source row 846
  idEntry 31 10 ⟨247800, -185047, -144461, 86448, 284954, by decide⟩, -- source row 847
  idEntry 32 3 ⟨1419, 8260, 0, 0, 16762, by decide⟩, -- source row 867
  idEntry 32 4 ⟨-8260, 1419, 0, 0, 16762, by decide⟩, -- source row 868
  idEntry 32 5 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 869
  idEntry 32 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 870
  idEntry 33 0 ⟨-1419, -8260, 124, -5403, 33524, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-1419, -8260, 124, -5403, 33524, by decide⟩, -- source row 892
  idEntry 33 2 ⟨4257, 24780, -372, 16209, 33524, by decide⟩, -- source row 893
  idEntry 33 3 ⟨-1419, -8260, -8260, 1419, 33524, by decide⟩, -- source row 894
  idEntry 33 4 ⟨8260, -1419, -1419, -8260, 33524, by decide⟩, -- source row 895
  idEntry 33 5 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 896
  idEntry 33 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 897
  idEntry 33 9 ⟨21285, 123900, -1860, 81045, 142477, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-11352, -66080, 992, -43224, 142477, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-4407, -2158, -2034, -996, 16762, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-4407, -2158, -2034, -996, 16762, by decide⟩, -- source row 919
  idEntry 34 2 ⟨13221, 6474, 6102, 2988, 16762, by decide⟩, -- source row 920
  idEntry 34 3 ⟨1419, 8260, 0, 0, 16762, by decide⟩, -- source row 921
  idEntry 34 4 ⟨-8260, 1419, 0, 0, 16762, by decide⟩, -- source row 922
  idEntry 34 5 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 923
  idEntry 34 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 924
  idEntry 34 9 ⟨-114921, -56274, -65766, -32204, 142477, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-56274, -27556, -49833, -24402, 142477, by decide⟩, -- source row 928
  idEntry 35 3 ⟨-1419, -8260, 8260, -1419, 33524, by decide⟩, -- source row 948
  idEntry 35 4 ⟨8260, -1419, 1419, 8260, 33524, by decide⟩, -- source row 949
  idEntry 35 5 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 950
  idEntry 35 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 951
  idEntry 36 0 ⟨0, 0, -2034, -996, 8381, by decide⟩, -- source row 972
  idEntry 36 1 ⟨0, 0, -2034, -996, 8381, by decide⟩, -- source row 973
  idEntry 36 2 ⟨0, 0, 6102, 2988, 8381, by decide⟩, -- source row 974
  idEntry 36 3 ⟨1419, 8260, 0, 0, 16762, by decide⟩, -- source row 975
  idEntry 36 4 ⟨-8260, 1419, 0, 0, 16762, by decide⟩, -- source row 976
  idEntry 36 5 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 977
  idEntry 36 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 978
  idEntry 36 9 ⟨0, 0, 122040, 59760, 142477, by decide⟩, -- source row 981
  idEntry 36 10 ⟨0, 0, -65088, -31872, 142477, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-1494, 3051, -1017, -498, 8381, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-1494, 3051, -1017, -498, 8381, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨4482, -9153, 3051, 1494, 8381, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨-1419, -8260, 8260, -1419, 33524, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨8260, -1419, 1419, 8260, 33524, by decide⟩, -- source row 1003
  idEntry 37 5 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 1005
  idEntry 37 9 ⟨-93636, 67626, -54414, 33876, 142477, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-67626, -93636, -28548, 99498, 142477, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨-1419, -8260, -8260, 1419, 33524, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨8260, -1419, -1419, -8260, 33524, by decide⟩, -- source row 1030
  idEntry 38 5 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 1032
  sumEntry 0 7 ⟨-178851, 148332, 18300, -92125, 2254200, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨184932, -5399, 92125, 18300, 2254200, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨3113439, -806448, 1014000, 680225, 29304600, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨-1221552, 1752989, 680225, -1014000, 29304600, by decide⟩, -- source row 1114
  sumEntry 1 5 ⟨161, -240, -240, -161, 3468, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨-240, -161, -161, 240, 3468, by decide⟩, -- source row 1125
  sumEntry 1 7 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1126
  sumEntry 1 8 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1127
  sumEntry 1 13 ⟨161, -240, 0, 0, 1734, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨-240, -161, 0, 0, 1734, by decide⟩, -- source row 1133
  sumEntry 1 15 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1134
  sumEntry 1 16 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1135
  sumEntry 1 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1141
  sumEntry 1 23 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1142
  sumEntry 1 24 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1143
  sumEntry 2 5 ⟨-161, 240, 0, 0, 1734, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨240, 161, 0, 0, 1734, by decide⟩, -- source row 1152
  sumEntry 2 7 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1153
  sumEntry 2 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1154
  sumEntry 2 13 ⟨161, -240, 0, 0, 1734, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨-240, -161, 0, 0, 1734, by decide⟩, -- source row 1160
  sumEntry 2 15 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1161
  sumEntry 2 16 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1162
  sumEntry 2 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1168
  sumEntry 2 23 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1169
  sumEntry 2 24 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1170
  sumEntry 3 5 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1179
  sumEntry 3 7 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1180
  sumEntry 3 8 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1181
  sumEntry 3 13 ⟨161, -240, 0, 0, 1734, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨-240, -161, 0, 0, 1734, by decide⟩, -- source row 1187
  sumEntry 3 15 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1188
  sumEntry 3 16 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1189
  sumEntry 3 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1195
  sumEntry 3 23 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1196
  sumEntry 3 24 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1197
  sumEntry 4 9 ⟨-32, -60, -60, 32, 867, by decide⟩, -- source row 1209
  sumEntry 4 10 ⟨-40, -75, -75, 40, 578, by decide⟩, -- source row 1210
  sumEntry 4 11 ⟨611, -480, 0, 289, 3468, by decide⟩, -- source row 1211
  sumEntry 4 12 ⟨480, 33, 289, 0, 3468, by decide⟩, -- source row 1212
  sumEntry 4 21 ⟨739, -240, 240, 161, 3468, by decide⟩, -- source row 1221
  sumEntry 4 22 ⟨-240, 417, 161, -240, 3468, by decide⟩, -- source row 1222
  sumEntry 5 9 ⟨-64, -120, 120, 225, 1734, by decide⟩, -- source row 1236
  sumEntry 5 10 ⟨-120, -225, -64, -120, 1734, by decide⟩, -- source row 1237
  sumEntry 5 11 ⟨-64, -120, 0, 0, 867, by decide⟩, -- source row 1238
  sumEntry 5 12 ⟨40, 75, 0, 0, 289, by decide⟩, -- source row 1239
  sumEntry 5 21 ⟨-64, -120, 120, 225, 1734, by decide⟩, -- source row 1248
  sumEntry 5 22 ⟨-120, -225, -64, -120, 1734, by decide⟩, -- source row 1249
  sumEntry 6 9 ⟨-611, 480, 0, 289, 3468, by decide⟩, -- source row 1263
  sumEntry 6 10 ⟨480, 33, -289, 0, 3468, by decide⟩, -- source row 1264
  sumEntry 6 11 ⟨611, -480, 0, -289, 3468, by decide⟩, -- source row 1265
  sumEntry 6 12 ⟨480, 33, -289, 0, 3468, by decide⟩, -- source row 1266
  sumEntry 6 21 ⟨-32, -60, 60, -32, 867, by decide⟩, -- source row 1275
  sumEntry 6 22 ⟨-40, -75, 75, -40, 578, by decide⟩, -- source row 1276
  sumEntry 7 0 ⟨24381, 50808, -16936, 8127, 450840, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨-8127, -16936, -16936, 8127, 450840, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨130089, -249948, 10116, 411863, 3381300, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨-83316, -43363, -108379, -52172, 1127100, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨162597, -182204, 65016, 135488, 1465230, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨546612, 487791, 81270, 169360, 4395690, by decide⟩, -- source row 1299
  sumEntry 8 0 ⟨-8127, -16936, -16936, 8127, 225420, by decide⟩, -- source row 1308
  sumEntry 8 7 ⟨-682839, 140148, 119916, -140887, 3381300, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨119916, -140887, 75871, -15572, 1127100, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨0, 0, -117188, -27109, 1465230, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨0, 0, 569061, -377252, 4395690, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨-24381, -50808, 16936, -8127, 450840, by decide⟩, -- source row 1335
  sumEntry 9 1 ⟨-8127, -16936, -16936, 8127, 225420, by decide⟩, -- source row 1336
  sumEntry 9 7 ⟨92125, 18300, -49444, -59617, 751400, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨-54900, 276375, 5399, 184932, 2254200, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨-264213, 230966, 48762, 101616, 1465230, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨-449088, -284559, 40635, 84680, 2930460, by decide⟩, -- source row 1353
  sumEntry 10 3 ⟨1419, 8260, 0, 0, 50286, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨-8260, 1419, 0, 0, 50286, by decide⟩, -- source row 1366
  sumEntry 10 5 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1368
  sumEntry 10 15 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1378
  sumEntry 10 17 ⟨-1419, -8260, 0, 0, 50286, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨-8260, 1419, 0, 0, 50286, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨-155, 468, -468, -155, 5916, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨468, 155, -155, 468, 5916, by decide⟩, -- source row 1382
  sumEntry 10 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1384
  sumEntry 11 3 ⟨-1419, -8260, 8260, -1419, 100572, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨8260, -1419, 1419, 8260, 100572, by decide⟩, -- source row 1393
  sumEntry 11 5 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1395
  sumEntry 11 15 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1405
  sumEntry 11 17 ⟨1419, 8260, -8260, 1419, 100572, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨8260, -1419, 1419, 8260, 100572, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨-155, 468, 468, 155, 5916, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨468, 155, 155, -468, 5916, by decide⟩, -- source row 1409
  sumEntry 11 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1411
  sumEntry 12 3 ⟨-1419, -8260, -8260, 1419, 100572, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨8260, -1419, -1419, -8260, 100572, by decide⟩, -- source row 1420
  sumEntry 12 5 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1422
  sumEntry 12 15 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1432
  sumEntry 12 17 ⟨1419, 8260, 8260, -1419, 100572, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨8260, -1419, -1419, -8260, 100572, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨155, -468, 0, 0, 2958, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨-468, -155, 0, 0, 2958, by decide⟩, -- source row 1436
  sumEntry 12 21 ⟨161, -240, 240, 161, 3468, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨-240, -161, 161, -240, 3468, by decide⟩, -- source row 1438
  pairEntry 0 21 (by decide) ⟨-40635, -84680, 50808, -24381, 450840, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨-8127, -16936, 0, 0, 112710, by decide⟩, -- source row 1464
  pairEntry 0 24 (by decide) ⟨24381, 50808, 16936, -8127, 225420, by decide⟩, -- source row 1466
  pairEntry 0 25 (by decide) ⟨0, 0, 16936, -8127, 112710, by decide⟩, -- source row 1467
  pairEntry 0 27 (by decide) ⟨8127, 16936, -16936, 8127, 225420, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨56889, 118552, -16936, 8127, 450840, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨8127, 16936, 16936, -8127, 450840, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 1501
  pairEntry 1 27 (by decide) ⟨8127, 16936, 16936, -8127, 150280, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨8127, 16936, 16936, -8127, 450840, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨8127, 16936, 16936, -8127, 450840, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨-8127, -16936, -16936, 8127, 450840, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨8127, 16936, 16936, -8127, 450840, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨-8127, -16936, -16936, 8127, 450840, by decide⟩, -- source row 1544
  pairEntry 3 12 (by decide) ⟨-739, 240, -240, -161, 3468, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨-611, 480, 0, -289, 3468, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨64, 120, -120, -225, 1734, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨64, 120, 0, 0, 867, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨32, 60, -60, 32, 867, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨-611, 480, 0, 289, 3468, by decide⟩, -- source row 1569
  pairEntry 3 30 (by decide) ⟨-203, -24476, 7956, 2635, 100572, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-2027, -152, -152, 2027, 50286, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨2027, 152, -8108, -608, 50286, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨2027, 152, 0, 0, 25143, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨-3851, 24172, 8260, -1419, 100572, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨-2027, -152, 152, -2027, 50286, by decide⟩, -- source row 1587
  pairEntry 4 12 (by decide) ⟨-32, -60, -60, 32, 867, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨-739, 240, -240, -161, 3468, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨-64, -120, -120, -225, 1734, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨64, 120, -120, -225, 1734, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨739, -240, -240, -161, 3468, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨32, 60, -60, 32, 867, by decide⟩, -- source row 1603
  pairEntry 4 30 (by decide) ⟨-2027, -152, -152, 2027, 50286, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨-3851, 24172, -8260, 1419, 100572, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨2027, 152, 0, 0, 25143, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨2027, 152, 8108, 608, 50286, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨-2027, -152, 152, -2027, 50286, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨-203, -24476, -7956, -2635, 100572, by decide⟩, -- source row 1621
  pairEntry 6 12 (by decide) ⟨32, 60, 60, -32, 867, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨739, -240, 240, 161, 3468, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨64, 120, 120, 225, 1734, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨-64, -120, 120, 225, 1734, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-739, 240, 240, 161, 3468, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-32, -60, 60, -32, 867, by decide⟩, -- source row 1668
  pairEntry 6 30 (by decide) ⟨-2027, -152, 0, 0, 25143, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨-2027, -152, -8108, -608, 50286, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨2027, 152, -152, 2027, 50286, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨203, 24476, 7956, 2635, 100572, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨2027, 152, 152, -2027, 50286, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨3851, -24172, 8260, -1419, 100572, by decide⟩, -- source row 1686
  pairEntry 7 12 (by decide) ⟨-611, 480, 0, -289, 3468, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨32, 60, 60, -32, 867, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨64, 120, 0, 0, 867, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨64, 120, 120, 225, 1734, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-611, 480, 0, 289, 3468, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-739, 240, 240, 161, 3468, by decide⟩, -- source row 1699
  pairEntry 7 30 (by decide) ⟨-2027, -152, -8108, -608, 50286, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨2027, 152, -8108, -608, 50286, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨203, 24476, 7956, 2635, 100572, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨-3851, 24172, 8260, -1419, 100572, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨3851, -24172, 8260, -1419, 100572, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨-203, -24476, 7956, 2635, 100572, by decide⟩, -- source row 1717
  pairEntry 9 12 (by decide) ⟨611, -480, 0, 289, 3468, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨-32, -60, -60, 32, 867, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨-64, -120, 0, 0, 867, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨-64, -120, -120, -225, 1734, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨611, -480, 0, -289, 3468, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨739, -240, -240, -161, 3468, by decide⟩, -- source row 1758
  pairEntry 9 30 (by decide) ⟨-203, -24476, -7956, -2635, 100572, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨3851, -24172, -8260, 1419, 100572, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨-3851, 24172, -8260, 1419, 100572, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨203, 24476, -7956, -2635, 100572, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨2027, 152, 8108, 608, 50286, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨-2027, -152, 8108, 608, 50286, by decide⟩, -- source row 1776
  pairEntry 10 12 (by decide) ⟨739, -240, 240, 161, 3468, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨611, -480, 0, 289, 3468, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨-64, -120, 120, 225, 1734, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨-64, -120, 0, 0, 867, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨-32, -60, 60, -32, 867, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨611, -480, 0, -289, 3468, by decide⟩, -- source row 1786
  pairEntry 10 30 (by decide) ⟨3851, -24172, -8260, 1419, 100572, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨2027, 152, -152, 2027, 50286, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨203, 24476, -7956, -2635, 100572, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨2027, 152, 152, -2027, 50286, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨-2027, -152, 8108, 608, 50286, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨-2027, -152, 0, 0, 25143, by decide⟩, -- source row 1804
  pairEntry 12 31 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1851
  pairEntry 12 34 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1854
  pairEntry 12 37 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1857
  pairEntry 13 30 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 1882
  pairEntry 15 30 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1929
  pairEntry 16 30 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1944
  pairEntry 16 33 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1947
  pairEntry 16 36 (by decide) ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 1950
  pairEntry 18 30 (by decide) ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 1985
  pairEntry 18 33 (by decide) ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 1988
  pairEntry 18 36 (by decide) ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 1991
  pairEntry 19 31 (by decide) ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 2005
  pairEntry 19 34 (by decide) ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 2008
  pairEntry 19 37 (by decide) ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 2011
  pairEntry 21 24 (by decide) ⟨-8127, -16936, -16936, 8127, 225420, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨-8127, -16936, 16936, -8127, 225420, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨8127, 16936, 0, 0, 112710, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨8127, 16936, 16936, -8127, 225420, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨-8127, -16936, -16936, 8127, 450840, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨-24381, -50808, 16936, -8127, 450840, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨8127, 16936, 16936, -8127, 450840, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨8127, 16936, -16936, 8127, 225420, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨-8127, -16936, 16936, -8127, 225420, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨8127, 16936, 0, 0, 112710, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨8127, 16936, -16936, 8127, 225420, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨-8127, -16936, 0, 0, 112710, by decide⟩ -- source row 2106
]

end Option2.NativeStress.NativeT

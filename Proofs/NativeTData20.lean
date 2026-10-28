module

public import NativeHWeights

@[expose] public section

/-! Exact source λ7; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda7 : List Entry := [
  idEntry 0 0 ⟨171, -140, 140, 171, 2652, by decide⟩, -- source row 0
  idEntry 0 1 ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 1
  idEntry 0 2 ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 2
  idEntry 1 0 ⟨-171, 140, -140, -171, 1768, by decide⟩, -- source row 27
  idEntry 1 1 ⟨171, -140, 140, 171, 1768, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-171, 140, -140, -171, 1768, by decide⟩, -- source row 29
  idEntry 1 17 ⟨-15, -8, 8, -15, 68, by decide⟩, -- source row 44
  idEntry 1 18 ⟨8, -15, 15, 8, 68, by decide⟩, -- source row 45
  idEntry 3 0 ⟨51, 0, -16, 13, 204, by decide⟩, -- source row 81
  idEntry 3 1 ⟨51, 0, -16, 13, 204, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-51, 0, 16, -13, 68, by decide⟩, -- source row 83
  idEntry 3 3 ⟨51, 0, -16, 13, 51, by decide⟩, -- source row 84
  idEntry 3 9 ⟨49, 8, -8, 15, 68, by decide⟩, -- source row 90
  idEntry 3 10 ⟨-8, -19, -15, -8, 68, by decide⟩, -- source row 91
  idEntry 4 0 ⟨-45, -24, -8, -19, 204, by decide⟩, -- source row 108
  idEntry 4 1 ⟨-45, -24, -8, -19, 204, by decide⟩, -- source row 109
  idEntry 4 2 ⟨45, 24, 8, 19, 68, by decide⟩, -- source row 110
  idEntry 4 3 ⟨45, 24, 8, 19, 102, by decide⟩, -- source row 111
  idEntry 4 4 ⟨8, 19, 15, 8, 34, by decide⟩, -- source row 112
  idEntry 4 9 ⟨-1, 4, 4, 1, 34, by decide⟩, -- source row 117
  idEntry 4 10 ⟨-2, 8, 8, 2, 17, by decide⟩, -- source row 118
  idEntry 5 9 ⟨-47, -16, 0, -17, 68, by decide⟩, -- source row 144
  idEntry 5 10 ⟨16, -13, -17, 0, 68, by decide⟩, -- source row 145
  idEntry 6 0 ⟨-51, 0, -16, 13, 204, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-51, 0, -16, 13, 204, by decide⟩, -- source row 163
  idEntry 6 2 ⟨51, 0, 16, -13, 68, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-51, 0, -16, 13, 51, by decide⟩, -- source row 165
  idEntry 6 9 ⟨49, 8, 8, -15, 68, by decide⟩, -- source row 171
  idEntry 6 10 ⟨-8, -19, 15, 8, 68, by decide⟩, -- source row 172
  idEntry 7 0 ⟨-24, -6, -2, 8, 51, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-24, -6, -2, 8, 51, by decide⟩, -- source row 190
  idEntry 7 2 ⟨24, 6, 2, -8, 17, by decide⟩, -- source row 191
  idEntry 7 3 ⟨48, 12, 4, -16, 51, by decide⟩, -- source row 192
  idEntry 7 4 ⟨4, -16, 16, 4, 17, by decide⟩, -- source row 193
  idEntry 7 9 ⟨-47, -16, 0, 17, 68, by decide⟩, -- source row 198
  idEntry 7 10 ⟨16, -13, 17, 0, 68, by decide⟩, -- source row 199
  idEntry 8 9 ⟨-1, 4, -4, -1, 34, by decide⟩, -- source row 225
  idEntry 8 10 ⟨-2, 8, -8, -2, 17, by decide⟩, -- source row 226
  idEntry 9 0 ⟨0, 0, -4, 16, 51, by decide⟩, -- source row 243
  idEntry 9 1 ⟨0, 0, -4, 16, 51, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, 4, -16, 17, by decide⟩, -- source row 245
  idEntry 9 3 ⟨0, 0, -16, 64, 51, by decide⟩, -- source row 246
  idEntry 9 9 ⟨1, -4, 0, 0, 17, by decide⟩, -- source row 252
  idEntry 9 10 ⟨4, -16, 0, 0, 17, by decide⟩, -- source row 253
  idEntry 10 0 ⟨3, -12, -4, 16, 102, by decide⟩, -- source row 270
  idEntry 10 1 ⟨3, -12, -4, 16, 102, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-3, 12, 4, -16, 34, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-3, 12, 4, -16, 51, by decide⟩, -- source row 273
  idEntry 10 4 ⟨4, -16, -1, 4, 17, by decide⟩, -- source row 274
  idEntry 10 9 ⟨-1, 4, -4, 16, 34, by decide⟩, -- source row 279
  idEntry 10 10 ⟨-4, 16, 1, -4, 34, by decide⟩, -- source row 280
  idEntry 11 9 ⟨-1, 4, 4, -16, 34, by decide⟩, -- source row 306
  idEntry 11 10 ⟨-4, 16, -1, 4, 34, by decide⟩, -- source row 307
  idEntry 12 0 ⟨0, 0, -8, 15, 102, by decide⟩, -- source row 324
  idEntry 12 1 ⟨0, 0, -8, 15, 102, by decide⟩, -- source row 325
  idEntry 12 2 ⟨0, 0, 8, -15, 34, by decide⟩, -- source row 326
  idEntry 12 3 ⟨-15, -8, 8, -15, 68, by decide⟩, -- source row 327
  idEntry 12 4 ⟨-8, 15, -15, -8, 68, by decide⟩, -- source row 328
  idEntry 12 5 ⟨0, 0, 16, -30, 51, by decide⟩, -- source row 329
  idEntry 12 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 331
  idEntry 12 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 332
  idEntry 13 0 ⟨45, 24, -8, 15, 204, by decide⟩, -- source row 351
  idEntry 13 1 ⟨45, 24, -8, 15, 204, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-45, -24, 8, -15, 68, by decide⟩, -- source row 353
  idEntry 13 3 ⟨-15, -8, -8, 15, 68, by decide⟩, -- source row 354
  idEntry 13 4 ⟨-8, 15, 15, 8, 68, by decide⟩, -- source row 355
  idEntry 13 5 ⟨45, 24, -8, 15, 102, by decide⟩, -- source row 356
  idEntry 13 6 ⟨8, -15, -15, -8, 34, by decide⟩, -- source row 357
  idEntry 13 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 358
  idEntry 13 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 359
  idEntry 14 3 ⟨15, 8, 0, 0, 34, by decide⟩, -- source row 381
  idEntry 14 4 ⟨8, -15, 0, 0, 34, by decide⟩, -- source row 382
  idEntry 14 7 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 385
  idEntry 14 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 386
  idEntry 15 0 ⟨-45, -24, 8, -15, 204, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-45, -24, 8, -15, 204, by decide⟩, -- source row 406
  idEntry 15 2 ⟨45, 24, -8, 15, 68, by decide⟩, -- source row 407
  idEntry 15 3 ⟨15, 8, 0, 0, 34, by decide⟩, -- source row 408
  idEntry 15 4 ⟨8, -15, 0, 0, 34, by decide⟩, -- source row 409
  idEntry 15 5 ⟨45, 24, -8, 15, 51, by decide⟩, -- source row 410
  idEntry 15 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 412
  idEntry 15 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 413
  idEntry 16 0 ⟨-45, -24, -8, 15, 204, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-45, -24, -8, 15, 204, by decide⟩, -- source row 433
  idEntry 16 2 ⟨45, 24, 8, -15, 68, by decide⟩, -- source row 434
  idEntry 16 3 ⟨-15, -8, 8, -15, 68, by decide⟩, -- source row 435
  idEntry 16 4 ⟨-8, 15, -15, -8, 68, by decide⟩, -- source row 436
  idEntry 16 5 ⟨-45, -24, -8, 15, 102, by decide⟩, -- source row 437
  idEntry 16 6 ⟨8, -15, 15, 8, 34, by decide⟩, -- source row 438
  idEntry 16 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 439
  idEntry 16 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 440
  idEntry 17 3 ⟨-15, -8, -8, 15, 68, by decide⟩, -- source row 462
  idEntry 17 4 ⟨-8, 15, 15, 8, 68, by decide⟩, -- source row 463
  idEntry 17 7 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 466
  idEntry 17 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 467
  idEntry 18 0 ⟨45, 24, 8, -15, 204, by decide⟩, -- source row 486
  idEntry 18 1 ⟨45, 24, 8, -15, 204, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-45, -24, -8, 15, 68, by decide⟩, -- source row 488
  idEntry 18 3 ⟨-15, -8, -8, 15, 68, by decide⟩, -- source row 489
  idEntry 18 4 ⟨-8, 15, 15, 8, 68, by decide⟩, -- source row 490
  idEntry 18 5 ⟨-45, -24, -8, 15, 51, by decide⟩, -- source row 491
  idEntry 18 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 493
  idEntry 18 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 494
  idEntry 19 0 ⟨0, 0, 8, -15, 102, by decide⟩, -- source row 513
  idEntry 19 1 ⟨0, 0, 8, -15, 102, by decide⟩, -- source row 514
  idEntry 19 2 ⟨0, 0, -8, 15, 34, by decide⟩, -- source row 515
  idEntry 19 3 ⟨15, 8, 0, 0, 34, by decide⟩, -- source row 516
  idEntry 19 4 ⟨8, -15, 0, 0, 34, by decide⟩, -- source row 517
  idEntry 19 5 ⟨0, 0, 8, -15, 51, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-8, 15, 0, 0, 17, by decide⟩, -- source row 519
  idEntry 19 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 520
  idEntry 19 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 521
  idEntry 20 3 ⟨-15, -8, 8, -15, 68, by decide⟩, -- source row 543
  idEntry 20 4 ⟨-8, 15, -15, -8, 68, by decide⟩, -- source row 544
  idEntry 20 7 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 547
  idEntry 20 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 548
  idEntry 21 0 ⟨-171, 140, 0, 0, 1326, by decide⟩, -- source row 567
  idEntry 21 1 ⟨171, -140, 420, 513, 2652, by decide⟩, -- source row 568
  idEntry 21 2 ⟨-171, 140, -420, -513, 2652, by decide⟩, -- source row 569
  idEntry 21 7 ⟨-389, -824, 264, -1073, 4420, by decide⟩, -- source row 574
  idEntry 21 8 ⟨1944, 979, -3219, -792, 13260, by decide⟩, -- source row 575
  idEntry 22 0 ⟨-171, 140, 140, 171, 1326, by decide⟩, -- source row 594
  idEntry 22 1 ⟨171, -140, -140, -171, 2652, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 596
  idEntry 22 7 ⟨-885, 4152, 1944, 979, 13260, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-4680, 1261, 1167, 2472, 13260, by decide⟩, -- source row 602
  idEntry 23 0 ⟨513, -420, -140, -171, 1768, by decide⟩, -- source row 621
  idEntry 23 1 ⟨-171, 140, -140, -171, 1768, by decide⟩, -- source row 622
  idEntry 23 2 ⟨171, -140, 700, 855, 5304, by decide⟩, -- source row 623
  idEntry 23 7 ⟨2193, 1632, -1104, 47, 6630, by decide⟩, -- source row 628
  idEntry 23 8 ⟨-576, -2099, -47, -1104, 6630, by decide⟩, -- source row 629
  idEntry 24 0 ⟨171, -140, 140, 171, 2652, by decide⟩, -- source row 648
  idEntry 24 1 ⟨342, -280, -140, -171, 1326, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-342, 280, 140, 171, 1326, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-1415, 16, -544, 731, 4420, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-2160, 4339, 2099, -576, 13260, by decide⟩, -- source row 656
  idEntry 25 0 ⟨513, -420, 140, 171, 2652, by decide⟩, -- source row 675
  idEntry 25 1 ⟨-513, 420, 140, 171, 2652, by decide⟩, -- source row 676
  idEntry 25 2 ⟨171, -140, -140, -171, 1326, by decide⟩, -- source row 677
  idEntry 25 7 ⟨4245, -48, 576, 2099, 13260, by decide⟩, -- source row 682
  idEntry 25 8 ⟨2160, -4339, 2193, 1632, 13260, by decide⟩, -- source row 683
  idEntry 26 0 ⟨-342, 280, -140, -171, 1326, by decide⟩, -- source row 702
  idEntry 26 1 ⟨-171, 140, 140, 171, 2652, by decide⟩, -- source row 703
  idEntry 26 2 ⟨171, -140, 0, 0, 1326, by decide⟩, -- source row 704
  idEntry 26 7 ⟨47, 1104, 544, -731, 4420, by decide⟩, -- source row 709
  idEntry 26 8 ⟨-3312, 141, -2099, 576, 13260, by decide⟩, -- source row 710
  idEntry 27 0 ⟨171, -140, 0, 0, 1326, by decide⟩, -- source row 729
  idEntry 27 1 ⟨-171, 140, 0, 0, 663, by decide⟩, -- source row 730
  idEntry 27 2 ⟨513, -420, -140, -171, 2652, by decide⟩, -- source row 731
  idEntry 27 7 ⟨1291, 1228, -140, -171, 4420, by decide⟩, -- source row 736
  idEntry 27 8 ⟨-918, -1819, -280, -342, 6630, by decide⟩, -- source row 737
  idEntry 28 0 ⟨0, 0, -140, -171, 1326, by decide⟩, -- source row 756
  idEntry 28 1 ⟨513, -420, 140, 171, 2652, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-1539, 1260, -140, -171, 5304, by decide⟩, -- source row 758
  idEntry 28 7 ⟨1539, -1260, 108, -2659, 13260, by decide⟩, -- source row 763
  idEntry 28 8 ⟨342, -280, -451, -202, 2210, by decide⟩, -- source row 764
  idEntry 29 0 ⟨-513, 420, 700, 855, 5304, by decide⟩, -- source row 783
  idEntry 29 1 ⟨513, -420, -140, -171, 5304, by decide⟩, -- source row 784
  idEntry 29 7 ⟨-840, -1026, 762, 233, 6630, by decide⟩, -- source row 790
  idEntry 29 8 ⟨1260, 1539, 607, 1788, 13260, by decide⟩, -- source row 791
  idEntry 30 0 ⟨357, -340, -268, 171, 1972, by decide⟩, -- source row 810
  idEntry 30 1 ⟨357, -340, -268, 171, 1972, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-1071, 1020, 804, -513, 1972, by decide⟩, -- source row 812
  idEntry 30 3 ⟨-15, -8, 0, 0, 34, by decide⟩, -- source row 813
  idEntry 30 4 ⟨-8, 15, 0, 0, 34, by decide⟩, -- source row 814
  idEntry 30 5 ⟨-21, 20, -20, -21, 116, by decide⟩, -- source row 815
  idEntry 30 6 ⟨-20, -21, 21, -20, 116, by decide⟩, -- source row 816
  idEntry 30 9 ⟨-5355, 5100, 4020, -2565, 8381, by decide⟩, -- source row 819
  idEntry 30 10 ⟨2856, -2720, -2144, 1368, 8381, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-39, -286, 18, 132, 986, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-39, -286, 18, 132, 986, by decide⟩, -- source row 838
  idEntry 31 2 ⟨117, 858, -54, -396, 986, by decide⟩, -- source row 839
  idEntry 31 3 ⟨15, 8, 8, -15, 68, by decide⟩, -- source row 840
  idEntry 31 4 ⟨8, -15, -15, -8, 68, by decide⟩, -- source row 841
  idEntry 31 5 ⟨21, -20, 0, 0, 58, by decide⟩, -- source row 842
  idEntry 31 6 ⟨20, 21, 0, 0, 58, by decide⟩, -- source row 843
  idEntry 31 9 ⟨-153, -1122, -42, -308, 8381, by decide⟩, -- source row 846
  idEntry 31 10 ⟨1122, 8228, -729, -5346, 8381, by decide⟩, -- source row 847
  idEntry 32 3 ⟨15, 8, -8, 15, 68, by decide⟩, -- source row 867
  idEntry 32 4 ⟨8, -15, 15, 8, 68, by decide⟩, -- source row 868
  idEntry 32 5 ⟨-21, 20, 20, 21, 116, by decide⟩, -- source row 869
  idEntry 32 6 ⟨-20, -21, -21, 20, 116, by decide⟩, -- source row 870
  idEntry 33 0 ⟨-357, 340, -268, 171, 1972, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-357, 340, -268, 171, 1972, by decide⟩, -- source row 892
  idEntry 33 2 ⟨1071, -1020, 804, -513, 1972, by decide⟩, -- source row 893
  idEntry 33 3 ⟨-15, -8, 0, 0, 34, by decide⟩, -- source row 894
  idEntry 33 4 ⟨-8, 15, 0, 0, 34, by decide⟩, -- source row 895
  idEntry 33 5 ⟨-21, 20, 20, 21, 116, by decide⟩, -- source row 896
  idEntry 33 6 ⟨-20, -21, -21, 20, 116, by decide⟩, -- source row 897
  idEntry 33 9 ⟨5355, -5100, 4020, -2565, 8381, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-2856, 2720, -2144, 1368, 8381, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-435, -232, -304, -93, 1972, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-435, -232, -304, -93, 1972, by decide⟩, -- source row 919
  idEntry 34 2 ⟨1305, 696, 912, 279, 1972, by decide⟩, -- source row 920
  idEntry 34 3 ⟨15, 8, 8, -15, 68, by decide⟩, -- source row 921
  idEntry 34 4 ⟨8, -15, -15, -8, 68, by decide⟩, -- source row 922
  idEntry 34 5 ⟨-21, 20, -20, -21, 116, by decide⟩, -- source row 923
  idEntry 34 6 ⟨-20, -21, 21, -20, 116, by decide⟩, -- source row 924
  idEntry 34 9 ⟨-13821, -5712, -8040, -3251, 16762, by decide⟩, -- source row 927
  idEntry 34 10 ⟨-10200, -2329, -4093, -2736, 16762, by decide⟩, -- source row 928
  idEntry 35 3 ⟨15, 8, -8, 15, 68, by decide⟩, -- source row 948
  idEntry 35 4 ⟨8, -15, 15, 8, 68, by decide⟩, -- source row 949
  idEntry 35 5 ⟨21, -20, 0, 0, 58, by decide⟩, -- source row 950
  idEntry 35 6 ⟨20, 21, 0, 0, 58, by decide⟩, -- source row 951
  idEntry 36 0 ⟨0, 0, 18, 132, 493, by decide⟩, -- source row 972
  idEntry 36 1 ⟨0, 0, 18, 132, 493, by decide⟩, -- source row 973
  idEntry 36 2 ⟨0, 0, -54, -396, 493, by decide⟩, -- source row 974
  idEntry 36 3 ⟨-15, -8, 0, 0, 34, by decide⟩, -- source row 975
  idEntry 36 4 ⟨-8, 15, 0, 0, 34, by decide⟩, -- source row 976
  idEntry 36 5 ⟨21, -20, 0, 0, 58, by decide⟩, -- source row 977
  idEntry 36 6 ⟨20, 21, 0, 0, 58, by decide⟩, -- source row 978
  idEntry 36 9 ⟨0, 0, -1080, -7920, 8381, by decide⟩, -- source row 981
  idEntry 36 10 ⟨0, 0, 576, 4224, 8381, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-198, 27, 9, 66, 493, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-198, 27, 9, 66, 493, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨594, -81, -27, -198, 493, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨15, 8, 8, -15, 68, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨8, -15, -15, -8, 68, by decide⟩, -- source row 1003
  idEntry 37 5 ⟨-21, 20, 20, 21, 116, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨-20, -21, -21, 20, 116, by decide⟩, -- source row 1005
  idEntry 37 9 ⟨-5508, 3978, -2898, 2412, 8381, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨3978, 5508, -6084, -246, 8381, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨15, 8, -8, 15, 68, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨8, -15, 15, 8, 68, by decide⟩, -- source row 1030
  idEntry 38 5 ⟨-21, 20, -20, -21, 116, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨-20, -21, 21, -20, 116, by decide⟩, -- source row 1032
  sumEntry 0 7 ⟨1167, 2472, 264, -1073, 26520, by decide⟩, -- source row 1099
  sumEntry 0 8 ⟨-1944, -979, -1073, -264, 26520, by decide⟩, -- source row 1100
  sumEntry 0 21 ⟨-29163, -24108, -14196, 2197, 344760, by decide⟩, -- source row 1113
  sumEntry 0 22 ⟨4284, 24769, -2197, -14196, 344760, by decide⟩, -- source row 1114
  sumEntry 1 9 ⟨-47, -16, 0, -17, 204, by decide⟩, -- source row 1128
  sumEntry 1 10 ⟨16, -13, -17, 0, 204, by decide⟩, -- source row 1129
  sumEntry 1 17 ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1136
  sumEntry 1 18 ⟨8, 19, 15, 8, 204, by decide⟩, -- source row 1137
  sumEntry 1 25 ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1144
  sumEntry 1 26 ⟨-2, 8, 8, 2, 51, by decide⟩, -- source row 1145
  sumEntry 2 9 ⟨-1, 4, -4, -1, 102, by decide⟩, -- source row 1155
  sumEntry 2 10 ⟨-2, 8, -8, -2, 51, by decide⟩, -- source row 1156
  sumEntry 2 17 ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1163
  sumEntry 2 18 ⟨2, -8, 8, 2, 51, by decide⟩, -- source row 1164
  sumEntry 2 25 ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1171
  sumEntry 2 26 ⟨-8, -19, 15, 8, 204, by decide⟩, -- source row 1172
  sumEntry 3 9 ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1182
  sumEntry 3 10 ⟨-4, 16, -1, 4, 102, by decide⟩, -- source row 1183
  sumEntry 3 17 ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1190
  sumEntry 3 18 ⟨4, -16, -1, 4, 102, by decide⟩, -- source row 1191
  sumEntry 3 25 ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1198
  sumEntry 3 26 ⟨-4, 16, -1, 4, 102, by decide⟩, -- source row 1199
  sumEntry 4 3 ⟨15, 8, 0, 0, 102, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨8, -15, 0, 0, 102, by decide⟩, -- source row 1204
  sumEntry 4 7 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1207
  sumEntry 4 8 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1208
  sumEntry 4 13 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1213
  sumEntry 4 14 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1214
  sumEntry 4 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1218
  sumEntry 4 19 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1219
  sumEntry 4 20 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1220
  sumEntry 4 23 ⟨-15, -8, -8, 15, 204, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨8, -15, -15, -8, 204, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨-15, -8, -8, 15, 204, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨-8, 15, 15, 8, 204, by decide⟩, -- source row 1231
  sumEntry 5 7 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1234
  sumEntry 5 8 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1235
  sumEntry 5 13 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1240
  sumEntry 5 14 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1241
  sumEntry 5 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1245
  sumEntry 5 19 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1246
  sumEntry 5 20 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1247
  sumEntry 5 23 ⟨-15, -8, -8, 15, 204, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨8, -15, -15, -8, 204, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨-8, 15, -15, -8, 204, by decide⟩, -- source row 1258
  sumEntry 6 7 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1261
  sumEntry 6 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1262
  sumEntry 6 13 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1267
  sumEntry 6 14 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1268
  sumEntry 6 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1272
  sumEntry 6 19 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1273
  sumEntry 6 20 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1274
  sumEntry 6 23 ⟨-15, -8, -8, 15, 204, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨8, -15, -15, -8, 204, by decide⟩, -- source row 1278
  sumEntry 7 0 ⟨171, -140, 140, 171, 5304, by decide⟩, -- source row 1281
  sumEntry 7 1 ⟨-513, 420, 140, 171, 5304, by decide⟩, -- source row 1282
  sumEntry 7 7 ⟨-3219, -792, 1944, 979, 39780, by decide⟩, -- source row 1288
  sumEntry 7 8 ⟨-264, 1073, 389, 824, 13260, by decide⟩, -- source row 1289
  sumEntry 7 17 ⟨-2535, -1352, 2736, -2240, 17238, by decide⟩, -- source row 1298
  sumEntry 7 18 ⟨4056, -7605, 3420, -2800, 51714, by decide⟩, -- source row 1299
  sumEntry 8 1 ⟨171, -140, 140, 171, 2652, by decide⟩, -- source row 1309
  sumEntry 8 7 ⟨1539, -1260, -684, 560, 19890, by decide⟩, -- source row 1315
  sumEntry 8 8 ⟨684, -560, 171, -140, 6630, by decide⟩, -- source row 1316
  sumEntry 8 17 ⟨-1710, 1400, -16, -1415, 17238, by decide⟩, -- source row 1325
  sumEntry 8 18 ⟨12312, -10080, 5895, 5456, 51714, by decide⟩, -- source row 1326
  sumEntry 9 0 ⟨171, -140, 140, 171, 5304, by decide⟩, -- source row 1335
  sumEntry 9 1 ⟨171, -140, 0, 0, 1326, by decide⟩, -- source row 1336
  sumEntry 9 7 ⟨1167, 2472, 264, -1073, 26520, by decide⟩, -- source row 1342
  sumEntry 9 8 ⟨-1944, -979, -1073, -264, 26520, by decide⟩, -- source row 1343
  sumEntry 9 17 ⟨-2520, -3078, 326, -1695, 17238, by decide⟩, -- source row 1352
  sumEntry 9 18 ⟨-2100, -2565, 4215, 3404, 34476, by decide⟩, -- source row 1353
  sumEntry 10 3 ⟨15, 8, -8, 15, 204, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1366
  sumEntry 10 5 ⟨-21, 20, 20, 21, 348, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨-20, -21, -21, 20, 348, by decide⟩, -- source row 1368
  sumEntry 10 15 ⟨21, -20, -20, -21, 348, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨-20, -21, -21, 20, 348, by decide⟩, -- source row 1378
  sumEntry 10 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1382
  sumEntry 10 21 ⟨-475, 132, 0, 0, 2958, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨-132, -475, 0, 0, 2958, by decide⟩, -- source row 1384
  sumEntry 11 3 ⟨15, 8, -8, 15, 204, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1393
  sumEntry 11 5 ⟨21, -20, 0, 0, 174, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨20, 21, 0, 0, 174, by decide⟩, -- source row 1395
  sumEntry 11 15 ⟨-21, 20, 0, 0, 174, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨20, 21, 0, 0, 174, by decide⟩, -- source row 1405
  sumEntry 11 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1409
  sumEntry 11 21 ⟨475, -132, 132, 475, 5916, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨132, 475, -475, 132, 5916, by decide⟩, -- source row 1411
  sumEntry 12 3 ⟨15, 8, -8, 15, 204, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1420
  sumEntry 12 5 ⟨-21, 20, -20, -21, 348, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨-20, -21, 21, -20, 348, by decide⟩, -- source row 1422
  sumEntry 12 15 ⟨21, -20, 20, 21, 348, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨-20, -21, 21, -20, 348, by decide⟩, -- source row 1432
  sumEntry 12 17 ⟨-15, -8, 8, -15, 204, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨8, -15, 15, 8, 204, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1436
  sumEntry 12 21 ⟨475, -132, -132, -475, 5916, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨132, 475, 475, -132, 5916, by decide⟩, -- source row 1438
  pairEntry 0 21 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 1463
  pairEntry 0 22 (by decide) ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 1464
  pairEntry 0 27 (by decide) ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 1469
  pairEntry 0 28 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 1470
  pairEntry 1 21 (by decide) ⟨855, -700, 140, 171, 5304, by decide⟩, -- source row 1500
  pairEntry 1 22 (by decide) ⟨171, -140, -140, -171, 1326, by decide⟩, -- source row 1501
  pairEntry 1 24 (by decide) ⟨0, 0, -140, -171, 1326, by decide⟩, -- source row 1503
  pairEntry 1 25 (by decide) ⟨-513, 420, -140, -171, 2652, by decide⟩, -- source row 1504
  pairEntry 1 27 (by decide) ⟨-1539, 1260, -140, -171, 5304, by decide⟩, -- source row 1506
  pairEntry 1 28 (by decide) ⟨-171, 140, 140, 171, 2652, by decide⟩, -- source row 1507
  pairEntry 1 29 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 1508
  pairEntry 2 22 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 1537
  pairEntry 2 23 (by decide) ⟨171, -140, 140, 171, 5304, by decide⟩, -- source row 1538
  pairEntry 2 27 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 1542
  pairEntry 2 29 (by decide) ⟨171, -140, 140, 171, 5304, by decide⟩, -- source row 1544
  pairEntry 3 12 (by decide) ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨-47, -16, 0, -17, 204, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨47, 16, 0, 17, 204, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨1, -4, -4, -1, 102, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨49, 8, -8, 15, 204, by decide⟩, -- source row 1569
  pairEntry 3 30 (by decide) ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1580
  pairEntry 3 31 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1581
  pairEntry 3 33 (by decide) ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1583
  pairEntry 3 34 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1584
  pairEntry 3 36 (by decide) ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1586
  pairEntry 3 37 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1587
  pairEntry 4 12 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨-49, -8, 8, -15, 204, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨49, 8, -8, 15, 204, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨47, 16, 0, 17, 204, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨-47, -16, 0, -17, 204, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨1, -4, -4, -1, 102, by decide⟩, -- source row 1603
  pairEntry 4 30 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1614
  pairEntry 4 31 (by decide) ⟨47, 16, 0, 17, 204, by decide⟩, -- source row 1615
  pairEntry 4 33 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1617
  pairEntry 4 34 (by decide) ⟨47, 16, 0, 17, 204, by decide⟩, -- source row 1618
  pairEntry 4 36 (by decide) ⟨-1, 4, 4, 1, 102, by decide⟩, -- source row 1620
  pairEntry 4 37 (by decide) ⟨47, 16, 0, 17, 204, by decide⟩, -- source row 1621
  pairEntry 6 12 (by decide) ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨-47, -16, 0, 17, 204, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨47, 16, 0, -17, 204, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-49, -8, -8, 15, 204, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-1, 4, -4, -1, 102, by decide⟩, -- source row 1668
  pairEntry 6 30 (by decide) ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1679
  pairEntry 6 31 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1680
  pairEntry 6 33 (by decide) ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1682
  pairEntry 6 34 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1683
  pairEntry 6 36 (by decide) ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1685
  pairEntry 6 37 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1686
  pairEntry 7 12 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨1, -4, 4, 1, 102, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨-1, 4, -4, -1, 102, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨47, 16, 0, -17, 204, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-47, -16, 0, 17, 204, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-49, -8, -8, 15, 204, by decide⟩, -- source row 1699
  pairEntry 7 30 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1710
  pairEntry 7 31 (by decide) ⟨47, 16, 0, -17, 204, by decide⟩, -- source row 1711
  pairEntry 7 33 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1713
  pairEntry 7 34 (by decide) ⟨47, 16, 0, -17, 204, by decide⟩, -- source row 1714
  pairEntry 7 36 (by decide) ⟨49, 8, 8, -15, 204, by decide⟩, -- source row 1716
  pairEntry 7 37 (by decide) ⟨47, 16, 0, -17, 204, by decide⟩, -- source row 1717
  pairEntry 9 12 (by decide) ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨1, -4, 0, 0, 51, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨-1, 4, 0, 0, 51, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨1, -4, -4, 16, 102, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨-1, 4, -4, 16, 102, by decide⟩, -- source row 1758
  pairEntry 9 30 (by decide) ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1769
  pairEntry 9 31 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1770
  pairEntry 9 33 (by decide) ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1772
  pairEntry 9 34 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1773
  pairEntry 9 36 (by decide) ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1775
  pairEntry 9 37 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1776
  pairEntry 10 12 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨1, -4, 4, -16, 102, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨-1, 4, -4, 16, 102, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨-1, 4, 0, 0, 51, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨1, -4, 0, 0, 51, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨1, -4, -4, 16, 102, by decide⟩, -- source row 1786
  pairEntry 10 30 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1797
  pairEntry 10 31 (by decide) ⟨-1, 4, 0, 0, 51, by decide⟩, -- source row 1798
  pairEntry 10 33 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1800
  pairEntry 10 34 (by decide) ⟨-1, 4, 0, 0, 51, by decide⟩, -- source row 1801
  pairEntry 10 36 (by decide) ⟨-1, 4, 4, -16, 102, by decide⟩, -- source row 1803
  pairEntry 10 37 (by decide) ⟨-1, 4, 0, 0, 51, by decide⟩, -- source row 1804
  pairEntry 12 31 (by decide) ⟨-63, 60, -20, -21, 348, by decide⟩, -- source row 1851
  pairEntry 12 34 (by decide) ⟨0, 0, 20, 21, 174, by decide⟩, -- source row 1854
  pairEntry 12 37 (by decide) ⟨63, -60, -20, -21, 348, by decide⟩, -- source row 1857
  pairEntry 13 30 (by decide) ⟨-63, 60, -20, -21, 348, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨-63, 60, -20, -21, 348, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨0, 0, 20, 21, 174, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨0, 0, 20, 21, 174, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨63, -60, -20, -21, 348, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨63, -60, -20, -21, 348, by decide⟩, -- source row 1882
  pairEntry 15 30 (by decide) ⟨-63, 60, 20, 21, 348, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨-63, 60, 20, 21, 348, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨63, -60, 20, 21, 348, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨63, -60, 20, 21, 348, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨0, 0, -20, -21, 174, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨0, 0, -20, -21, 174, by decide⟩, -- source row 1929
  pairEntry 16 30 (by decide) ⟨-63, 60, 20, 21, 348, by decide⟩, -- source row 1944
  pairEntry 16 33 (by decide) ⟨63, -60, 20, 21, 348, by decide⟩, -- source row 1947
  pairEntry 16 36 (by decide) ⟨0, 0, -20, -21, 174, by decide⟩, -- source row 1950
  pairEntry 18 30 (by decide) ⟨0, 0, 20, 21, 174, by decide⟩, -- source row 1985
  pairEntry 18 33 (by decide) ⟨63, -60, -20, -21, 348, by decide⟩, -- source row 1988
  pairEntry 18 36 (by decide) ⟨-63, 60, -20, -21, 348, by decide⟩, -- source row 1991
  pairEntry 19 31 (by decide) ⟨0, 0, -20, -21, 174, by decide⟩, -- source row 2005
  pairEntry 19 34 (by decide) ⟨-63, 60, 20, 21, 348, by decide⟩, -- source row 2008
  pairEntry 19 37 (by decide) ⟨63, -60, 20, 21, 348, by decide⟩, -- source row 2011
  pairEntry 21 24 (by decide) ⟨-171, 140, 0, 0, 1326, by decide⟩, -- source row 2033
  pairEntry 21 25 (by decide) ⟨171, -140, -140, -171, 2652, by decide⟩, -- source row 2034
  pairEntry 21 27 (by decide) ⟨171, -140, -140, -171, 2652, by decide⟩, -- source row 2036
  pairEntry 21 29 (by decide) ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 2038
  pairEntry 22 25 (by decide) ⟨171, -140, 0, 0, 1326, by decide⟩, -- source row 2050
  pairEntry 22 27 (by decide) ⟨171, -140, 140, 171, 5304, by decide⟩, -- source row 2052
  pairEntry 22 28 (by decide) ⟨-513, 420, 140, 171, 5304, by decide⟩, -- source row 2053
  pairEntry 22 29 (by decide) ⟨-171, 140, -140, -171, 5304, by decide⟩, -- source row 2054
  pairEntry 23 24 (by decide) ⟨-171, 140, 140, 171, 2652, by decide⟩, -- source row 2064
  pairEntry 24 27 (by decide) ⟨171, -140, 140, 171, 2652, by decide⟩, -- source row 2081
  pairEntry 24 28 (by decide) ⟨-171, 140, 0, 0, 1326, by decide⟩, -- source row 2082
  pairEntry 25 28 (by decide) ⟨-171, 140, -140, -171, 2652, by decide⟩, -- source row 2095
  pairEntry 26 27 (by decide) ⟨171, -140, 0, 0, 1326, by decide⟩ -- source row 2106
]

end Option2.NativeStress.NativeT

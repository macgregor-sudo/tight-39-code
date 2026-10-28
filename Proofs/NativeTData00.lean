module

public import NativeHWeights

@[expose] public section

/-! Exact source λ42; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda42 : List Entry := [
  idEntry 1 0 ⟨48597, -34296, -57160, -80995, 1034280, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-48597, 34296, 57160, 80995, 1034280, by decide⟩, -- source row 28
  idEntry 1 2 ⟨48597, -34296, -57160, -80995, 1034280, by decide⟩, -- source row 29
  idEntry 1 11 ⟨-943, -576, 0, 0, 2210, by decide⟩, -- source row 38
  idEntry 1 12 ⟨576, -943, 0, 0, 2210, by decide⟩, -- source row 39
  idEntry 2 0 ⟨-985, 4730, -2758, 13244, 86190, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-985, 4730, -2758, 13244, 86190, by decide⟩, -- source row 55
  idEntry 2 2 ⟨985, -4730, 2758, -13244, 86190, by decide⟩, -- source row 56
  idEntry 2 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 57
  idEntry 2 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 58
  idEntry 3 0 ⟨-197, 946, 0, 0, 8619, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-38747, -13004, 0, 0, 86190, by decide⟩, -- source row 82
  idEntry 3 2 ⟨288959, 5888, 22464, -36777, 344760, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-126091, 8288, -22464, 36777, 344760, by decide⟩, -- source row 84
  idEntry 3 4 ⟨-34296, -48597, 40717, 3544, 344760, by decide⟩, -- source row 85
  idEntry 4 0 ⟨985, -4730, -19706, 23533, 172380, by decide⟩, -- source row 108
  idEntry 4 1 ⟨18881, 8867, 1379, -6622, 86190, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-38747, -13004, 16948, -10289, 172380, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-40717, -3544, 11432, 16199, 114920, by decide⟩, -- source row 111
  idEntry 4 4 ⟨135984, -13137, 44657, -15376, 344760, by decide⟩, -- source row 112
  idEntry 5 0 ⟨985, -4730, 10246, -25503, 172380, by decide⟩, -- source row 135
  idEntry 5 1 ⟨18881, 8867, -6109, 5637, 86190, by decide⟩, -- source row 136
  idEntry 5 2 ⟨-39929, -7328, 80, 13835, 68952, by decide⟩, -- source row 137
  idEntry 5 3 ⟨-122151, -10632, -41384, 32837, 344760, by decide⟩, -- source row 138
  idEntry 5 4 ⟨576, -943, 943, 576, 8840, by decide⟩, -- source row 139
  idEntry 6 0 ⟨-116241, -39012, 28780, 75085, 517140, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-2955, 14190, -19306, 92708, 258570, by decide⟩, -- source row 163
  idEntry 6 2 ⟨36777, 22464, -11432, -16199, 172380, by decide⟩, -- source row 164
  idEntry 6 3 ⟨14775, -70950, 31538, 61841, 258570, by decide⟩, -- source row 165
  idEntry 6 4 ⟨-30738, 76509, -985, 4730, 86190, by decide⟩, -- source row 166
  idEntry 7 0 ⟨348723, 117036, -38212, 254591, 1034280, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-92601, -152532, -38212, 254591, 1034280, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-128061, 17748, -6716, -181037, 344760, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-110331, -67392, 87856, -492983, 517140, by decide⟩, -- source row 192
  idEntry 7 4 ⟨-11432, -16199, -40717, -3544, 172380, by decide⟩, -- source row 193
  idEntry 8 0 ⟨-92601, -152532, 4316, -234013, 1034280, by decide⟩, -- source row 216
  idEntry 8 1 ⟨128061, -17748, 139100, -454675, 1034280, by decide⟩, -- source row 217
  idEntry 8 2 ⟨10289, 16948, 1972, 14229, 114920, by decide⟩, -- source row 218
  idEntry 8 3 ⟨110331, 67392, -23264, -101573, 517140, by decide⟩, -- source row 219
  idEntry 8 4 ⟨-400, -69175, -36777, -22464, 172380, by decide⟩, -- source row 220
  idEntry 9 0 ⟨16911, 18327, -9653, 46354, 129285, by decide⟩, -- source row 243
  idEntry 9 1 ⟨35595, 28140, 5756, 15017, 103428, by decide⟩, -- source row 244
  idEntry 9 2 ⟨-23533, -19706, -4730, -985, 57460, by decide⟩, -- source row 245
  idEntry 9 3 ⟨535563, 215166, 3958, 194281, 517140, by decide⟩, -- source row 246
  idEntry 9 4 ⟨-18906, 161883, -985, 4730, 172380, by decide⟩, -- source row 247
  idEntry 10 0 ⟨-16911, -18327, 15569, -3667, 258570, by decide⟩, -- source row 270
  idEntry 10 1 ⟨76509, 30738, -36254, 102997, 517140, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-19866, -4137, 1379, -6622, 86190, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-144153, -104046, 63034, -373787, 517140, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-24422, 188371, 25503, 10246, 172380, by decide⟩, -- source row 274
  idEntry 11 0 ⟨36777, 22464, -400, -69175, 258570, by decide⟩, -- source row 297
  idEntry 11 1 ⟨-73554, -44928, -400, -69175, 258570, by decide⟩, -- source row 298
  idEntry 11 2 ⟨2955, -14190, 19706, -23533, 172380, by decide⟩, -- source row 299
  idEntry 11 3 ⟨-138243, -132426, 58318, -208949, 517140, by decide⟩, -- source row 300
  idEntry 11 4 ⟨-8674, -29443, -29443, 8674, 172380, by decide⟩, -- source row 301
  idEntry 12 0 ⟨-207, 736, -72, 256, 2210, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-207, 736, -72, 256, 2210, by decide⟩, -- source row 325
  idEntry 12 2 ⟨621, -2208, 216, -768, 2210, by decide⟩, -- source row 326
  idEntry 12 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 327
  idEntry 12 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 328
  idEntry 12 5 ⟨414, -1472, 144, -512, 1105, by decide⟩, -- source row 329
  idEntry 12 9 ⟨-81, 288, 0, 0, 1105, by decide⟩, -- source row 333
  idEntry 12 10 ⟨288, -1024, 0, 0, 1105, by decide⟩, -- source row 334
  idEntry 13 0 ⟨-207, 736, 72, -256, 2210, by decide⟩, -- source row 351
  idEntry 13 1 ⟨-207, 736, 72, -256, 2210, by decide⟩, -- source row 352
  idEntry 13 2 ⟨621, -2208, -216, 768, 2210, by decide⟩, -- source row 353
  idEntry 13 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 354
  idEntry 13 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 355
  idEntry 13 5 ⟨-207, 736, 72, -256, 1105, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-216, 768, 207, -736, 1105, by decide⟩, -- source row 357
  idEntry 13 9 ⟨81, -288, 288, -1024, 2210, by decide⟩, -- source row 360
  idEntry 13 10 ⟨-288, 1024, 81, -288, 2210, by decide⟩, -- source row 361
  idEntry 14 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 381
  idEntry 14 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 382
  idEntry 14 9 ⟨81, -288, -288, 1024, 2210, by decide⟩, -- source row 387
  idEntry 14 10 ⟨-288, 1024, -81, 288, 2210, by decide⟩, -- source row 388
  idEntry 15 0 ⟨-384, -108, -36, 128, 1105, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-384, -108, -36, 128, 1105, by decide⟩, -- source row 406
  idEntry 15 2 ⟨1152, 324, 108, -384, 1105, by decide⟩, -- source row 407
  idEntry 15 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 408
  idEntry 15 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 409
  idEntry 15 5 ⟨1536, 432, 144, -512, 1105, by decide⟩, -- source row 410
  idEntry 15 9 ⟨-3153, -576, -576, 943, 4420, by decide⟩, -- source row 414
  idEntry 15 10 ⟨-576, -1267, 943, 576, 4420, by decide⟩, -- source row 415
  idEntry 16 0 ⟨-975, 520, -808, 49, 4420, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-975, 520, -808, 49, 4420, by decide⟩, -- source row 433
  idEntry 16 2 ⟨2925, -1560, 2424, -147, 4420, by decide⟩, -- source row 434
  idEntry 16 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 435
  idEntry 16 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 436
  idEntry 16 5 ⟨-975, 520, -808, 49, 2210, by decide⟩, -- source row 437
  idEntry 16 6 ⟨2424, -147, 975, -520, 2210, by decide⟩, -- source row 438
  idEntry 16 9 ⟨2991, 1152, 0, -1105, 4420, by decide⟩, -- source row 441
  idEntry 16 10 ⟨1152, -781, 1105, 0, 4420, by decide⟩, -- source row 442
  idEntry 17 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 462
  idEntry 17 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 463
  idEntry 17 9 ⟨81, -288, 288, 81, 2210, by decide⟩, -- source row 468
  idEntry 17 10 ⟨-144, 512, -512, -144, 1105, by decide⟩, -- source row 469
  idEntry 18 0 ⟨-975, 520, 808, -49, 4420, by decide⟩, -- source row 486
  idEntry 18 1 ⟨-975, 520, 808, -49, 4420, by decide⟩, -- source row 487
  idEntry 18 2 ⟨2925, -1560, -2424, 147, 4420, by decide⟩, -- source row 488
  idEntry 18 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 489
  idEntry 18 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 490
  idEntry 18 5 ⟨975, -520, -808, 49, 1105, by decide⟩, -- source row 491
  idEntry 18 9 ⟨-3153, -576, 576, -943, 4420, by decide⟩, -- source row 495
  idEntry 18 10 ⟨-576, -1267, -943, -576, 4420, by decide⟩, -- source row 496
  idEntry 19 0 ⟨-384, -108, 36, -128, 1105, by decide⟩, -- source row 513
  idEntry 19 1 ⟨-384, -108, 36, -128, 1105, by decide⟩, -- source row 514
  idEntry 19 2 ⟨1152, 324, -108, 384, 1105, by decide⟩, -- source row 515
  idEntry 19 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 516
  idEntry 19 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 517
  idEntry 19 5 ⟨-768, -216, 72, -256, 1105, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-216, 768, 768, 216, 1105, by decide⟩, -- source row 519
  idEntry 19 9 ⟨81, -288, -288, -81, 2210, by decide⟩, -- source row 522
  idEntry 19 10 ⟨-144, 512, 512, 144, 1105, by decide⟩, -- source row 523
  idEntry 20 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 543
  idEntry 20 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 544
  idEntry 20 9 ⟨2991, 1152, 0, 1105, 4420, by decide⟩, -- source row 549
  idEntry 20 10 ⟨1152, -781, -1105, 0, 4420, by decide⟩, -- source row 550
  idEntry 21 0 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 567
  idEntry 21 1 ⟨-45, 24, -8, -15, 204, by decide⟩, -- source row 568
  idEntry 21 2 ⟨45, -24, 8, 15, 68, by decide⟩, -- source row 569
  idEntry 21 3 ⟨837, -116, 0, 0, 845, by decide⟩, -- source row 570
  idEntry 21 4 ⟨116, 837, 0, 0, 845, by decide⟩, -- source row 571
  idEntry 21 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 572
  idEntry 21 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 573
  idEntry 21 7 ⟨45, -24, 8, 15, 85, by decide⟩, -- source row 574
  idEntry 21 8 ⟨180, -96, 32, 60, 255, by decide⟩, -- source row 575
  idEntry 22 0 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 594
  idEntry 22 1 ⟨-45, 24, 8, 15, 204, by decide⟩, -- source row 595
  idEntry 22 2 ⟨45, -24, -8, -15, 68, by decide⟩, -- source row 596
  idEntry 22 3 ⟨837, -116, 0, 0, 845, by decide⟩, -- source row 597
  idEntry 22 4 ⟨116, 837, 0, 0, 845, by decide⟩, -- source row 598
  idEntry 22 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 599
  idEntry 22 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 600
  idEntry 22 7 ⟨-13, 84, -52, 47, 170, by decide⟩, -- source row 601
  idEntry 22 8 ⟨-252, -39, 167, -12, 510, by decide⟩, -- source row 602
  idEntry 23 3 ⟨837, -116, 0, 0, 845, by decide⟩, -- source row 624
  idEntry 23 4 ⟨116, 837, 0, 0, 845, by decide⟩, -- source row 625
  idEntry 23 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 626
  idEntry 23 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 627
  idEntry 24 0 ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 648
  idEntry 24 1 ⟨45, -24, -8, -15, 204, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-45, 24, 8, 15, 68, by decide⟩, -- source row 650
  idEntry 24 3 ⟨837, -116, 116, 837, 3380, by decide⟩, -- source row 651
  idEntry 24 4 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 652
  idEntry 24 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 653
  idEntry 24 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 654
  idEntry 24 7 ⟨-45, 24, 8, 15, 85, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-180, 96, 32, 60, 255, by decide⟩, -- source row 656
  idEntry 25 0 ⟨0, 0, -8, -15, 102, by decide⟩, -- source row 675
  idEntry 25 1 ⟨0, 0, -8, -15, 102, by decide⟩, -- source row 676
  idEntry 25 2 ⟨0, 0, 8, 15, 34, by decide⟩, -- source row 677
  idEntry 25 3 ⟨837, -116, 116, 837, 3380, by decide⟩, -- source row 678
  idEntry 25 4 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 679
  idEntry 25 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 680
  idEntry 25 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 681
  idEntry 25 7 ⟨-32, -60, -8, -15, 85, by decide⟩, -- source row 682
  idEntry 25 8 ⟨72, 135, -32, -60, 255, by decide⟩, -- source row 683
  idEntry 26 3 ⟨837, -116, 116, 837, 3380, by decide⟩, -- source row 705
  idEntry 26 4 ⟨116, 837, -837, 116, 3380, by decide⟩, -- source row 706
  idEntry 26 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 707
  idEntry 26 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 708
  idEntry 27 0 ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 729
  idEntry 27 1 ⟨0, 0, 8, 15, 102, by decide⟩, -- source row 730
  idEntry 27 2 ⟨0, 0, -8, -15, 34, by decide⟩, -- source row 731
  idEntry 27 3 ⟨837, -116, -116, -837, 3380, by decide⟩, -- source row 732
  idEntry 27 4 ⟨116, 837, 837, -116, 3380, by decide⟩, -- source row 733
  idEntry 27 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 734
  idEntry 27 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 735
  idEntry 27 7 ⟨0, 0, -16, -30, 85, by decide⟩, -- source row 736
  idEntry 27 8 ⟨0, 0, -64, -120, 255, by decide⟩, -- source row 737
  idEntry 28 0 ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 756
  idEntry 28 1 ⟨45, -24, 8, 15, 204, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-45, 24, -8, -15, 68, by decide⟩, -- source row 758
  idEntry 28 3 ⟨837, -116, -116, -837, 3380, by decide⟩, -- source row 759
  idEntry 28 4 ⟨116, 837, 837, -116, 3380, by decide⟩, -- source row 760
  idEntry 28 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 761
  idEntry 28 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 762
  idEntry 28 7 ⟨77, 36, 68, -17, 170, by decide⟩, -- source row 763
  idEntry 28 8 ⟨108, -231, -103, 132, 510, by decide⟩, -- source row 764
  idEntry 29 3 ⟨837, -116, -116, -837, 3380, by decide⟩, -- source row 786
  idEntry 29 4 ⟨116, 837, 837, -116, 3380, by decide⟩, -- source row 787
  idEntry 29 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 788
  idEntry 29 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 789
  idEntry 30 0 ⟨-8640, 4200, -1400, -2880, 19227, by decide⟩, -- source row 810
  idEntry 30 1 ⟨-8640, 4200, -1400, -2880, 19227, by decide⟩, -- source row 811
  idEntry 30 2 ⟨8640, -4200, 1400, 2880, 6409, by decide⟩, -- source row 812
  idEntry 30 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 813
  idEntry 30 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 814
  idEntry 30 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 815
  idEntry 30 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 816
  idEntry 30 7 ⟨-427, 1836, 0, 0, 3770, by decide⟩, -- source row 817
  idEntry 30 8 ⟨-1836, -427, 0, 0, 3770, by decide⟩, -- source row 818
  idEntry 30 9 ⟨172800, -84000, 28000, 57600, 108953, by decide⟩, -- source row 819
  idEntry 30 10 ⟨-276480, 134400, -44800, -92160, 326859, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-8640, 4200, 1400, 2880, 19227, by decide⟩, -- source row 837
  idEntry 31 1 ⟨-8640, 4200, 1400, 2880, 19227, by decide⟩, -- source row 838
  idEntry 31 2 ⟨8640, -4200, -1400, -2880, 6409, by decide⟩, -- source row 839
  idEntry 31 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 840
  idEntry 31 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 841
  idEntry 31 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 842
  idEntry 31 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 843
  idEntry 31 7 ⟨427, -1836, 1836, 427, 7540, by decide⟩, -- source row 844
  idEntry 31 8 ⟨1836, 427, -427, 1836, 7540, by decide⟩, -- source row 845
  idEntry 31 9 ⟨-64000, 88080, -32080, 51200, 108953, by decide⟩, -- source row 846
  idEntry 31 10 ⟨264240, 192000, -281600, 79920, 326859, by decide⟩, -- source row 847
  idEntry 32 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 867
  idEntry 32 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 868
  idEntry 32 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 869
  idEntry 32 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 870
  idEntry 32 7 ⟨427, -1836, -1836, -427, 7540, by decide⟩, -- source row 871
  idEntry 32 8 ⟨1836, 427, 427, -1836, 7540, by decide⟩, -- source row 872
  idEntry 33 0 ⟨315, 648, -2800, -5760, 38454, by decide⟩, -- source row 891
  idEntry 33 1 ⟨315, 648, -2800, -5760, 38454, by decide⟩, -- source row 892
  idEntry 33 2 ⟨-315, -648, 2800, 5760, 12818, by decide⟩, -- source row 893
  idEntry 33 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 894
  idEntry 33 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 895
  idEntry 33 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 896
  idEntry 33 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 897
  idEntry 33 7 ⟨427, -1836, -1836, -427, 7540, by decide⟩, -- source row 898
  idEntry 33 8 ⟨1836, 427, 427, -1836, 7540, by decide⟩, -- source row 899
  idEntry 33 9 ⟨-3150, -6480, 28000, 57600, 108953, by decide⟩, -- source row 900
  idEntry 33 10 ⟨5040, 10368, -44800, -92160, 326859, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-16965, 9048, -2152, -6075, 76908, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-16965, 9048, -2152, -6075, 76908, by decide⟩, -- source row 919
  idEntry 34 2 ⟨16965, -9048, 2152, 6075, 25636, by decide⟩, -- source row 920
  idEntry 34 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 921
  idEntry 34 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 922
  idEntry 34 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 923
  idEntry 34 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 924
  idEntry 34 7 ⟨-427, 1836, 0, 0, 3770, by decide⟩, -- source row 925
  idEntry 34 8 ⟨-1836, -427, 0, 0, 3770, by decide⟩, -- source row 926
  idEntry 34 9 ⟨-102041, -3360, -56000, -6247, 217906, by decide⟩, -- source row 927
  idEntry 34 10 ⟨38880, -345759, -237259, 184320, 653718, by decide⟩, -- source row 928
  idEntry 35 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 948
  idEntry 35 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 949
  idEntry 35 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 950
  idEntry 35 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 951
  idEntry 35 7 ⟨427, -1836, 1836, 427, 7540, by decide⟩, -- source row 952
  idEntry 35 8 ⟨1836, 427, -427, 1836, 7540, by decide⟩, -- source row 953
  idEntry 36 0 ⟨-16965, 9048, 2152, 6075, 76908, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-16965, 9048, 2152, 6075, 76908, by decide⟩, -- source row 973
  idEntry 36 2 ⟨16965, -9048, -2152, -6075, 25636, by decide⟩, -- source row 974
  idEntry 36 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 975
  idEntry 36 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 976
  idEntry 36 5 ⟨-15, 8, 0, 0, 34, by decide⟩, -- source row 977
  idEntry 36 6 ⟨-8, -15, 0, 0, 34, by decide⟩, -- source row 978
  idEntry 36 7 ⟨427, -1836, 1836, 427, 7540, by decide⟩, -- source row 979
  idEntry 36 8 ⟨1836, 427, -427, 1836, 7540, by decide⟩, -- source row 980
  idEntry 36 9 ⟨84825, -45240, -10760, -30375, 108953, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-135720, 72384, 17216, 48600, 326859, by decide⟩, -- source row 982
  idEntry 37 0 ⟨315, 648, 2800, 5760, 38454, by decide⟩, -- source row 999
  idEntry 37 1 ⟨315, 648, 2800, 5760, 38454, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨-315, -648, -2800, -5760, 12818, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 1003
  idEntry 37 5 ⟨15, -8, 8, 15, 68, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨8, 15, -15, 8, 68, by decide⟩, -- source row 1005
  idEntry 37 7 ⟨427, -1836, -1836, -427, 7540, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨1836, 427, 427, -1836, 7540, by decide⟩, -- source row 1007
  idEntry 37 9 ⟨23975, 49320, 14840, 30528, 108953, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨123480, 254016, -17675, -36360, 326859, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨837, -116, 0, 0, 1690, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨116, 837, 0, 0, 1690, by decide⟩, -- source row 1030
  idEntry 38 5 ⟨15, -8, -8, -15, 68, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨8, 15, 15, -8, 68, by decide⟩, -- source row 1032
  idEntry 38 7 ⟨-427, 1836, 0, 0, 3770, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨-1836, -427, 0, 0, 3770, by decide⟩, -- source row 1034
  sumEntry 0 3 ⟨19866, 4137, -6895, 33110, 86190, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨-35454, 241347, 985, -4730, 517140, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨-38747, -13004, 24036, -91723, 344760, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨39012, -116241, 120181, 20092, 1034280, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨42687, -5916, 16948, -10289, 1034280, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨59598, 12411, 12811, 9577, 258570, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨36777, 22464, 11432, 16199, 517140, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨76509, 30738, 8674, 29443, 517140, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨2838, 591, -197, 946, 103428, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨-360543, -60276, -16948, 10289, 1034280, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨119436, 66327, -46627, 24836, 1034280, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨-42687, 5916, -16948, 10289, 258570, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨-5916, -42687, 38747, 13004, 517140, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨-54507, 62676, -50044, 169217, 1034280, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨-201615, -27180, -50044, 169217, 1034280, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 2758, -13244, 129285, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨2955, -14190, 11032, -52976, 129285, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨-2758, 13244, 0, 0, 43095, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨-36777, -22464, 11432, 16199, 258570, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨-42687, 5916, -61076, 222193, 517140, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨16948, -10289, 14229, -1972, 172380, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨19866, 4137, -1379, 6622, 258570, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨-8865, 42570, 8674, 29443, 517140, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨2955, -14190, -25222, 50021, 517140, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨-21563, -29166, 11818, -80449, 172380, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨3158, 55931, -985, 4730, 172380, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨-6622, -1379, -6895, 33110, 86190, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨1379, -6622, -6622, -1379, 86190, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨1379, -6622, -6622, -1379, 43095, by decide⟩, -- source row 1193
  sumEntry 4 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1204
  sumEntry 4 9 ⟨81, -288, -288, 1024, 6630, by decide⟩, -- source row 1209
  sumEntry 4 10 ⟨-288, 1024, -81, 288, 6630, by decide⟩, -- source row 1210
  sumEntry 4 11 ⟨27, -96, 0, 0, 1105, by decide⟩, -- source row 1211
  sumEntry 4 12 ⟨288, -1024, 0, 0, 3315, by decide⟩, -- source row 1212
  sumEntry 4 17 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨116, 837, 837, -116, 10140, by decide⟩, -- source row 1218
  sumEntry 4 21 ⟨81, -288, 288, -1024, 6630, by decide⟩, -- source row 1221
  sumEntry 4 22 ⟨-288, 1024, 81, -288, 6630, by decide⟩, -- source row 1222
  sumEntry 4 23 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1231
  sumEntry 5 9 ⟨27, -96, 96, 27, 2210, by decide⟩, -- source row 1236
  sumEntry 5 10 ⟨-144, 512, -512, -144, 3315, by decide⟩, -- source row 1237
  sumEntry 5 11 ⟨-2991, -1152, 0, 1105, 13260, by decide⟩, -- source row 1238
  sumEntry 5 12 ⟨1152, -781, 1105, 0, 13260, by decide⟩, -- source row 1239
  sumEntry 5 17 ⟨-837, 116, -116, -837, 10140, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1245
  sumEntry 5 21 ⟨27, -96, 96, 27, 2210, by decide⟩, -- source row 1248
  sumEntry 5 22 ⟨-144, 512, -512, -144, 3315, by decide⟩, -- source row 1249
  sumEntry 5 23 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨-116, -837, 0, 0, 5070, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1258
  sumEntry 6 9 ⟨2991, 1152, 0, 1105, 13260, by decide⟩, -- source row 1263
  sumEntry 6 10 ⟨1152, -781, -1105, 0, 13260, by decide⟩, -- source row 1264
  sumEntry 6 11 ⟨-2991, -1152, 0, -1105, 13260, by decide⟩, -- source row 1265
  sumEntry 6 12 ⟨1152, -781, -1105, 0, 13260, by decide⟩, -- source row 1266
  sumEntry 6 17 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨-116, -837, 0, 0, 5070, by decide⟩, -- source row 1272
  sumEntry 6 21 ⟨-3153, -576, 576, -943, 13260, by decide⟩, -- source row 1275
  sumEntry 6 22 ⟨-576, -1267, -943, -576, 13260, by decide⟩, -- source row 1276
  sumEntry 6 23 ⟨-837, 116, 116, 837, 10140, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨116, 837, 837, -116, 10140, by decide⟩, -- source row 1278
  sumEntry 7 3 ⟨837, -116, 0, 0, 2535, by decide⟩, -- source row 1284
  sumEntry 7 4 ⟨116, 837, 0, 0, 2535, by decide⟩, -- source row 1285
  sumEntry 7 5 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1286
  sumEntry 7 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1287
  sumEntry 7 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1292
  sumEntry 7 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1293
  sumEntry 7 13 ⟨5, -12, -12, -5, 78, by decide⟩, -- source row 1294
  sumEntry 7 14 ⟨12, 5, 5, -12, 78, by decide⟩, -- source row 1295
  sumEntry 7 23 ⟨-21, -220, 220, -21, 2652, by decide⟩, -- source row 1304
  sumEntry 7 24 ⟨-220, 21, -21, -220, 2652, by decide⟩, -- source row 1305
  sumEntry 7 25 ⟨-33, -56, 56, -33, 390, by decide⟩, -- source row 1306
  sumEntry 7 26 ⟨56, -33, 33, 56, 390, by decide⟩, -- source row 1307
  sumEntry 8 3 ⟨837, -116, 116, 837, 10140, by decide⟩, -- source row 1311
  sumEntry 8 4 ⟨116, 837, -837, 116, 10140, by decide⟩, -- source row 1312
  sumEntry 8 5 ⟨15, -8, 8, 15, 204, by decide⟩, -- source row 1313
  sumEntry 8 6 ⟨8, 15, -15, 8, 204, by decide⟩, -- source row 1314
  sumEntry 8 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1319
  sumEntry 8 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1320
  sumEntry 8 13 ⟨-5, 12, 12, 5, 156, by decide⟩, -- source row 1321
  sumEntry 8 14 ⟨-12, -5, -5, 12, 156, by decide⟩, -- source row 1322
  sumEntry 8 23 ⟨-21, -220, 220, -21, 2652, by decide⟩, -- source row 1331
  sumEntry 8 24 ⟨-220, 21, -21, -220, 2652, by decide⟩, -- source row 1332
  sumEntry 8 25 ⟨33, 56, -56, 33, 780, by decide⟩, -- source row 1333
  sumEntry 8 26 ⟨-56, 33, -33, -56, 780, by decide⟩, -- source row 1334
  sumEntry 9 3 ⟨837, -116, -116, -837, 10140, by decide⟩, -- source row 1338
  sumEntry 9 4 ⟨116, 837, 837, -116, 10140, by decide⟩, -- source row 1339
  sumEntry 9 5 ⟨-15, 8, 0, 0, 102, by decide⟩, -- source row 1340
  sumEntry 9 6 ⟨-8, -15, 0, 0, 102, by decide⟩, -- source row 1341
  sumEntry 9 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1346
  sumEntry 9 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1347
  sumEntry 9 13 ⟨-5, 12, 12, 5, 156, by decide⟩, -- source row 1348
  sumEntry 9 14 ⟨-12, -5, -5, 12, 156, by decide⟩, -- source row 1349
  sumEntry 9 23 ⟨-21, -220, 220, -21, 2652, by decide⟩, -- source row 1358
  sumEntry 9 24 ⟨-220, 21, -21, -220, 2652, by decide⟩, -- source row 1359
  sumEntry 9 25 ⟨33, 56, -56, 33, 780, by decide⟩, -- source row 1360
  sumEntry 9 26 ⟨-56, 33, -33, -56, 780, by decide⟩, -- source row 1361
  sumEntry 10 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1366
  sumEntry 10 5 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1368
  sumEntry 10 7 ⟨427, -1836, -1836, -427, 22620, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨1836, 427, 427, -1836, 22620, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1374
  sumEntry 10 15 ⟨-184023, -373736, -373736, 184023, 4999020, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨373736, -184023, -184023, -373736, 4999020, by decide⟩, -- source row 1378
  sumEntry 10 17 ⟨21, 20, -20, 21, 348, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨-20, 21, -21, -20, 348, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨-475, -132, 0, 0, 2958, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨132, -475, 0, 0, 2958, by decide⟩, -- source row 1382
  sumEntry 10 21 ⟨-19897, -14304, 14304, -19897, 294060, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨-14304, 19897, -19897, -14304, 294060, by decide⟩, -- source row 1384
  sumEntry 10 25 ⟨-33, -56, 56, -33, 780, by decide⟩, -- source row 1387
  sumEntry 10 26 ⟨56, -33, 33, 56, 780, by decide⟩, -- source row 1388
  sumEntry 11 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1393
  sumEntry 11 5 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1395
  sumEntry 11 7 ⟨427, -1836, 1836, 427, 22620, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨1836, 427, -427, 1836, 22620, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1401
  sumEntry 11 15 ⟨-184023, -373736, 373736, -184023, 4999020, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨373736, -184023, 184023, 373736, 4999020, by decide⟩, -- source row 1405
  sumEntry 11 17 ⟨-21, -20, 0, 0, 174, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨20, -21, 0, 0, 174, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨475, 132, 132, -475, 5916, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨-132, 475, 475, 132, 5916, by decide⟩, -- source row 1409
  sumEntry 11 21 ⟨19897, 14304, 0, 0, 147030, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨14304, -19897, 0, 0, 147030, by decide⟩, -- source row 1411
  sumEntry 11 25 ⟨-33, -56, 56, -33, 780, by decide⟩, -- source row 1414
  sumEntry 11 26 ⟨56, -33, 33, 56, 780, by decide⟩, -- source row 1415
  sumEntry 12 3 ⟨837, -116, 0, 0, 5070, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨116, 837, 0, 0, 5070, by decide⟩, -- source row 1420
  sumEntry 12 5 ⟨15, -8, -8, -15, 204, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨8, 15, 15, -8, 204, by decide⟩, -- source row 1422
  sumEntry 12 7 ⟨-427, 1836, 0, 0, 11310, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨-1836, -427, 0, 0, 11310, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨-943, -576, 0, 0, 6630, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨576, -943, 0, 0, 6630, by decide⟩, -- source row 1428
  sumEntry 12 15 ⟨184023, 373736, 0, 0, 2499510, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨-373736, 184023, 0, 0, 2499510, by decide⟩, -- source row 1432
  sumEntry 12 17 ⟨21, 20, 20, -21, 348, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨-20, 21, 21, 20, 348, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨475, 132, -132, 475, 5916, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨-132, 475, -475, -132, 5916, by decide⟩, -- source row 1436
  sumEntry 12 21 ⟨-19897, -14304, -14304, 19897, 294060, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨-14304, 19897, 19897, 14304, 294060, by decide⟩, -- source row 1438
  sumEntry 12 25 ⟨-33, -56, 56, -33, 780, by decide⟩, -- source row 1441
  sumEntry 12 26 ⟨56, -33, 33, 56, 780, by decide⟩, -- source row 1442
  pairEntry 0 4 (by decide) ⟨40717, 3544, -3544, 40717, 344760, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 2758, -13244, 43095, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨38747, 13004, -1972, -14229, 344760, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨-19866, -4137, 1379, -6622, 86190, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, -2758, 13244, 43095, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨-114271, -48472, -11432, -16199, 344760, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨-40717, -3544, -26408, 8319, 344760, by decide⟩, -- source row 1484
  pairEntry 1 6 (by decide) ⟨36777, 22464, 3544, -40717, 172380, by decide⟩, -- source row 1485
  pairEntry 1 8 (by decide) ⟨112301, 57932, 13004, -38747, 344760, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨-16911, -18327, 9653, -46354, 258570, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨42687, -5916, -33496, 89753, 258570, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨-24957, -79224, -11432, -16199, 517140, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨46627, -24836, -1972, -14229, 344760, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨197, -946, -946, -197, 34476, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨-38747, -13004, 1972, 14229, 344760, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨38747, 13004, -1972, -14229, 344760, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨-46627, 24836, -27980, 63265, 344760, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨-985, 4730, -2758, 13244, 43095, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨985, -4730, 10246, -25503, 172380, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨-985, 4730, -2758, 13244, 86190, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨-197, 946, 946, 197, 17238, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨38747, 13004, -1972, -14229, 344760, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨38747, 13004, -1972, -14229, 344760, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨197, -946, -946, -197, 34476, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨-197, 946, 946, 197, 17238, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨-38747, -13004, 1972, 14229, 344760, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨42687, -5916, 16948, -10289, 344760, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨-19866, -4137, 1379, -6622, 86190, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨-40717, -3544, 7488, -12259, 172380, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨-42687, 5916, -16948, 10289, 344760, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨-38747, -13004, 1972, 14229, 344760, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨-18881, -8867, -3351, -7607, 86190, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, -2758, 13244, 43095, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨985, -4730, 8274, -39732, 86190, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨985, -4730, 2758, -13244, 43095, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨985, -4730, 2758, -13244, 43095, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨985, -4730, 2758, -13244, 86190, by decide⟩, -- source row 1721
  pairEntry 12 21 (by decide) ⟨-49, -808, 0, 0, 2210, by decide⟩, -- source row 1841
  pairEntry 12 22 (by decide) ⟨-147, -2424, 1384, -2097, 13260, by decide⟩, -- source row 1842
  pairEntry 12 24 (by decide) ⟨147, 2424, 520, 975, 13260, by decide⟩, -- source row 1844
  pairEntry 12 25 (by decide) ⟨128, 36, -36, 128, 1105, by decide⟩, -- source row 1845
  pairEntry 12 27 (by decide) ⟨147, 2424, -520, -975, 13260, by decide⟩, -- source row 1847
  pairEntry 12 28 (by decide) ⟨-1389, 1992, -952, 561, 13260, by decide⟩, -- source row 1848
  pairEntry 12 30 (by decide) ⟨-1863, -61912, 0, 0, 166634, by decide⟩, -- source row 1850
  pairEntry 12 31 (by decide) ⟨-27945, -928680, -210872, -395049, 4999020, by decide⟩, -- source row 1851
  pairEntry 12 33 (by decide) ⟨496179, -736152, 373736, -184023, 4999020, by decide⟩, -- source row 1853
  pairEntry 12 34 (by decide) ⟨-5589, -185736, 107320, -152619, 999804, by decide⟩, -- source row 1854
  pairEntry 12 36 (by decide) ⟨496179, -736152, -373736, 184023, 4999020, by decide⟩, -- source row 1856
  pairEntry 12 37 (by decide) ⟨43677, 16044, 13572, -48256, 416585, by decide⟩, -- source row 1857
  pairEntry 13 21 (by decide) ⟨-147, -2424, -1384, 2097, 13260, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨-49, -808, 0, 0, 2210, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨-1389, 1992, 952, -561, 13260, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨147, 2424, 520, 975, 13260, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨128, 36, 36, -128, 1105, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨147, 2424, -520, -975, 13260, by decide⟩, -- source row 1873
  pairEntry 13 30 (by decide) ⟨-27945, -928680, 210872, 395049, 4999020, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨-1863, -61912, 0, 0, 166634, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨43677, 16044, -13572, 48256, 416585, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨496179, -736152, 373736, -184023, 4999020, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨-5589, -185736, -107320, 152619, 999804, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨496179, -736152, -373736, 184023, 4999020, by decide⟩, -- source row 1882
  pairEntry 15 21 (by decide) ⟨1536, 432, 952, -561, 6630, by decide⟩, -- source row 1913
  pairEntry 15 22 (by decide) ⟨3219, 3288, -520, -975, 13260, by decide⟩, -- source row 1914
  pairEntry 15 24 (by decide) ⟨-128, -36, -36, 128, 1105, by decide⟩, -- source row 1916
  pairEntry 15 25 (by decide) ⟨-147, -2424, 520, 975, 13260, by decide⟩, -- source row 1917
  pairEntry 15 27 (by decide) ⟨-768, -216, -736, -207, 6630, by decide⟩, -- source row 1919
  pairEntry 15 28 (by decide) ⟨-256, -72, 0, 0, 1105, by decide⟩, -- source row 1920
  pairEntry 15 30 (by decide) ⟨113067, 34056, 73264, -39552, 499902, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨101091, 24672, 29616, -91933, 833170, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨188445, 56760, -2472, -4579, 833170, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨231723, 253848, -39208, -73515, 999804, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨578601, -780648, 358904, -211497, 4999020, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨303273, 74016, -284888, -91776, 2499510, by decide⟩, -- source row 1929
  pairEntry 16 21 (by decide) ⟨-49, -808, 808, -49, 4420, by decide⟩, -- source row 1935
  pairEntry 16 22 (by decide) ⟨1536, 432, 952, -561, 6630, by decide⟩, -- source row 1936
  pairEntry 16 24 (by decide) ⟨-1389, 1992, -952, 561, 13260, by decide⟩, -- source row 1938
  pairEntry 16 25 (by decide) ⟨-128, -36, -36, 128, 1105, by decide⟩, -- source row 1939
  pairEntry 16 27 (by decide) ⟨768, 216, -736, -207, 6630, by decide⟩, -- source row 1941
  pairEntry 16 28 (by decide) ⟨-768, -216, -736, -207, 6630, by decide⟩, -- source row 1942
  pairEntry 16 30 (by decide) ⟨262062, 96264, 277472, 78039, 2499510, by decide⟩, -- source row 1944
  pairEntry 16 31 (by decide) ⟨113067, 34056, 73264, -39552, 499902, by decide⟩, -- source row 1945
  pairEntry 16 33 (by decide) ⟨-27945, -928680, 181208, 340101, 4999020, by decide⟩, -- source row 1947
  pairEntry 16 34 (by decide) ⟨188445, 56760, -2472, -4579, 833170, by decide⟩, -- source row 1948
  pairEntry 16 36 (by decide) ⟨-1863, -61912, 61912, -1863, 333268, by decide⟩, -- source row 1950
  pairEntry 16 37 (by decide) ⟨578601, -780648, 358904, -211497, 4999020, by decide⟩, -- source row 1951
  pairEntry 18 21 (by decide) ⟨1536, 432, -952, 561, 6630, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨-49, -808, -808, 49, 4420, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨-768, -216, 736, 207, 6630, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨768, 216, 736, 207, 6630, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨-128, -36, 36, -128, 1105, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨-1389, 1992, 952, -561, 13260, by decide⟩, -- source row 1983
  pairEntry 18 30 (by decide) ⟨113067, 34056, -73264, 39552, 499902, by decide⟩, -- source row 1985
  pairEntry 18 31 (by decide) ⟨262062, 96264, -277472, -78039, 2499510, by decide⟩, -- source row 1986
  pairEntry 18 33 (by decide) ⟨578601, -780648, -358904, 211497, 4999020, by decide⟩, -- source row 1988
  pairEntry 18 34 (by decide) ⟨-1863, -61912, -61912, 1863, 333268, by decide⟩, -- source row 1989
  pairEntry 18 36 (by decide) ⟨188445, 56760, 2472, 4579, 833170, by decide⟩, -- source row 1991
  pairEntry 18 37 (by decide) ⟨-27945, -928680, -181208, -340101, 4999020, by decide⟩, -- source row 1992
  pairEntry 19 21 (by decide) ⟨3219, 3288, 520, 975, 13260, by decide⟩, -- source row 1995
  pairEntry 19 22 (by decide) ⟨1536, 432, -952, 561, 6630, by decide⟩, -- source row 1996
  pairEntry 19 24 (by decide) ⟨-256, -72, 0, 0, 1105, by decide⟩, -- source row 1998
  pairEntry 19 25 (by decide) ⟨-768, -216, 736, 207, 6630, by decide⟩, -- source row 1999
  pairEntry 19 27 (by decide) ⟨-147, -2424, -520, -975, 13260, by decide⟩, -- source row 2001
  pairEntry 19 28 (by decide) ⟨-128, -36, 36, -128, 1105, by decide⟩, -- source row 2002
  pairEntry 19 30 (by decide) ⟨101091, 24672, -29616, 91933, 833170, by decide⟩, -- source row 2004
  pairEntry 19 31 (by decide) ⟨113067, 34056, -73264, 39552, 499902, by decide⟩, -- source row 2005
  pairEntry 19 33 (by decide) ⟨303273, 74016, 284888, 91776, 2499510, by decide⟩, -- source row 2007
  pairEntry 19 34 (by decide) ⟨578601, -780648, -358904, 211497, 4999020, by decide⟩, -- source row 2008
  pairEntry 19 36 (by decide) ⟨231723, 253848, 39208, 73515, 999804, by decide⟩, -- source row 2010
  pairEntry 19 37 (by decide) ⟨188445, 56760, 2472, 4579, 833170, by decide⟩, -- source row 2011
  pairEntry 21 30 (by decide) ⟨345, -152, 0, 0, 754, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨1035, -456, 152, 345, 4524, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨-345, 152, 152, 345, 1508, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨-1035, 456, 152, 345, 4524, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨-345, 152, -152, -345, 1508, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨0, 0, -152, -345, 2262, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨1035, -456, -152, -345, 4524, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨345, -152, 0, 0, 754, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨0, 0, 152, 345, 2262, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨-345, 152, 152, 345, 1508, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨-1035, 456, -152, -345, 4524, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨-345, 152, -152, -345, 1508, by decide⟩, -- source row 2062
  pairEntry 24 31 (by decide) ⟨0, 0, -152, -345, 2262, by decide⟩, -- source row 2085
  pairEntry 24 34 (by decide) ⟨1035, -456, 152, 345, 4524, by decide⟩, -- source row 2088
  pairEntry 24 37 (by decide) ⟨-1035, 456, 152, 345, 4524, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨0, 0, 152, 345, 2262, by decide⟩, -- source row 2097
  pairEntry 25 33 (by decide) ⟨-1035, 456, -152, -345, 4524, by decide⟩, -- source row 2100
  pairEntry 25 36 (by decide) ⟨1035, -456, -152, -345, 4524, by decide⟩, -- source row 2103
  pairEntry 27 31 (by decide) ⟨0, 0, -152, -345, 2262, by decide⟩, -- source row 2121
  pairEntry 27 34 (by decide) ⟨1035, -456, 152, 345, 4524, by decide⟩, -- source row 2124
  pairEntry 27 37 (by decide) ⟨-1035, 456, 152, 345, 4524, by decide⟩, -- source row 2127
  pairEntry 28 30 (by decide) ⟨0, 0, 152, 345, 2262, by decide⟩, -- source row 2130
  pairEntry 28 33 (by decide) ⟨-1035, 456, -152, -345, 4524, by decide⟩, -- source row 2133
  pairEntry 28 36 (by decide) ⟨1035, -456, -152, -345, 4524, by decide⟩ -- source row 2136
]

end Option2.NativeStress.NativeT

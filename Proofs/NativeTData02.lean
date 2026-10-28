module

public import NativeHWeights

@[expose] public section

/-! Exact source λ45; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda45 : List Entry := [
  idEntry 0 19 ⟨13167, 6156, 0, 0, 18785, by decide⟩, -- source row 19
  idEntry 0 20 ⟨-2156, -1008, 0, 0, 3757, by decide⟩, -- source row 20
  idEntry 1 0 ⟨-118503, -55404, -53900, -25200, 676260, by decide⟩, -- source row 27
  idEntry 1 1 ⟨118503, 55404, 53900, 25200, 676260, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-118503, -55404, -53900, -25200, 676260, by decide⟩, -- source row 29
  idEntry 2 0 ⟨-13167, -6156, -10780, -5040, 112710, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-13167, -6156, -10780, -5040, 112710, by decide⟩, -- source row 55
  idEntry 2 2 ⟨13167, 6156, 10780, 5040, 112710, by decide⟩, -- source row 56
  idEntry 3 0 ⟨8778, 4104, 0, 0, 18785, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-4389, -2052, 0, 0, 18785, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-48279, -22572, -10780, -5040, 75140, by decide⟩, -- source row 83
  idEntry 3 3 ⟨30723, 14364, 10780, 5040, 75140, by decide⟩, -- source row 84
  idEntry 3 4 ⟨-10780, -5040, -4389, -2052, 75140, by decide⟩, -- source row 85
  idEntry 4 0 ⟨-13167, -6156, 21560, 10080, 112710, by decide⟩, -- source row 108
  idEntry 4 1 ⟨13167, 6156, -5390, -2520, 56355, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-13167, -6156, -10780, -5040, 112710, by decide⟩, -- source row 110
  idEntry 4 3 ⟨13167, 6156, 10780, 5040, 75140, by decide⟩, -- source row 111
  idEntry 4 4 ⟨-2156, -1008, -4389, -2052, 15028, by decide⟩, -- source row 112
  idEntry 5 0 ⟨-13167, -6156, -21560, -10080, 112710, by decide⟩, -- source row 135
  idEntry 5 1 ⟨13167, 6156, 5390, 2520, 56355, by decide⟩, -- source row 136
  idEntry 5 2 ⟨13167, 6156, 53900, 25200, 225420, by decide⟩, -- source row 137
  idEntry 5 3 ⟨13167, 6156, 10780, 5040, 75140, by decide⟩, -- source row 138
  idEntry 5 4 ⟨-10780, -5040, 13167, 6156, 75140, by decide⟩, -- source row 139
  idEntry 6 0 ⟨-79002, -36936, 10780, 5040, 169065, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-39501, -18468, -75460, -35280, 338130, by decide⟩, -- source row 163
  idEntry 6 2 ⟨39501, 18468, -10780, -5040, 112710, by decide⟩, -- source row 164
  idEntry 6 3 ⟨-79002, -36936, -21560, -10080, 169065, by decide⟩, -- source row 165
  idEntry 6 4 ⟨-10780, -5040, 4389, 2052, 18785, by decide⟩, -- source row 166
  idEntry 7 0 ⟨-118503, -55404, -247940, -115920, 676260, by decide⟩, -- source row 189
  idEntry 7 1 ⟨118503, 55404, -53900, -25200, 676260, by decide⟩, -- source row 190
  idEntry 7 2 ⟨118503, 55404, 118580, 55440, 225420, by decide⟩, -- source row 191
  idEntry 7 3 ⟨118503, 55404, 247940, 115920, 338130, by decide⟩, -- source row 192
  idEntry 7 4 ⟨53900, 25200, 13167, 6156, 112710, by decide⟩, -- source row 193
  idEntry 8 0 ⟨355509, 166212, 140140, 65520, 676260, by decide⟩, -- source row 216
  idEntry 8 1 ⟨-118503, -55404, 140140, 65520, 676260, by decide⟩, -- source row 217
  idEntry 8 2 ⟨-39501, -18468, -10780, -5040, 75140, by decide⟩, -- source row 218
  idEntry 8 3 ⟨118503, 55404, -10780, -5040, 338130, by decide⟩, -- source row 219
  idEntry 8 4 ⟨75460, 35280, 39501, 18468, 112710, by decide⟩, -- source row 220
  idEntry 9 0 ⟨-39501, -18468, -21560, -10080, 169065, by decide⟩, -- source row 243
  idEntry 9 1 ⟨39501, 18468, 53900, 25200, 338130, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, -1078, -504, 3757, by decide⟩, -- source row 245
  idEntry 9 3 ⟨39501, 18468, 150920, 70560, 338130, by decide⟩, -- source row 246
  idEntry 9 4 ⟨-21560, -10080, 4389, 2052, 37570, by decide⟩, -- source row 247
  idEntry 10 0 ⟨79002, 36936, -5390, -2520, 169065, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-39501, -18468, -5390, -2520, 169065, by decide⟩, -- source row 271
  idEntry 10 2 ⟨0, 0, -1078, -504, 11271, by decide⟩, -- source row 272
  idEntry 10 3 ⟨39501, 18468, 86240, 40320, 338130, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-43120, -20160, 13167, 6156, 112710, by decide⟩, -- source row 274
  idEntry 11 0 ⟨-79002, -36936, 43120, 20160, 169065, by decide⟩, -- source row 297
  idEntry 11 1 ⟨-39501, -18468, -10780, -5040, 338130, by decide⟩, -- source row 298
  idEntry 11 2 ⟨39501, 18468, 5390, 2520, 56355, by decide⟩, -- source row 299
  idEntry 11 3 ⟨39501, 18468, 4312, 2016, 67626, by decide⟩, -- source row 300
  idEntry 11 4 ⟨-21560, -10080, -39501, -18468, 112710, by decide⟩, -- source row 301
  idEntry 12 0 ⟨-3619, -1692, -28336, -13248, 187850, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-3619, -1692, -28336, -13248, 187850, by decide⟩, -- source row 325
  idEntry 12 2 ⟨10857, 5076, 85008, 39744, 187850, by decide⟩, -- source row 326
  idEntry 12 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 327
  idEntry 12 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 328
  idEntry 12 5 ⟨7238, 3384, 56672, 26496, 93925, by decide⟩, -- source row 329
  idEntry 12 7 ⟨13167, 6156, 0, 0, 18785, by decide⟩, -- source row 331
  idEntry 12 8 ⟨-2156, -1008, 0, 0, 3757, by decide⟩, -- source row 332
  idEntry 13 0 ⟨-3619, -1692, 28336, 13248, 187850, by decide⟩, -- source row 351
  idEntry 13 1 ⟨-3619, -1692, 28336, 13248, 187850, by decide⟩, -- source row 352
  idEntry 13 2 ⟨10857, 5076, -85008, -39744, 187850, by decide⟩, -- source row 353
  idEntry 13 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 354
  idEntry 13 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 355
  idEntry 13 5 ⟨-3619, -1692, 28336, 13248, 93925, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-85008, -39744, 3619, 1692, 93925, by decide⟩, -- source row 357
  idEntry 13 7 ⟨-13167, -6156, 10780, 5040, 37570, by decide⟩, -- source row 358
  idEntry 13 8 ⟨10780, 5040, 13167, 6156, 37570, by decide⟩, -- source row 359
  idEntry 14 3 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 381
  idEntry 14 4 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 382
  idEntry 14 7 ⟨-13167, -6156, -10780, -5040, 37570, by decide⟩, -- source row 385
  idEntry 14 8 ⟨10780, 5040, -13167, -6156, 37570, by decide⟩, -- source row 386
  idEntry 15 0 ⟨0, 0, 28336, 13248, 93925, by decide⟩, -- source row 405
  idEntry 15 1 ⟨0, 0, 28336, 13248, 93925, by decide⟩, -- source row 406
  idEntry 15 2 ⟨0, 0, -85008, -39744, 93925, by decide⟩, -- source row 407
  idEntry 15 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 408
  idEntry 15 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 409
  idEntry 15 5 ⟨0, 0, -113344, -52992, 93925, by decide⟩, -- source row 410
  idEntry 15 7 ⟨-13167, -6156, 10780, 5040, 37570, by decide⟩, -- source row 412
  idEntry 15 8 ⟨10780, 5040, 13167, 6156, 37570, by decide⟩, -- source row 413
  idEntry 16 0 ⟨3619, 1692, 28336, 13248, 187850, by decide⟩, -- source row 432
  idEntry 16 1 ⟨3619, 1692, 28336, 13248, 187850, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-10857, -5076, -85008, -39744, 187850, by decide⟩, -- source row 434
  idEntry 16 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 435
  idEntry 16 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 436
  idEntry 16 5 ⟨3619, 1692, 28336, 13248, 93925, by decide⟩, -- source row 437
  idEntry 16 6 ⟨-85008, -39744, -3619, -1692, 93925, by decide⟩, -- source row 438
  idEntry 16 7 ⟨-13167, -6156, -10780, -5040, 37570, by decide⟩, -- source row 439
  idEntry 16 8 ⟨10780, 5040, -13167, -6156, 37570, by decide⟩, -- source row 440
  idEntry 17 3 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 462
  idEntry 17 4 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 463
  idEntry 17 7 ⟨13167, 6156, 0, 0, 18785, by decide⟩, -- source row 466
  idEntry 17 8 ⟨-2156, -1008, 0, 0, 3757, by decide⟩, -- source row 467
  idEntry 18 0 ⟨3619, 1692, -28336, -13248, 187850, by decide⟩, -- source row 486
  idEntry 18 1 ⟨3619, 1692, -28336, -13248, 187850, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-10857, -5076, 85008, 39744, 187850, by decide⟩, -- source row 488
  idEntry 18 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 489
  idEntry 18 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 490
  idEntry 18 5 ⟨-7238, -3384, 56672, 26496, 93925, by decide⟩, -- source row 491
  idEntry 18 7 ⟨-13167, -6156, -10780, -5040, 37570, by decide⟩, -- source row 493
  idEntry 18 8 ⟨10780, 5040, -13167, -6156, 37570, by decide⟩, -- source row 494
  idEntry 19 0 ⟨0, 0, -28336, -13248, 93925, by decide⟩, -- source row 513
  idEntry 19 1 ⟨0, 0, -28336, -13248, 93925, by decide⟩, -- source row 514
  idEntry 19 2 ⟨0, 0, 85008, 39744, 93925, by decide⟩, -- source row 515
  idEntry 19 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 516
  idEntry 19 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 517
  idEntry 19 5 ⟨0, 0, -56672, -26496, 93925, by decide⟩, -- source row 518
  idEntry 19 6 ⟨170016, 79488, 0, 0, 93925, by decide⟩, -- source row 519
  idEntry 19 7 ⟨13167, 6156, 0, 0, 18785, by decide⟩, -- source row 520
  idEntry 19 8 ⟨-2156, -1008, 0, 0, 3757, by decide⟩, -- source row 521
  idEntry 20 3 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 543
  idEntry 20 4 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 544
  idEntry 20 7 ⟨-13167, -6156, 10780, 5040, 37570, by decide⟩, -- source row 547
  idEntry 20 8 ⟨10780, 5040, 13167, 6156, 37570, by decide⟩, -- source row 548
  idEntry 21 0 ⟨693, 324, 36, -77, 1020, by decide⟩, -- source row 567
  idEntry 21 1 ⟨693, 324, 36, -77, 1020, by decide⟩, -- source row 568
  idEntry 21 2 ⟨-693, -324, -36, 77, 340, by decide⟩, -- source row 569
  idEntry 21 7 ⟨-693, -324, -36, 77, 425, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-2772, -1296, -144, 308, 1275, by decide⟩, -- source row 575
  idEntry 21 9 ⟨3177, 2236, 0, 0, 2890, by decide⟩, -- source row 576
  idEntry 21 10 ⟨-2388, 291, 0, 0, 2890, by decide⟩, -- source row 577
  idEntry 22 0 ⟨693, 324, -36, 77, 1020, by decide⟩, -- source row 594
  idEntry 22 1 ⟨693, 324, -36, 77, 1020, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-693, -324, 36, -77, 340, by decide⟩, -- source row 596
  idEntry 22 7 ⟨549, 632, 888, 509, 850, by decide⟩, -- source row 601
  idEntry 22 8 ⟨3096, 603, -2223, -664, 2550, by decide⟩, -- source row 602
  idEntry 22 9 ⟨-3177, -2236, -2388, 291, 5780, by decide⟩, -- source row 603
  idEntry 22 10 ⟨2388, -291, -3177, -2236, 5780, by decide⟩, -- source row 604
  idEntry 23 9 ⟨-3177, -2236, 2388, -291, 5780, by decide⟩, -- source row 630
  idEntry 23 10 ⟨2388, -291, 3177, 2236, 5780, by decide⟩, -- source row 631
  idEntry 24 0 ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 648
  idEntry 24 1 ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-231, -108, -36, 77, 340, by decide⟩, -- source row 650
  idEntry 24 7 ⟨-231, -108, -36, 77, 425, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-924, -432, -144, 308, 1275, by decide⟩, -- source row 656
  idEntry 24 9 ⟨-144, 308, -308, -144, 1445, by decide⟩, -- source row 657
  idEntry 24 10 ⟨-108, 231, -231, -108, 578, by decide⟩, -- source row 658
  idEntry 25 0 ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 675
  idEntry 25 1 ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 676
  idEntry 25 2 ⟨231, 108, 36, -77, 340, by decide⟩, -- source row 677
  idEntry 25 7 ⟨-375, 200, -344, -67, 850, by decide⟩, -- source row 682
  idEntry 25 8 ⟨-600, -1125, 549, 632, 2550, by decide⟩, -- source row 683
  idEntry 25 9 ⟨-3177, -2236, 76, 1443, 5780, by decide⟩, -- source row 684
  idEntry 25 10 ⟨2388, -291, 1443, -76, 5780, by decide⟩, -- source row 685
  idEntry 26 9 ⟨3753, 1004, 1156, -867, 5780, by decide⟩, -- source row 711
  idEntry 26 10 ⟨-1308, -2019, 867, 1156, 5780, by decide⟩, -- source row 712
  idEntry 27 0 ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 729
  idEntry 27 1 ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 730
  idEntry 27 2 ⟨231, 108, -36, 77, 340, by decide⟩, -- source row 731
  idEntry 27 7 ⟨231, 108, -36, 77, 425, by decide⟩, -- source row 736
  idEntry 27 8 ⟨924, 432, -144, 308, 1275, by decide⟩, -- source row 737
  idEntry 27 9 ⟨-144, 308, 308, 144, 1445, by decide⟩, -- source row 738
  idEntry 27 10 ⟨-108, 231, 231, 108, 578, by decide⟩, -- source row 739
  idEntry 28 0 ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 756
  idEntry 28 1 ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-231, -108, 36, -77, 340, by decide⟩, -- source row 758
  idEntry 28 7 ⟨87, 416, 272, 221, 850, by decide⟩, -- source row 763
  idEntry 28 8 ⟨1248, -261, -837, -16, 2550, by decide⟩, -- source row 764
  idEntry 28 9 ⟨3753, 1004, -1156, 867, 5780, by decide⟩, -- source row 765
  idEntry 28 10 ⟨-1308, -2019, -867, -1156, 5780, by decide⟩, -- source row 766
  idEntry 29 9 ⟨-3177, -2236, -76, -1443, 5780, by decide⟩, -- source row 792
  idEntry 29 10 ⟨2388, -291, -1443, 76, 5780, by decide⟩, -- source row 793
  idEntry 30 0 ⟨4433121, 2072628, -156804, 528053, 6537180, by decide⟩, -- source row 810
  idEntry 30 1 ⟨4433121, 2072628, -156804, 528053, 6537180, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-4433121, -2072628, 156804, -528053, 2179060, by decide⟩, -- source row 812
  idEntry 30 5 ⟨492107, 230076, 0, 0, 544765, by decide⟩, -- source row 815
  idEntry 30 6 ⟨7392, 3456, 0, 0, 108953, by decide⟩, -- source row 816
  idEntry 30 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 817
  idEntry 30 8 ⟨8, 15, 0, 0, 34, by decide⟩, -- source row 818
  idEntry 30 9 ⟨-4433121, -2072628, 156804, -528053, 1852201, by decide⟩, -- source row 819
  idEntry 30 10 ⟨35464968, 16581024, -1254432, 4224424, 27783015, by decide⟩, -- source row 820
  idEntry 31 0 ⟨4433121, 2072628, 156804, -528053, 6537180, by decide⟩, -- source row 837
  idEntry 31 1 ⟨4433121, 2072628, 156804, -528053, 6537180, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-4433121, -2072628, -156804, 528053, 2179060, by decide⟩, -- source row 839
  idEntry 31 5 ⟨-492107, -230076, -36960, -17280, 1089530, by decide⟩, -- source row 842
  idEntry 31 6 ⟨-36960, -17280, 492107, 230076, 1089530, by decide⟩, -- source row 843
  idEntry 31 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 844
  idEntry 31 8 ⟨-8, -15, 15, -8, 68, by decide⟩, -- source row 845
  idEntry 31 9 ⟨23420037, 6138716, 12605676, 2886743, 18522010, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-28408788, -40343409, 65242383, 35313844, 55566030, by decide⟩, -- source row 847
  idEntry 32 5 ⟨-492107, -230076, 36960, 17280, 1089530, by decide⟩, -- source row 869
  idEntry 32 6 ⟨-36960, -17280, -492107, -230076, 1089530, by decide⟩, -- source row 870
  idEntry 32 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 871
  idEntry 32 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 872
  idEntry 33 0 ⟨1480479, 692172, -378564, 424373, 6537180, by decide⟩, -- source row 891
  idEntry 33 1 ⟨1480479, 692172, -378564, 424373, 6537180, by decide⟩, -- source row 892
  idEntry 33 2 ⟨-1480479, -692172, 378564, -424373, 2179060, by decide⟩, -- source row 893
  idEntry 33 5 ⟨-492107, -230076, -36960, -17280, 1089530, by decide⟩, -- source row 896
  idEntry 33 6 ⟨-36960, -17280, 492107, 230076, 1089530, by decide⟩, -- source row 897
  idEntry 33 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 898
  idEntry 33 8 ⟨8, 15, 0, 0, 34, by decide⟩, -- source row 899
  idEntry 33 9 ⟨-1480479, -692172, 378564, -424373, 1852201, by decide⟩, -- source row 900
  idEntry 33 10 ⟨11843832, 5537376, -3028512, 3394984, 27783015, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-1472163, -688284, 156804, -528053, 6537180, by decide⟩, -- source row 918
  idEntry 34 1 ⟨-1472163, -688284, 156804, -528053, 6537180, by decide⟩, -- source row 919
  idEntry 34 2 ⟨1472163, 688284, -156804, 528053, 2179060, by decide⟩, -- source row 920
  idEntry 34 5 ⟨-492107, -230076, 36960, 17280, 1089530, by decide⟩, -- source row 923
  idEntry 34 6 ⟨-36960, -17280, -492107, -230076, 1089530, by decide⟩, -- source row 924
  idEntry 34 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 925
  idEntry 34 8 ⟨-8, -15, 15, -8, 68, by decide⟩, -- source row 926
  idEntry 34 9 ⟨-6106383, -7665844, -3141748, -4475689, 18522010, by decide⟩, -- source row 927
  idEntry 34 10 ⟨18833484, -18256113, -23336877, -6099836, 55566030, by decide⟩, -- source row 928
  idEntry 35 5 ⟨492107, 230076, 0, 0, 544765, by decide⟩, -- source row 950
  idEntry 35 6 ⟨7392, 3456, 0, 0, 108953, by decide⟩, -- source row 951
  idEntry 35 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 952
  idEntry 35 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 953
  idEntry 36 0 ⟨-1472163, -688284, -156804, 528053, 6537180, by decide⟩, -- source row 972
  idEntry 36 1 ⟨-1472163, -688284, -156804, 528053, 6537180, by decide⟩, -- source row 973
  idEntry 36 2 ⟨1472163, 688284, 156804, -528053, 2179060, by decide⟩, -- source row 974
  idEntry 36 5 ⟨-492107, -230076, 36960, 17280, 1089530, by decide⟩, -- source row 977
  idEntry 36 6 ⟨-36960, -17280, -492107, -230076, 1089530, by decide⟩, -- source row 978
  idEntry 36 7 ⟨15, -8, 0, 0, 34, by decide⟩, -- source row 979
  idEntry 36 8 ⟨8, 15, 0, 0, 34, by decide⟩, -- source row 980
  idEntry 36 9 ⟨1472163, 688284, 156804, -528053, 1852201, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-11777304, -5506272, -1254432, 4224424, 27783015, by decide⟩, -- source row 982
  idEntry 37 0 ⟨1480479, 692172, 378564, -424373, 6537180, by decide⟩, -- source row 999
  idEntry 37 1 ⟨1480479, 692172, 378564, -424373, 6537180, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨-1480479, -692172, -378564, 424373, 2179060, by decide⟩, -- source row 1001
  idEntry 37 5 ⟨492107, 230076, 0, 0, 544765, by decide⟩, -- source row 1004
  idEntry 37 6 ⟨7392, 3456, 0, 0, 108953, by decide⟩, -- source row 1005
  idEntry 37 7 ⟨-15, 8, -8, -15, 68, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨-8, -15, 15, -8, 68, by decide⟩, -- source row 1007
  idEntry 37 9 ⟨10430907, 65876, 5840764, -276073, 18522010, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨5191548, -24634161, 19178673, 13777564, 55566030, by decide⟩, -- source row 1009
  idEntry 38 5 ⟨-492107, -230076, -36960, -17280, 1089530, by decide⟩, -- source row 1031
  idEntry 38 6 ⟨-36960, -17280, 492107, 230076, 1089530, by decide⟩, -- source row 1032
  idEntry 38 7 ⟨-15, 8, 8, 15, 68, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨-8, -15, -15, 8, 68, by decide⟩, -- source row 1034
  sumEntry 0 3 ⟨0, 0, -1078, -504, 11271, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨0, 0, -1463, -684, 37570, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨144837, 67716, 53900, 25200, 225420, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨-10780, -5040, -1463, -684, 75140, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨-39501, -18468, -10780, -5040, 676260, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨0, 0, 1078, 504, 33813, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨39501, 18468, 10780, 5040, 338130, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨39501, 18468, 21560, 10080, 338130, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨0, 0, 1463, 684, 37570, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨39501, 18468, 10780, 5040, 676260, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨10780, 5040, 30723, 14364, 225420, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨39501, 18468, 10780, 5040, 169065, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨-10780, -5040, 4389, 2052, 112710, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨-39501, -18468, -53900, -25200, 676260, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨39501, 18468, 10780, 5040, 676260, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 2156, 1008, 33813, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨39501, 18468, 43120, 20160, 169065, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨-39501, -18468, 10780, 5040, 169065, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨39501, 18468, -75460, -35280, 338130, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨-10780, -5040, -13167, -6156, 112710, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨0, 0, 1078, 504, 33813, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨0, 0, -1078, -504, 33813, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨-39501, -18468, -21560, -10080, 338130, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨13167, 6156, 21560, 10080, 112710, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨-21560, -10080, 13167, 6156, 112710, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨0, 0, -1078, -504, 3757, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨-1078, -504, 0, 0, 11271, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1193
  sumEntry 4 3 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1204
  sumEntry 4 7 ⟨-13167, -6156, -10780, -5040, 112710, by decide⟩, -- source row 1207
  sumEntry 4 8 ⟨10780, 5040, -13167, -6156, 112710, by decide⟩, -- source row 1208
  sumEntry 4 13 ⟨-13167, -6156, 10780, 5040, 112710, by decide⟩, -- source row 1213
  sumEntry 4 14 ⟨-10780, -5040, -13167, -6156, 112710, by decide⟩, -- source row 1214
  sumEntry 4 17 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1218
  sumEntry 4 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1219
  sumEntry 4 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1220
  sumEntry 4 23 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1231
  sumEntry 5 7 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1234
  sumEntry 5 8 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1235
  sumEntry 5 13 ⟨-13167, -6156, 10780, 5040, 112710, by decide⟩, -- source row 1240
  sumEntry 5 14 ⟨-10780, -5040, -13167, -6156, 112710, by decide⟩, -- source row 1241
  sumEntry 5 17 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1245
  sumEntry 5 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1246
  sumEntry 5 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1247
  sumEntry 5 23 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1258
  sumEntry 6 7 ⟨-13167, -6156, 10780, 5040, 112710, by decide⟩, -- source row 1261
  sumEntry 6 8 ⟨10780, 5040, 13167, 6156, 112710, by decide⟩, -- source row 1262
  sumEntry 6 13 ⟨-13167, -6156, 10780, 5040, 112710, by decide⟩, -- source row 1267
  sumEntry 6 14 ⟨-10780, -5040, -13167, -6156, 112710, by decide⟩, -- source row 1268
  sumEntry 6 17 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1272
  sumEntry 6 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1273
  sumEntry 6 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1274
  sumEntry 6 23 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1278
  sumEntry 7 9 ⟨-3177, -2236, 2388, -291, 17340, by decide⟩, -- source row 1290
  sumEntry 7 10 ⟨2388, -291, 3177, 2236, 17340, by decide⟩, -- source row 1291
  sumEntry 7 15 ⟨-28887, 90084, 256716, 115613, 1127100, by decide⟩, -- source row 1296
  sumEntry 7 16 ⟨-256716, -115613, -28887, 90084, 1127100, by decide⟩, -- source row 1297
  sumEntry 7 19 ⟨44541, 7688, 0, 0, 112710, by decide⟩, -- source row 1300
  sumEntry 7 20 ⟨-8728, -9429, 0, 0, 37570, by decide⟩, -- source row 1301
  sumEntry 8 9 ⟨3753, 1004, 1156, -867, 17340, by decide⟩, -- source row 1317
  sumEntry 8 10 ⟨-1308, -2019, 867, 1156, 17340, by decide⟩, -- source row 1318
  sumEntry 8 15 ⟨6624, -14168, 14168, 6624, 93925, by decide⟩, -- source row 1323
  sumEntry 8 16 ⟨1692, -3619, 3619, 1692, 563550, by decide⟩, -- source row 1324
  sumEntry 8 19 ⟨34461, 29248, -4624, -18207, 225420, by decide⟩, -- source row 1327
  sumEntry 8 20 ⟨-38496, -1953, -18207, 4624, 225420, by decide⟩, -- source row 1328
  sumEntry 9 9 ⟨-3177, -2236, -76, -1443, 17340, by decide⟩, -- source row 1344
  sumEntry 9 10 ⟨2388, -291, -1443, 76, 17340, by decide⟩, -- source row 1345
  sumEntry 9 15 ⟨-28887, 90084, 83316, 43363, 1127100, by decide⟩, -- source row 1350
  sumEntry 9 16 ⟨-256716, -115613, 43363, -83316, 1127100, by decide⟩, -- source row 1351
  sumEntry 9 19 ⟨34461, 29248, 4624, 18207, 225420, by decide⟩, -- source row 1354
  sumEntry 9 20 ⟨-38496, -1953, 18207, -4624, 225420, by decide⟩, -- source row 1355
  sumEntry 10 5 ⟨-492107, -230076, 36960, 17280, 3268590, by decide⟩, -- source row 1367
  sumEntry 10 6 ⟨-36960, -17280, -492107, -230076, 3268590, by decide⟩, -- source row 1368
  sumEntry 10 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨1419, 8260, 0, 0, 50286, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨-8260, 1419, 0, 0, 50286, by decide⟩, -- source row 1374
  sumEntry 10 17 ⟨-385, -180, 924, 432, 6630, by decide⟩, -- source row 1379
  sumEntry 10 18 ⟨924, 432, 385, 180, 6630, by decide⟩, -- source row 1380
  sumEntry 10 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1381
  sumEntry 10 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1382
  sumEntry 10 25 ⟨-155, 468, -468, -155, 5916, by decide⟩, -- source row 1387
  sumEntry 10 26 ⟨-468, -155, 155, -468, 5916, by decide⟩, -- source row 1388
  sumEntry 11 5 ⟨492107, 230076, 0, 0, 1634295, by decide⟩, -- source row 1394
  sumEntry 11 6 ⟨2464, 1152, 0, 0, 108953, by decide⟩, -- source row 1395
  sumEntry 11 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨-1419, -8260, 8260, -1419, 100572, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨8260, -1419, 1419, 8260, 100572, by decide⟩, -- source row 1401
  sumEntry 11 17 ⟨-385, -180, 924, 432, 6630, by decide⟩, -- source row 1406
  sumEntry 11 18 ⟨924, 432, 385, 180, 6630, by decide⟩, -- source row 1407
  sumEntry 11 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1408
  sumEntry 11 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1409
  sumEntry 11 25 ⟨-155, 468, 468, 155, 5916, by decide⟩, -- source row 1414
  sumEntry 11 26 ⟨-468, -155, -155, 468, 5916, by decide⟩, -- source row 1415
  sumEntry 12 5 ⟨-492107, -230076, -36960, -17280, 3268590, by decide⟩, -- source row 1421
  sumEntry 12 6 ⟨-36960, -17280, 492107, 230076, 3268590, by decide⟩, -- source row 1422
  sumEntry 12 7 ⟨-15, 8, 8, 15, 204, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨-8, -15, -15, 8, 204, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨-1419, -8260, -8260, 1419, 100572, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨8260, -1419, -1419, -8260, 100572, by decide⟩, -- source row 1428
  sumEntry 12 17 ⟨-385, -180, 924, 432, 6630, by decide⟩, -- source row 1433
  sumEntry 12 18 ⟨924, 432, 385, 180, 6630, by decide⟩, -- source row 1434
  sumEntry 12 19 ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1435
  sumEntry 12 20 ⟨-2156, -1008, 0, 0, 11271, by decide⟩, -- source row 1436
  sumEntry 12 25 ⟨155, -468, 0, 0, 2958, by decide⟩, -- source row 1441
  sumEntry 12 26 ⟨468, 155, 0, 0, 2958, by decide⟩, -- source row 1442
  pairEntry 0 4 (by decide) ⟨-4389, -2052, 10780, 5040, 75140, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 2156, 1008, 11271, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨13167, 6156, -10780, -5040, 225420, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨0, 0, -1078, -504, 11271, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, -2156, -1008, 11271, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨-13167, -6156, -2156, -1008, 45084, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨13167, 6156, 10780, 5040, 225420, by decide⟩, -- source row 1484
  pairEntry 1 8 (by decide) ⟨-4389, -2052, -2156, -1008, 15028, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨39501, 18468, 21560, 10080, 338130, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨-39501, -18468, -21560, -10080, 169065, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨39501, 18468, -10780, -5040, 338130, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨-92169, -43092, -10780, -5040, 225420, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨-4389, -2052, 0, 0, 37570, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨-13167, -6156, 10780, 5040, 225420, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨13167, 6156, -10780, -5040, 225420, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨13167, 6156, -10780, -5040, 225420, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨-13167, -6156, -10780, -5040, 56355, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨13167, 6156, 5390, 2520, 56355, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨-13167, -6156, -10780, -5040, 112710, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨13167, 6156, -10780, -5040, 225420, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨13167, 6156, -10780, -5040, 225420, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨-4389, -2052, 0, 0, 37570, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨4389, 2052, 0, 0, 18785, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨-13167, -6156, 10780, 5040, 225420, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨-39501, -18468, -10780, -5040, 225420, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨0, 0, -1078, -504, 11271, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨13167, 6156, -10780, -5040, 112710, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨39501, 18468, 10780, 5040, 225420, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨-13167, -6156, 10780, 5040, 225420, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨-13167, -6156, -5390, -2520, 56355, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, -2156, -1008, 11271, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨4389, 2052, 10780, 5040, 37570, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨13167, 6156, 10780, 5040, 56355, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨13167, 6156, 10780, 5040, 56355, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨13167, 6156, 10780, 5040, 112710, by decide⟩, -- source row 1721
  pairEntry 12 21 (by decide) ⟨-9629, 30028, 0, 0, 187850, by decide⟩, -- source row 1841
  pairEntry 12 22 (by decide) ⟨-28887, 90084, 256716, 115613, 1127100, by decide⟩, -- source row 1842
  pairEntry 12 24 (by decide) ⟨50601, -79932, 86700, 36125, 1127100, by decide⟩, -- source row 1844
  pairEntry 12 25 (by decide) ⟨6624, -14168, 14168, 6624, 93925, by decide⟩, -- source row 1845
  pairEntry 12 27 (by decide) ⟨50601, -79932, -86700, -36125, 1127100, by decide⟩, -- source row 1847
  pairEntry 12 28 (by decide) ⟨-28887, 90084, 83316, 43363, 1127100, by decide⟩, -- source row 1848
  pairEntry 12 30 (by decide) ⟨-385163, 18996, 0, 0, 1089530, by decide⟩, -- source row 1850
  pairEntry 12 31 (by decide) ⟨-1155489, 56988, -443220, -136715, 6537180, by decide⟩, -- source row 1851
  pairEntry 12 33 (by decide) ⟨1155489, -56988, 591060, 205835, 6537180, by decide⟩, -- source row 1853
  pairEntry 12 34 (by decide) ⟨1797153, 1437444, 517140, 171275, 6537180, by decide⟩, -- source row 1854
  pairEntry 12 36 (by decide) ⟨1155489, -56988, -591060, -205835, 6537180, by decide⟩, -- source row 1856
  pairEntry 12 37 (by decide) ⟨-53472, -124536, -6160, -2880, 544765, by decide⟩, -- source row 1857
  pairEntry 13 21 (by decide) ⟨-28887, 90084, -256716, -115613, 1127100, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨-9629, 30028, 0, 0, 187850, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨-28887, 90084, -83316, -43363, 1127100, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨50601, -79932, 86700, 36125, 1127100, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨6624, -14168, -14168, -6624, 93925, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨50601, -79932, -86700, -36125, 1127100, by decide⟩, -- source row 1873
  pairEntry 13 30 (by decide) ⟨-1155489, 56988, 443220, 136715, 6537180, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨-385163, 18996, 0, 0, 1089530, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨-53472, -124536, 6160, 2880, 544765, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨1155489, -56988, 591060, 205835, 6537180, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨1797153, 1437444, -517140, -171275, 6537180, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨1155489, -56988, -591060, -205835, 6537180, by decide⟩, -- source row 1882
  pairEntry 15 21 (by decide) ⟨28887, -90084, -256716, -115613, 1127100, by decide⟩, -- source row 1913
  pairEntry 15 22 (by decide) ⟨-28887, 90084, -256716, -115613, 1127100, by decide⟩, -- source row 1914
  pairEntry 15 24 (by decide) ⟨-6624, 14168, -14168, -6624, 93925, by decide⟩, -- source row 1916
  pairEntry 15 25 (by decide) ⟨-28887, 90084, -83316, -43363, 1127100, by decide⟩, -- source row 1917
  pairEntry 15 27 (by decide) ⟨28887, -90084, -83316, -43363, 1127100, by decide⟩, -- source row 1919
  pairEntry 15 28 (by decide) ⟨6624, -14168, -14168, -6624, 93925, by decide⟩, -- source row 1920
  pairEntry 15 30 (by decide) ⟨-1797153, -1437444, -517140, -171275, 6537180, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨-53472, -124536, 6160, 2880, 544765, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨53472, 124536, 6160, 2880, 544765, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨1797153, 1437444, -517140, -171275, 6537180, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨1155489, -56988, 443220, 136715, 6537180, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨-1155489, 56988, 443220, 136715, 6537180, by decide⟩, -- source row 1929
  pairEntry 16 21 (by decide) ⟨9629, -30028, 0, 0, 187850, by decide⟩, -- source row 1935
  pairEntry 16 22 (by decide) ⟨28887, -90084, -256716, -115613, 1127100, by decide⟩, -- source row 1936
  pairEntry 16 24 (by decide) ⟨-50601, 79932, -86700, -36125, 1127100, by decide⟩, -- source row 1938
  pairEntry 16 25 (by decide) ⟨-6624, 14168, -14168, -6624, 93925, by decide⟩, -- source row 1939
  pairEntry 16 27 (by decide) ⟨-50601, 79932, 86700, 36125, 1127100, by decide⟩, -- source row 1941
  pairEntry 16 28 (by decide) ⟨28887, -90084, -83316, -43363, 1127100, by decide⟩, -- source row 1942
  pairEntry 16 30 (by decide) ⟨-1155489, 56988, -591060, -205835, 6537180, by decide⟩, -- source row 1944
  pairEntry 16 31 (by decide) ⟨-1797153, -1437444, -517140, -171275, 6537180, by decide⟩, -- source row 1945
  pairEntry 16 33 (by decide) ⟨-1155489, 56988, 591060, 205835, 6537180, by decide⟩, -- source row 1947
  pairEntry 16 34 (by decide) ⟨53472, 124536, 6160, 2880, 544765, by decide⟩, -- source row 1948
  pairEntry 16 36 (by decide) ⟨385163, -18996, 0, 0, 1089530, by decide⟩, -- source row 1950
  pairEntry 16 37 (by decide) ⟨1155489, -56988, 443220, 136715, 6537180, by decide⟩, -- source row 1951
  pairEntry 18 21 (by decide) ⟨28887, -90084, 256716, 115613, 1127100, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨9629, -30028, 0, 0, 187850, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨28887, -90084, 83316, 43363, 1127100, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨-50601, 79932, -86700, -36125, 1127100, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨-6624, 14168, 14168, 6624, 93925, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨-50601, 79932, 86700, 36125, 1127100, by decide⟩, -- source row 1983
  pairEntry 18 30 (by decide) ⟨-1797153, -1437444, 517140, 171275, 6537180, by decide⟩, -- source row 1985
  pairEntry 18 31 (by decide) ⟨-1155489, 56988, 591060, 205835, 6537180, by decide⟩, -- source row 1986
  pairEntry 18 33 (by decide) ⟨1155489, -56988, -443220, -136715, 6537180, by decide⟩, -- source row 1988
  pairEntry 18 34 (by decide) ⟨385163, -18996, 0, 0, 1089530, by decide⟩, -- source row 1989
  pairEntry 18 36 (by decide) ⟨53472, 124536, -6160, -2880, 544765, by decide⟩, -- source row 1991
  pairEntry 18 37 (by decide) ⟨-1155489, 56988, -591060, -205835, 6537180, by decide⟩, -- source row 1992
  pairEntry 19 21 (by decide) ⟨-28887, 90084, 256716, 115613, 1127100, by decide⟩, -- source row 1995
  pairEntry 19 22 (by decide) ⟨28887, -90084, 256716, 115613, 1127100, by decide⟩, -- source row 1996
  pairEntry 19 24 (by decide) ⟨6624, -14168, 14168, 6624, 93925, by decide⟩, -- source row 1998
  pairEntry 19 25 (by decide) ⟨28887, -90084, 83316, 43363, 1127100, by decide⟩, -- source row 1999
  pairEntry 19 27 (by decide) ⟨-28887, 90084, 83316, 43363, 1127100, by decide⟩, -- source row 2001
  pairEntry 19 28 (by decide) ⟨-6624, 14168, 14168, 6624, 93925, by decide⟩, -- source row 2002
  pairEntry 19 30 (by decide) ⟨-53472, -124536, -6160, -2880, 544765, by decide⟩, -- source row 2004
  pairEntry 19 31 (by decide) ⟨-1797153, -1437444, 517140, 171275, 6537180, by decide⟩, -- source row 2005
  pairEntry 19 33 (by decide) ⟨-1155489, 56988, -443220, -136715, 6537180, by decide⟩, -- source row 2007
  pairEntry 19 34 (by decide) ⟨1155489, -56988, -443220, -136715, 6537180, by decide⟩, -- source row 2008
  pairEntry 19 36 (by decide) ⟨1797153, 1437444, 517140, 171275, 6537180, by decide⟩, -- source row 2010
  pairEntry 19 37 (by decide) ⟨53472, 124536, -6160, -2880, 544765, by decide⟩, -- source row 2011
  pairEntry 21 30 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨-77, -36, 0, 0, 170, by decide⟩, -- source row 2062
  pairEntry 24 31 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2085
  pairEntry 24 34 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2088
  pairEntry 24 37 (by decide) ⟨-231, -108, -36, 77, 1020, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 2097
  pairEntry 25 33 (by decide) ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 2100
  pairEntry 25 36 (by decide) ⟨231, 108, 36, -77, 1020, by decide⟩, -- source row 2103
  pairEntry 27 31 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 2121
  pairEntry 27 34 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 2124
  pairEntry 27 37 (by decide) ⟨231, 108, -36, 77, 1020, by decide⟩, -- source row 2127
  pairEntry 28 30 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 2130
  pairEntry 28 33 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩, -- source row 2133
  pairEntry 28 36 (by decide) ⟨-231, -108, 36, -77, 1020, by decide⟩ -- source row 2136
]

end Option2.NativeStress.NativeT

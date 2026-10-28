module

public import NativeHWeights

@[expose] public section

/-! Exact source λ43; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda43 : List Entry := [
  idEntry 1 0 ⟨-147489, 258252, 430420, 245815, 5171400, by decide⟩, -- source row 27
  idEntry 1 1 ⟨147489, -258252, -430420, -245815, 5171400, by decide⟩, -- source row 28
  idEntry 1 2 ⟨-147489, 258252, 430420, 245815, 5171400, by decide⟩, -- source row 29
  idEntry 1 11 ⟨323, 36, 0, 0, 650, by decide⟩, -- source row 38
  idEntry 1 12 ⟨-36, 323, 0, 0, 650, by decide⟩, -- source row 39
  idEntry 2 0 ⟨-5555, -23510, -15554, -65828, 430950, by decide⟩, -- source row 54
  idEntry 2 1 ⟨-5555, -23510, -15554, -65828, 430950, by decide⟩, -- source row 55
  idEntry 2 2 ⟨5555, 23510, 15554, 65828, 430950, by decide⟩, -- source row 56
  idEntry 2 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 57
  idEntry 2 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 58
  idEntry 3 0 ⟨-1111, -4702, 0, 0, 43095, by decide⟩, -- source row 81
  idEntry 3 1 ⟨203039, -23152, 0, 0, 430950, by decide⟩, -- source row 82
  idEntry 3 2 ⟨-1321283, 585244, -23868, 214149, 1723800, by decide⟩, -- source row 83
  idEntry 3 3 ⟨553567, -304556, 23868, -214149, 1723800, by decide⟩, -- source row 84
  idEntry 3 4 ⟨258252, 147489, -191929, 70172, 1723800, by decide⟩, -- source row 85
  idEntry 4 0 ⟨5555, 23510, 39422, -148321, 861900, by decide⟩, -- source row 108
  idEntry 4 1 ⟨-104297, -179, 7777, 32914, 430950, by decide⟩, -- source row 109
  idEntry 4 2 ⟨203039, -23152, -54976, 82493, 861900, by decide⟩, -- source row 110
  idEntry 4 3 ⟨191929, -70172, -86084, -49163, 574600, by decide⟩, -- source row 111
  idEntry 4 4 ⟨-588108, 347469, -169709, 164212, 1723800, by decide⟩, -- source row 112
  idEntry 5 0 ⟨5555, 23510, 7598, 137211, 861900, by decide⟩, -- source row 135
  idEntry 5 1 ⟨-104297, -179, 15733, -38469, 430950, by decide⟩, -- source row 136
  idEntry 5 2 ⟨196373, -51364, -29660, -62495, 344760, by decide⟩, -- source row 137
  idEntry 5 3 ⟨575787, -210516, 117908, -236369, 1723800, by decide⟩, -- source row 138
  idEntry 5 4 ⟨-36, 323, -323, -36, 2600, by decide⟩, -- source row 139
  idEntry 6 0 ⟨609117, -69456, -289360, -279145, 2585700, by decide⟩, -- source row 162
  idEntry 6 1 ⟨-16665, -70530, -108878, -460796, 1292850, by decide⟩, -- source row 163
  idEntry 6 2 ⟨-214149, -23868, 86084, 49163, 861900, by decide⟩, -- source row 164
  idEntry 6 3 ⟨83325, 352650, -273806, -213317, 1292850, by decide⟩, -- source row 165
  idEntry 6 4 ⟨-22794, -411633, -5555, -23510, 430950, by decide⟩, -- source row 166
  idEntry 7 0 ⟨-1827351, 208368, -366056, -1234067, 5171400, by decide⟩, -- source row 189
  idEntry 7 1 ⟨742437, 494784, -366056, -1234067, 5171400, by decide⟩, -- source row 190
  idEntry 7 2 ⟨542457, -351576, 413792, 805769, 1723800, by decide⟩, -- source row 191
  idEntry 7 3 ⟨642447, 71604, 646028, 2418971, 2585700, by decide⟩, -- source row 192
  idEntry 7 4 ⟨86084, 49163, 191929, -70172, 861900, by decide⟩, -- source row 193
  idEntry 8 0 ⟨742437, 494784, 476008, 1069081, 5171400, by decide⟩, -- source row 216
  idEntry 8 1 ⟨-542457, 351576, 332800, 2353975, 5171400, by decide⟩, -- source row 217
  idEntry 8 2 ⟨-82493, -54976, -39064, -60273, 574600, by decide⟩, -- source row 218
  idEntry 8 3 ⟨-642447, -71604, 320468, 410801, 2585700, by decide⟩, -- source row 219
  idEntry 8 4 ⟨148300, 312475, 214149, 23868, 861900, by decide⟩, -- source row 220
  idEntry 9 0 ⟨-115407, -47199, -54439, -230398, 646425, by decide⟩, -- source row 243
  idEntry 9 1 ⟨-220815, -52080, -57872, -55829, 517140, by decide⟩, -- source row 244
  idEntry 9 2 ⟨148321, 39422, 23510, -5555, 287300, by decide⟩, -- source row 245
  idEntry 9 3 ⟨-2881431, 159558, -429346, -871597, 2585700, by decide⟩, -- source row 246
  idEntry 9 4 ⟨-257178, -773271, -5555, -23510, 861900, by decide⟩, -- source row 247
  idEntry 10 0 ⟨115407, 47199, -62753, 49579, 1292850, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-411633, 22794, -53902, -543289, 2585700, by decide⟩, -- source row 271
  idEntry 10 2 ⟨98742, -23331, 7777, 32914, 430950, by decide⟩, -- source row 272
  idEntry 10 3 ⟨873261, 166002, 506042, 1826519, 2585700, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-288286, -904927, -137211, 7598, 861900, by decide⟩, -- source row 274
  idEntry 11 0 ⟨-214149, -23868, 148300, 312475, 1292850, by decide⟩, -- source row 297
  idEntry 11 1 ⟨428298, 47736, 148300, 312475, 1292850, by decide⟩, -- source row 298
  idEntry 11 2 ⟨16665, 70530, -39422, 148321, 861900, by decide⟩, -- source row 299
  idEntry 11 3 ⟨906591, 307062, 178334, 1069913, 2585700, by decide⟩, -- source row 300
  idEntry 11 4 ⟨101638, 114991, 114991, -101638, 861900, by decide⟩, -- source row 301
  idEntry 12 0 ⟨-621, -3772, -216, -1312, 11050, by decide⟩, -- source row 324
  idEntry 12 1 ⟨-621, -3772, -216, -1312, 11050, by decide⟩, -- source row 325
  idEntry 12 2 ⟨1863, 11316, 648, 3936, 11050, by decide⟩, -- source row 326
  idEntry 12 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 327
  idEntry 12 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 328
  idEntry 12 5 ⟨1242, 7544, 432, 2624, 5525, by decide⟩, -- source row 329
  idEntry 12 7 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 331
  idEntry 12 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 332
  idEntry 12 9 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 333
  idEntry 12 10 ⟨-36, 323, 0, 0, 650, by decide⟩, -- source row 334
  idEntry 13 0 ⟨-621, -3772, 216, 1312, 11050, by decide⟩, -- source row 351
  idEntry 13 1 ⟨-621, -3772, 216, 1312, 11050, by decide⟩, -- source row 352
  idEntry 13 2 ⟨1863, 11316, -648, -3936, 11050, by decide⟩, -- source row 353
  idEntry 13 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 354
  idEntry 13 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 355
  idEntry 13 5 ⟨-621, -3772, 216, 1312, 5525, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-648, -3936, 621, 3772, 5525, by decide⟩, -- source row 357
  idEntry 13 7 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 358
  idEntry 13 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 359
  idEntry 13 9 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 360
  idEntry 13 10 ⟨36, -323, 323, 36, 1300, by decide⟩, -- source row 361
  idEntry 14 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 381
  idEntry 14 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 382
  idEntry 14 7 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 385
  idEntry 14 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 386
  idEntry 14 9 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 387
  idEntry 14 10 ⟨36, -323, -323, -36, 1300, by decide⟩, -- source row 388
  idEntry 15 0 ⟨1968, -324, -108, -656, 5525, by decide⟩, -- source row 405
  idEntry 15 1 ⟨1968, -324, -108, -656, 5525, by decide⟩, -- source row 406
  idEntry 15 2 ⟨-5904, 972, 324, 1968, 5525, by decide⟩, -- source row 407
  idEntry 15 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 408
  idEntry 15 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 409
  idEntry 15 5 ⟨-7872, 1296, 432, 2624, 5525, by decide⟩, -- source row 410
  idEntry 15 7 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 412
  idEntry 15 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 413
  idEntry 15 9 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 414
  idEntry 15 10 ⟨36, -323, -323, -36, 1300, by decide⟩, -- source row 415
  idEntry 16 0 ⟨3315, -4420, 3556, -1933, 22100, by decide⟩, -- source row 432
  idEntry 16 1 ⟨3315, -4420, 3556, -1933, 22100, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-9945, 13260, -10668, 5799, 22100, by decide⟩, -- source row 434
  idEntry 16 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 435
  idEntry 16 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 436
  idEntry 16 5 ⟨3315, -4420, 3556, -1933, 11050, by decide⟩, -- source row 437
  idEntry 16 6 ⟨-10668, 5799, -3315, 4420, 11050, by decide⟩, -- source row 438
  idEntry 16 7 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 439
  idEntry 16 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 440
  idEntry 16 9 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 441
  idEntry 16 10 ⟨-36, 323, 0, 0, 650, by decide⟩, -- source row 442
  idEntry 17 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 462
  idEntry 17 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 463
  idEntry 17 7 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 466
  idEntry 17 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 467
  idEntry 17 9 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 468
  idEntry 17 10 ⟨36, -323, 323, 36, 1300, by decide⟩, -- source row 469
  idEntry 18 0 ⟨3315, -4420, -3556, 1933, 22100, by decide⟩, -- source row 486
  idEntry 18 1 ⟨3315, -4420, -3556, 1933, 22100, by decide⟩, -- source row 487
  idEntry 18 2 ⟨-9945, 13260, 10668, -5799, 22100, by decide⟩, -- source row 488
  idEntry 18 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 489
  idEntry 18 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 490
  idEntry 18 5 ⟨-3315, 4420, 3556, -1933, 5525, by decide⟩, -- source row 491
  idEntry 18 7 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 493
  idEntry 18 8 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 494
  idEntry 18 9 ⟨323, 36, -36, 323, 1300, by decide⟩, -- source row 495
  idEntry 18 10 ⟨36, -323, 323, 36, 1300, by decide⟩, -- source row 496
  idEntry 19 0 ⟨1968, -324, 108, 656, 5525, by decide⟩, -- source row 513
  idEntry 19 1 ⟨1968, -324, 108, 656, 5525, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-5904, 972, -324, -1968, 5525, by decide⟩, -- source row 515
  idEntry 19 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 516
  idEntry 19 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 517
  idEntry 19 5 ⟨3936, -648, 216, 1312, 5525, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-648, -3936, -3936, 648, 5525, by decide⟩, -- source row 519
  idEntry 19 7 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 520
  idEntry 19 8 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 521
  idEntry 19 9 ⟨323, 36, 36, -323, 1300, by decide⟩, -- source row 522
  idEntry 19 10 ⟨36, -323, -323, -36, 1300, by decide⟩, -- source row 523
  idEntry 20 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 543
  idEntry 20 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 544
  idEntry 20 7 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 547
  idEntry 20 8 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 548
  idEntry 20 9 ⟨-323, -36, 0, 0, 650, by decide⟩, -- source row 549
  idEntry 20 10 ⟨-36, 323, 0, 0, 650, by decide⟩, -- source row 550
  idEntry 21 0 ⟨9, -12, 4, 3, 30, by decide⟩, -- source row 567
  idEntry 21 1 ⟨9, -12, 4, 3, 30, by decide⟩, -- source row 568
  idEntry 21 2 ⟨-9, 12, -4, -3, 10, by decide⟩, -- source row 569
  idEntry 21 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 570
  idEntry 21 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 571
  idEntry 21 5 ⟨3, -4, 0, 0, 5, by decide⟩, -- source row 572
  idEntry 21 6 ⟨4, 3, 0, 0, 5, by decide⟩, -- source row 573
  idEntry 21 7 ⟨-18, 24, -8, -6, 25, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-72, 96, -32, -24, 75, by decide⟩, -- source row 575
  idEntry 22 0 ⟨9, -12, -4, -3, 30, by decide⟩, -- source row 594
  idEntry 22 1 ⟨9, -12, -4, -3, 30, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-9, 12, 4, 3, 10, by decide⟩, -- source row 596
  idEntry 22 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 597
  idEntry 22 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 598
  idEntry 22 5 ⟨-3, 4, -4, -3, 10, by decide⟩, -- source row 599
  idEntry 22 6 ⟨-4, -3, 3, -4, 10, by decide⟩, -- source row 600
  idEntry 22 7 ⟨-7, -24, 8, -19, 25, by decide⟩, -- source row 601
  idEntry 22 8 ⟨72, -21, -43, 24, 75, by decide⟩, -- source row 602
  idEntry 23 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 624
  idEntry 23 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 625
  idEntry 23 5 ⟨-3, 4, 4, 3, 10, by decide⟩, -- source row 626
  idEntry 23 6 ⟨-4, -3, -3, 4, 10, by decide⟩, -- source row 627
  idEntry 24 0 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 648
  idEntry 24 1 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 649
  idEntry 24 2 ⟨0, 0, -4, -3, 10, by decide⟩, -- source row 650
  idEntry 24 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 651
  idEntry 24 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 652
  idEntry 24 5 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 653
  idEntry 24 6 ⟨4, 3, -3, 4, 20, by decide⟩, -- source row 654
  idEntry 24 7 ⟨0, 0, -8, -6, 25, by decide⟩, -- source row 655
  idEntry 24 8 ⟨0, 0, -32, -24, 75, by decide⟩, -- source row 656
  idEntry 25 0 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 675
  idEntry 25 1 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 676
  idEntry 25 2 ⟨-9, 12, -4, -3, 20, by decide⟩, -- source row 677
  idEntry 25 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 678
  idEntry 25 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 679
  idEntry 25 5 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 680
  idEntry 25 6 ⟨4, 3, 3, -4, 20, by decide⟩, -- source row 681
  idEntry 25 7 ⟨25, 0, 16, -13, 50, by decide⟩, -- source row 682
  idEntry 25 8 ⟨0, -75, -11, 48, 150, by decide⟩, -- source row 683
  idEntry 26 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 705
  idEntry 26 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 706
  idEntry 26 5 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 707
  idEntry 26 6 ⟨-4, -3, 0, 0, 10, by decide⟩, -- source row 708
  idEntry 27 0 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 729
  idEntry 27 1 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 730
  idEntry 27 2 ⟨-9, 12, 4, 3, 20, by decide⟩, -- source row 731
  idEntry 27 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 732
  idEntry 27 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 733
  idEntry 27 5 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 734
  idEntry 27 6 ⟨4, 3, 3, -4, 20, by decide⟩, -- source row 735
  idEntry 27 7 ⟨-9, 12, 4, 3, 25, by decide⟩, -- source row 736
  idEntry 27 8 ⟨-36, 48, 16, 12, 75, by decide⟩, -- source row 737
  idEntry 28 0 ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 756
  idEntry 28 1 ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 757
  idEntry 28 2 ⟨0, 0, 4, 3, 10, by decide⟩, -- source row 758
  idEntry 28 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 759
  idEntry 28 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 760
  idEntry 28 5 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 761
  idEntry 28 6 ⟨-4, -3, 0, 0, 10, by decide⟩, -- source row 762
  idEntry 28 7 ⟨-16, -12, -4, -3, 25, by decide⟩, -- source row 763
  idEntry 28 8 ⟨36, 27, -16, -12, 75, by decide⟩, -- source row 764
  idEntry 29 3 ⟨-60273, 39064, 0, 0, 143650, by decide⟩, -- source row 786
  idEntry 29 4 ⟨-39064, -60273, 0, 0, 143650, by decide⟩, -- source row 787
  idEntry 29 5 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 788
  idEntry 29 6 ⟨4, 3, -3, 4, 20, by decide⟩, -- source row 789
  idEntry 30 0 ⟨63279, -72372, 24124, 21093, 384540, by decide⟩, -- source row 810
  idEntry 30 1 ⟨63279, -72372, 24124, 21093, 384540, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-63279, 72372, -24124, -21093, 128180, by decide⟩, -- source row 812
  idEntry 30 3 ⟨-38241609, 43736812, 0, 0, 60404825, by decide⟩, -- source row 813
  idEntry 30 4 ⟨10883988, -12447984, 0, 0, 60404825, by decide⟩, -- source row 814
  idEntry 30 7 ⟨-33217, -156744, 0, 0, 320450, by decide⟩, -- source row 817
  idEntry 30 8 ⟨156744, -33217, 0, 0, 320450, by decide⟩, -- source row 818
  idEntry 30 9 ⟨-63279, 72372, -24124, -21093, 108953, by decide⟩, -- source row 819
  idEntry 30 10 ⟨506232, -578976, 192992, 168744, 1634295, by decide⟩, -- source row 820
  idEntry 31 0 ⟨63279, -72372, -24124, -21093, 384540, by decide⟩, -- source row 837
  idEntry 31 1 ⟨63279, -72372, -24124, -21093, 384540, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-63279, 72372, 24124, 21093, 128180, by decide⟩, -- source row 839
  idEntry 31 3 ⟨-38241609, 43736812, 0, 0, 60404825, by decide⟩, -- source row 840
  idEntry 31 4 ⟨10883988, -12447984, 0, 0, 60404825, by decide⟩, -- source row 841
  idEntry 31 7 ⟨33217, 156744, -156744, 33217, 640900, by decide⟩, -- source row 844
  idEntry 31 8 ⟨-156744, 33217, -33217, -156744, 640900, by decide⟩, -- source row 845
  idEntry 31 9 ⟨123403, -530604, 48124, -298457, 1089530, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-1591812, -370209, 1142177, -916836, 3268590, by decide⟩, -- source row 847
  idEntry 32 3 ⟨-38241609, 43736812, 0, 0, 60404825, by decide⟩, -- source row 867
  idEntry 32 4 ⟨10883988, -12447984, 0, 0, 60404825, by decide⟩, -- source row 868
  idEntry 32 7 ⟨33217, 156744, 156744, -33217, 640900, by decide⟩, -- source row 871
  idEntry 32 8 ⟨-156744, 33217, 33217, 156744, 640900, by decide⟩, -- source row 872
  idEntry 33 0 ⟨-63279, 72372, 24124, 21093, 384540, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-63279, 72372, 24124, 21093, 384540, by decide⟩, -- source row 892
  idEntry 33 2 ⟨63279, -72372, -24124, -21093, 128180, by decide⟩, -- source row 893
  idEntry 33 3 ⟨-75585561, 11084848, 54620800, 25793625, 241619300, by decide⟩, -- source row 894
  idEntry 33 4 ⟨-120326448, -127172811, 25793625, -54620800, 241619300, by decide⟩, -- source row 895
  idEntry 33 7 ⟨33217, 156744, 156744, -33217, 640900, by decide⟩, -- source row 898
  idEntry 33 8 ⟨-156744, 33217, 33217, 156744, 640900, by decide⟩, -- source row 899
  idEntry 33 9 ⟨63279, -72372, -24124, -21093, 108953, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-506232, 578976, 192992, 168744, 1634295, by decide⟩, -- source row 901
  idEntry 34 0 ⟨0, 0, 24124, 21093, 192270, by decide⟩, -- source row 918
  idEntry 34 1 ⟨0, 0, 24124, 21093, 192270, by decide⟩, -- source row 919
  idEntry 34 2 ⟨0, 0, -24124, -21093, 64090, by decide⟩, -- source row 920
  idEntry 34 3 ⟨-75585561, 11084848, 54620800, 25793625, 241619300, by decide⟩, -- source row 921
  idEntry 34 4 ⟨-120326448, -127172811, 25793625, -54620800, 241619300, by decide⟩, -- source row 922
  idEntry 34 7 ⟨-33217, -156744, 0, 0, 320450, by decide⟩, -- source row 925
  idEntry 34 8 ⟨156744, -33217, 0, 0, 320450, by decide⟩, -- source row 926
  idEntry 34 9 ⟨192992, 168744, 120620, 105465, 544765, by decide⟩, -- source row 927
  idEntry 34 10 ⟨1085580, 949185, -192992, -168744, 1634295, by decide⟩, -- source row 928
  idEntry 35 3 ⟨-75585561, 11084848, 54620800, 25793625, 241619300, by decide⟩, -- source row 948
  idEntry 35 4 ⟨-120326448, -127172811, 25793625, -54620800, 241619300, by decide⟩, -- source row 949
  idEntry 35 7 ⟨33217, 156744, -156744, 33217, 640900, by decide⟩, -- source row 952
  idEntry 35 8 ⟨-156744, 33217, -33217, -156744, 640900, by decide⟩, -- source row 953
  idEntry 36 0 ⟨0, 0, -24124, -21093, 192270, by decide⟩, -- source row 972
  idEntry 36 1 ⟨0, 0, -24124, -21093, 192270, by decide⟩, -- source row 973
  idEntry 36 2 ⟨0, 0, 24124, 21093, 64090, by decide⟩, -- source row 974
  idEntry 36 3 ⟨-75585561, 11084848, -54620800, -25793625, 241619300, by decide⟩, -- source row 975
  idEntry 36 4 ⟨-120326448, -127172811, -25793625, 54620800, 241619300, by decide⟩, -- source row 976
  idEntry 36 7 ⟨33217, 156744, -156744, 33217, 640900, by decide⟩, -- source row 979
  idEntry 36 8 ⟨-156744, 33217, -33217, -156744, 640900, by decide⟩, -- source row 980
  idEntry 36 9 ⟨0, 0, 48248, 42186, 108953, by decide⟩, -- source row 981
  idEntry 36 10 ⟨0, 0, -385984, -337488, 1634295, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-63279, 72372, -24124, -21093, 384540, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-63279, 72372, -24124, -21093, 384540, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨63279, -72372, 24124, 21093, 128180, by decide⟩, -- source row 1001
  idEntry 37 3 ⟨-75585561, 11084848, -54620800, -25793625, 241619300, by decide⟩, -- source row 1002
  idEntry 37 4 ⟨-120326448, -127172811, -25793625, 54620800, 241619300, by decide⟩, -- source row 1003
  idEntry 37 7 ⟨33217, 156744, 156744, -33217, 640900, by decide⟩, -- source row 1006
  idEntry 37 8 ⟨-156744, 33217, 33217, 156744, 640900, by decide⟩, -- source row 1007
  idEntry 37 9 ⟨-509387, 193116, -289364, 87527, 1089530, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨-579348, -1528161, -756193, 1254324, 3268590, by decide⟩, -- source row 1009
  idEntry 38 3 ⟨-75585561, 11084848, -54620800, -25793625, 241619300, by decide⟩, -- source row 1029
  idEntry 38 4 ⟨-120326448, -127172811, -25793625, 54620800, 241619300, by decide⟩, -- source row 1030
  idEntry 38 7 ⟨-33217, -156744, 0, 0, 320450, by decide⟩, -- source row 1033
  idEntry 38 8 ⟨156744, -33217, 0, 0, 320450, by decide⟩, -- source row 1034
  sumEntry 0 3 ⟨-98742, 23331, -38885, -164570, 430950, by decide⟩, -- source row 1095
  sumEntry 0 4 ⟨-350502, -1168239, 5555, 23510, 2585700, by decide⟩, -- source row 1096
  sumEntry 0 19 ⟨203039, -23152, 85368, 466351, 1723800, by decide⟩, -- source row 1111
  sumEntry 0 20 ⟨69456, 609117, -586897, 163496, 5171400, by decide⟩, -- source row 1112
  sumEntry 1 0 ⟨-180819, 117192, -54976, 82493, 5171400, by decide⟩, -- source row 1119
  sumEntry 1 1 ⟨-296226, 69993, -78307, -16249, 1292850, by decide⟩, -- source row 1120
  sumEntry 1 2 ⟨-214149, -23868, -86084, -49163, 2585700, by decide⟩, -- source row 1121
  sumEntry 1 3 ⟨-411633, 22794, -101638, -114991, 2585700, by decide⟩, -- source row 1122
  sumEntry 1 4 ⟨-14106, 3333, -1111, -4702, 517140, by decide⟩, -- source row 1123
  sumEntry 1 11 ⟨1760691, -490488, 54976, -82493, 5171400, by decide⟩, -- source row 1130
  sumEntry 1 12 ⟨-681432, -47499, 158599, -211232, 5171400, by decide⟩, -- source row 1131
  sumEntry 1 19 ⟨180819, -117192, 54976, -82493, 1292850, by decide⟩, -- source row 1138
  sumEntry 1 20 ⟨117192, 180819, -203039, 23152, 2585700, by decide⟩, -- source row 1139
  sumEntry 2 0 ⟨114159, -399312, -131672, -872429, 5171400, by decide⟩, -- source row 1146
  sumEntry 2 1 ⟨970755, -303840, -131672, -872429, 5171400, by decide⟩, -- source row 1147
  sumEntry 2 2 ⟨0, 0, 15554, 65828, 646425, by decide⟩, -- source row 1148
  sumEntry 2 3 ⟨16665, 70530, 62216, 263312, 646425, by decide⟩, -- source row 1149
  sumEntry 2 4 ⟨-15554, -65828, 0, 0, 215475, by decide⟩, -- source row 1150
  sumEntry 2 11 ⟨214149, 23868, -86084, -49163, 1292850, by decide⟩, -- source row 1157
  sumEntry 2 19 ⟨180819, -117192, -193888, -1135741, 2585700, by decide⟩, -- source row 1165
  sumEntry 2 20 ⟨-54976, 82493, -60273, 39064, 861900, by decide⟩, -- source row 1166
  sumEntry 3 0 ⟨-98742, 23331, -7777, -32914, 1292850, by decide⟩, -- source row 1173
  sumEntry 3 1 ⟨-49995, -211590, -101638, -114991, 2585700, by decide⟩, -- source row 1174
  sumEntry 3 2 ⟨16665, 70530, 8314, -279977, 2585700, by decide⟩, -- source row 1175
  sumEntry 3 3 ⟨159431, 86442, 116834, 389413, 861900, by decide⟩, -- source row 1176
  sumEntry 3 4 ⟨-132746, -246647, -5555, -23510, 861900, by decide⟩, -- source row 1177
  sumEntry 3 11 ⟨32914, -7777, -38885, -164570, 430950, by decide⟩, -- source row 1184
  sumEntry 3 12 ⟨7777, 32914, 32914, -7777, 430950, by decide⟩, -- source row 1185
  sumEntry 3 20 ⟨7777, 32914, 32914, -7777, 215475, by decide⟩, -- source row 1193
  sumEntry 4 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1204
  sumEntry 4 7 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1207
  sumEntry 4 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1208
  sumEntry 4 9 ⟨323, 36, 36, -323, 3900, by decide⟩, -- source row 1209
  sumEntry 4 10 ⟨36, -323, -323, -36, 3900, by decide⟩, -- source row 1210
  sumEntry 4 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1211
  sumEntry 4 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1212
  sumEntry 4 13 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1213
  sumEntry 4 14 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1214
  sumEntry 4 17 ⟨60273, -39064, -39064, -60273, 861900, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨-39064, -60273, -60273, 39064, 861900, by decide⟩, -- source row 1218
  sumEntry 4 19 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1219
  sumEntry 4 20 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1220
  sumEntry 4 21 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1221
  sumEntry 4 22 ⟨36, -323, 323, 36, 3900, by decide⟩, -- source row 1222
  sumEntry 4 23 ⟨60273, -39064, 39064, 60273, 861900, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨-39064, -60273, 60273, -39064, 861900, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1231
  sumEntry 5 7 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1234
  sumEntry 5 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1235
  sumEntry 5 9 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1236
  sumEntry 5 10 ⟨36, -323, 323, 36, 3900, by decide⟩, -- source row 1237
  sumEntry 5 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1238
  sumEntry 5 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1239
  sumEntry 5 13 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1240
  sumEntry 5 14 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1241
  sumEntry 5 17 ⟨60273, -39064, 39064, 60273, 861900, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨-39064, -60273, 60273, -39064, 861900, by decide⟩, -- source row 1245
  sumEntry 5 19 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1246
  sumEntry 5 20 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1247
  sumEntry 5 21 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1248
  sumEntry 5 22 ⟨36, -323, 323, 36, 3900, by decide⟩, -- source row 1249
  sumEntry 5 23 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨39064, 60273, 0, 0, 430950, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1258
  sumEntry 6 7 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1261
  sumEntry 6 8 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1262
  sumEntry 6 9 ⟨-323, -36, 0, 0, 1950, by decide⟩, -- source row 1263
  sumEntry 6 10 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1264
  sumEntry 6 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1265
  sumEntry 6 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1266
  sumEntry 6 13 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1267
  sumEntry 6 14 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1268
  sumEntry 6 17 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨39064, 60273, 0, 0, 430950, by decide⟩, -- source row 1272
  sumEntry 6 19 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1273
  sumEntry 6 20 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1274
  sumEntry 6 21 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1275
  sumEntry 6 22 ⟨36, -323, 323, 36, 3900, by decide⟩, -- source row 1276
  sumEntry 6 23 ⟨60273, -39064, -39064, -60273, 861900, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨-39064, -60273, -60273, 39064, 861900, by decide⟩, -- source row 1278
  sumEntry 7 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1284
  sumEntry 7 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1285
  sumEntry 7 5 ⟨-3, 4, 4, 3, 30, by decide⟩, -- source row 1286
  sumEntry 7 6 ⟨-4, -3, -3, 4, 30, by decide⟩, -- source row 1287
  sumEntry 7 11 ⟨323, 36, 0, 0, 975, by decide⟩, -- source row 1292
  sumEntry 7 12 ⟨-36, 323, 0, 0, 975, by decide⟩, -- source row 1293
  sumEntry 7 13 ⟨47, 1104, 1104, -47, 13260, by decide⟩, -- source row 1294
  sumEntry 7 14 ⟨-1104, 47, 47, 1104, 13260, by decide⟩, -- source row 1295
  sumEntry 7 23 ⟨33, 56, -56, 33, 390, by decide⟩, -- source row 1304
  sumEntry 7 24 ⟨56, -33, 33, 56, 390, by decide⟩, -- source row 1305
  sumEntry 7 25 ⟨4557, 3124, -3124, 4557, 66300, by decide⟩, -- source row 1306
  sumEntry 7 26 ⟨-3124, 4557, -4557, -3124, 66300, by decide⟩, -- source row 1307
  sumEntry 8 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1311
  sumEntry 8 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1312
  sumEntry 8 5 ⟨-3, 4, 0, 0, 30, by decide⟩, -- source row 1313
  sumEntry 8 6 ⟨-4, -3, 0, 0, 30, by decide⟩, -- source row 1314
  sumEntry 8 11 ⟨323, 36, 36, -323, 3900, by decide⟩, -- source row 1319
  sumEntry 8 12 ⟨-36, 323, 323, 36, 3900, by decide⟩, -- source row 1320
  sumEntry 8 13 ⟨47, 1104, -1104, 47, 13260, by decide⟩, -- source row 1321
  sumEntry 8 14 ⟨-1104, 47, -47, -1104, 13260, by decide⟩, -- source row 1322
  sumEntry 8 23 ⟨33, 56, 0, 0, 390, by decide⟩, -- source row 1331
  sumEntry 8 24 ⟨56, -33, 0, 0, 390, by decide⟩, -- source row 1332
  sumEntry 8 25 ⟨-4557, -3124, 0, 0, 33150, by decide⟩, -- source row 1333
  sumEntry 8 26 ⟨3124, -4557, 0, 0, 33150, by decide⟩, -- source row 1334
  sumEntry 9 3 ⟨-60273, 39064, 0, 0, 430950, by decide⟩, -- source row 1338
  sumEntry 9 4 ⟨-39064, -60273, 0, 0, 430950, by decide⟩, -- source row 1339
  sumEntry 9 5 ⟨3, -4, 4, 3, 60, by decide⟩, -- source row 1340
  sumEntry 9 6 ⟨4, 3, -3, 4, 60, by decide⟩, -- source row 1341
  sumEntry 9 11 ⟨323, 36, -36, 323, 3900, by decide⟩, -- source row 1346
  sumEntry 9 12 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1347
  sumEntry 9 13 ⟨-47, -1104, 0, 0, 6630, by decide⟩, -- source row 1348
  sumEntry 9 14 ⟨1104, -47, 0, 0, 6630, by decide⟩, -- source row 1349
  sumEntry 9 23 ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 1358
  sumEntry 9 24 ⟨-56, 33, 33, 56, 780, by decide⟩, -- source row 1359
  sumEntry 9 25 ⟨4557, 3124, 3124, -4557, 66300, by decide⟩, -- source row 1360
  sumEntry 9 26 ⟨-3124, 4557, 4557, 3124, 66300, by decide⟩, -- source row 1361
  sumEntry 10 3 ⟨-38241609, 43736812, 0, 0, 181214475, by decide⟩, -- source row 1365
  sumEntry 10 4 ⟨3627996, -4149328, 0, 0, 60404825, by decide⟩, -- source row 1366
  sumEntry 10 7 ⟨33217, 156744, 156744, -33217, 1922700, by decide⟩, -- source row 1369
  sumEntry 10 8 ⟨-156744, 33217, 33217, 156744, 1922700, by decide⟩, -- source row 1370
  sumEntry 10 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1373
  sumEntry 10 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1374
  sumEntry 10 15 ⟨991371, -1133828, 23286672, -26632896, 212458350, by decide⟩, -- source row 1377
  sumEntry 10 16 ⟨-23286672, 26632896, 991371, -1133828, 212458350, by decide⟩, -- source row 1378
  sumEntry 10 21 ⟨696069, -796092, -1181208, 1350944, 12497550, by decide⟩, -- source row 1383
  sumEntry 10 22 ⟨1181208, -1350944, 696069, -796092, 12497550, by decide⟩, -- source row 1384
  sumEntry 10 25 ⟨4557, 3124, -3124, 4557, 66300, by decide⟩, -- source row 1387
  sumEntry 10 26 ⟨-3124, 4557, -4557, -3124, 66300, by decide⟩, -- source row 1388
  sumEntry 11 3 ⟨-75585561, 11084848, 54620800, 25793625, 724857900, by decide⟩, -- source row 1392
  sumEntry 11 4 ⟨-120326448, -127172811, 25793625, -54620800, 724857900, by decide⟩, -- source row 1393
  sumEntry 11 7 ⟨33217, 156744, -156744, 33217, 1922700, by decide⟩, -- source row 1396
  sumEntry 11 8 ⟨-156744, 33217, -33217, -156744, 1922700, by decide⟩, -- source row 1397
  sumEntry 11 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1400
  sumEntry 11 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1401
  sumEntry 11 15 ⟨78907317, 70993844, -22152844, 27624267, 424916700, by decide⟩, -- source row 1404
  sumEntry 11 16 ⟨26688156, -23658783, -27624267, -22152844, 424916700, by decide⟩, -- source row 1405
  sumEntry 11 21 ⟨-4748901, -2747532, 1977300, -654875, 24995100, by decide⟩, -- source row 1410
  sumEntry 11 22 ⟨1207068, 3439151, 654875, 1977300, 24995100, by decide⟩, -- source row 1411
  sumEntry 11 25 ⟨4557, 3124, -3124, 4557, 66300, by decide⟩, -- source row 1414
  sumEntry 11 26 ⟨-3124, 4557, -4557, -3124, 66300, by decide⟩, -- source row 1415
  sumEntry 12 3 ⟨-75585561, 11084848, -54620800, -25793625, 724857900, by decide⟩, -- source row 1419
  sumEntry 12 4 ⟨-120326448, -127172811, -25793625, 54620800, 724857900, by decide⟩, -- source row 1420
  sumEntry 12 7 ⟨-33217, -156744, 0, 0, 961350, by decide⟩, -- source row 1423
  sumEntry 12 8 ⟨156744, -33217, 0, 0, 961350, by decide⟩, -- source row 1424
  sumEntry 12 11 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1427
  sumEntry 12 12 ⟨-36, 323, 0, 0, 1950, by decide⟩, -- source row 1428
  sumEntry 12 15 ⟨-80890059, -68726188, -24420500, 25641525, 424916700, by decide⟩, -- source row 1431
  sumEntry 12 16 ⟨19885188, -29607009, 25641525, 24420500, 424916700, by decide⟩, -- source row 1432
  sumEntry 12 21 ⟨3356763, 4339716, 385116, -2047013, 24995100, by decide⟩, -- source row 1437
  sumEntry 12 22 ⟨-3569484, -737263, -2047013, -385116, 24995100, by decide⟩, -- source row 1438
  sumEntry 12 25 ⟨4557, 3124, -3124, 4557, 66300, by decide⟩, -- source row 1441
  sumEntry 12 26 ⟨-3124, 4557, -4557, -3124, 66300, by decide⟩, -- source row 1442
  pairEntry 0 4 (by decide) ⟨-191929, 70172, -70172, -191929, 1723800, by decide⟩, -- source row 1446
  pairEntry 0 6 (by decide) ⟨0, 0, 15554, 65828, 215475, by decide⟩, -- source row 1448
  pairEntry 0 8 (by decide) ⟨-203039, 23152, 39064, 60273, 1723800, by decide⟩, -- source row 1450
  pairEntry 0 9 (by decide) ⟨98742, -23331, 7777, 32914, 430950, by decide⟩, -- source row 1451
  pairEntry 0 10 (by decide) ⟨0, 0, -15554, -65828, 215475, by decide⟩, -- source row 1452
  pairEntry 1 3 (by decide) ⟨620227, -22436, 86084, 49163, 1723800, by decide⟩, -- source row 1482
  pairEntry 1 5 (by decide) ⟨191929, -70172, 101996, -93603, 1723800, by decide⟩, -- source row 1484
  pairEntry 1 6 (by decide) ⟨-214149, -23868, 70172, 191929, 861900, by decide⟩, -- source row 1485
  pairEntry 1 8 (by decide) ⟨-631337, -24584, 23152, 203039, 1723800, by decide⟩, -- source row 1487
  pairEntry 1 9 (by decide) ⟨115407, 47199, 54439, 230398, 1292850, by decide⟩, -- source row 1488
  pairEntry 1 10 (by decide) ⟨-180819, 117192, -38348, -477461, 1292850, by decide⟩, -- source row 1489
  pairEntry 1 11 (by decide) ⟨280809, 305988, 86084, 49163, 2585700, by decide⟩, -- source row 1490
  pairEntry 2 3 (by decide) ⟨-158599, 211232, 39064, 60273, 1723800, by decide⟩, -- source row 1518
  pairEntry 2 4 (by decide) ⟨1111, 4702, 4702, -1111, 172380, by decide⟩, -- source row 1519
  pairEntry 2 5 (by decide) ⟨203039, -23152, -39064, -60273, 1723800, by decide⟩, -- source row 1520
  pairEntry 2 6 (by decide) ⟨-203039, 23152, 39064, 60273, 1723800, by decide⟩, -- source row 1521
  pairEntry 2 7 (by decide) ⟨158599, -211232, -7240, -345805, 1723800, by decide⟩, -- source row 1522
  pairEntry 2 8 (by decide) ⟨-5555, -23510, -15554, -65828, 215475, by decide⟩, -- source row 1523
  pairEntry 2 9 (by decide) ⟨5555, 23510, 7598, 137211, 861900, by decide⟩, -- source row 1524
  pairEntry 2 10 (by decide) ⟨-5555, -23510, -15554, -65828, 430950, by decide⟩, -- source row 1525
  pairEntry 2 11 (by decide) ⟨-1111, -4702, -4702, 1111, 86190, by decide⟩, -- source row 1526
  pairEntry 3 6 (by decide) ⟨-203039, 23152, 39064, 60273, 1723800, by decide⟩, -- source row 1556
  pairEntry 3 8 (by decide) ⟨-203039, 23152, 39064, 60273, 1723800, by decide⟩, -- source row 1558
  pairEntry 3 9 (by decide) ⟨1111, 4702, 4702, -1111, 172380, by decide⟩, -- source row 1559
  pairEntry 3 10 (by decide) ⟨-1111, -4702, -4702, 1111, 86190, by decide⟩, -- source row 1560
  pairEntry 4 6 (by decide) ⟨203039, -23152, -39064, -60273, 1723800, by decide⟩, -- source row 1590
  pairEntry 4 8 (by decide) ⟨-180819, 117192, -54976, 82493, 1723800, by decide⟩, -- source row 1592
  pairEntry 4 9 (by decide) ⟨98742, -23331, 7777, 32914, 430950, by decide⟩, -- source row 1593
  pairEntry 4 10 (by decide) ⟨191929, -70172, -7956, 71383, 861900, by decide⟩, -- source row 1594
  pairEntry 5 6 (by decide) ⟨180819, -117192, 54976, -82493, 1723800, by decide⟩, -- source row 1623
  pairEntry 5 8 (by decide) ⟨203039, -23152, -39064, -60273, 1723800, by decide⟩, -- source row 1625
  pairEntry 5 9 (by decide) ⟨104297, 179, 31287, 27359, 430950, by decide⟩, -- source row 1626
  pairEntry 6 9 (by decide) ⟨0, 0, -15554, -65828, 215475, by decide⟩, -- source row 1658
  pairEntry 7 10 (by decide) ⟨5555, 23510, 46662, 197484, 430950, by decide⟩, -- source row 1690
  pairEntry 7 11 (by decide) ⟨5555, 23510, 15554, 65828, 215475, by decide⟩, -- source row 1691
  pairEntry 8 10 (by decide) ⟨5555, 23510, 15554, 65828, 215475, by decide⟩, -- source row 1720
  pairEntry 8 11 (by decide) ⟨5555, 23510, 15554, 65828, 430950, by decide⟩, -- source row 1721
  pairEntry 12 21 (by decide) ⟨-691, 3988, 0, 0, 11050, by decide⟩, -- source row 1841
  pairEntry 12 22 (by decide) ⟨-2073, 11964, 5716, 11187, 66300, by decide⟩, -- source row 1842
  pairEntry 12 24 (by decide) ⟨-3936, 648, -3772, 621, 33150, by decide⟩, -- source row 1844
  pairEntry 12 25 (by decide) ⟨-1312, 216, 0, 0, 5525, by decide⟩, -- source row 1845
  pairEntry 12 27 (by decide) ⟨-3936, 648, 3772, -621, 33150, by decide⟩, -- source row 1847
  pairEntry 12 28 (by decide) ⟨3936, -648, 3772, -621, 33150, by decide⟩, -- source row 1848
  pairEntry 12 30 (by decide) ⟨2079237, 1183604, 0, 0, 14163890, by decide⟩, -- source row 1850
  pairEntry 12 31 (by decide) ⟨31188555, 17754060, 26551628, -24059979, 424916700, by decide⟩, -- source row 1851
  pairEntry 12 33 (by decide) ⟨28214442, 21155544, 1133828, 991371, 212458350, by decide⟩, -- source row 1853
  pairEntry 12 34 (by decide) ⟨10811313, 9101556, -4217456, 5683008, 42491670, by decide⟩, -- source row 1854
  pairEntry 12 36 (by decide) ⟨28214442, 21155544, -1133828, -991371, 212458350, by decide⟩, -- source row 1856
  pairEntry 12 37 (by decide) ⟨-8614041, -8117412, -7407036, 9141223, 70819450, by decide⟩, -- source row 1857
  pairEntry 13 21 (by decide) ⟨-2073, 11964, -5716, -11187, 66300, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨-691, 3988, 0, 0, 11050, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨3936, -648, -3772, 621, 33150, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨-3936, 648, -3772, 621, 33150, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨-1312, 216, 0, 0, 5525, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨-3936, 648, 3772, -621, 33150, by decide⟩, -- source row 1873
  pairEntry 13 30 (by decide) ⟨31188555, 17754060, -26551628, 24059979, 424916700, by decide⟩, -- source row 1875
  pairEntry 13 31 (by decide) ⟨2079237, 1183604, 0, 0, 14163890, by decide⟩, -- source row 1876
  pairEntry 13 33 (by decide) ⟨-8614041, -8117412, 7407036, -9141223, 70819450, by decide⟩, -- source row 1878
  pairEntry 13 34 (by decide) ⟨28214442, 21155544, 1133828, 991371, 212458350, by decide⟩, -- source row 1879
  pairEntry 13 36 (by decide) ⟨10811313, 9101556, 4217456, -5683008, 42491670, by decide⟩, -- source row 1881
  pairEntry 13 37 (by decide) ⟨28214442, 21155544, -1133828, -991371, 212458350, by decide⟩, -- source row 1882
  pairEntry 15 21 (by decide) ⟨-17817, 14556, -3124, 4557, 66300, by decide⟩, -- source row 1913
  pairEntry 15 22 (by decide) ⟨-7872, 1296, 4420, 3315, 33150, by decide⟩, -- source row 1914
  pairEntry 15 24 (by decide) ⟨-656, 108, -108, -656, 5525, by decide⟩, -- source row 1916
  pairEntry 15 25 (by decide) ⟨-2073, 11964, 3124, -4557, 66300, by decide⟩, -- source row 1917
  pairEntry 15 27 (by decide) ⟨5799, 10668, 4420, 3315, 66300, by decide⟩, -- source row 1919
  pairEntry 15 28 (by decide) ⟨656, -108, 108, 656, 5525, by decide⟩, -- source row 1920
  pairEntry 15 30 (by decide) ⟨-6237711, -3550812, -13319012, 16494321, 84983340, by decide⟩, -- source row 1922
  pairEntry 15 31 (by decide) ⟨-4702407, -3525924, -3881112, 4438816, 35409725, by decide⟩, -- source row 1923
  pairEntry 15 33 (by decide) ⟨-18018855, -15169260, 355188, 263591, 70819450, by decide⟩, -- source row 1925
  pairEntry 15 34 (by decide) ⟨-27860337, -21753924, 4884100, -5128305, 84983340, by decide⟩, -- source row 1926
  pairEntry 15 36 (by decide) ⟨25842123, 24352236, 2199392, 1782144, 212458350, by decide⟩, -- source row 1928
  pairEntry 15 37 (by decide) ⟨20495691, 30950412, 22152844, -27624267, 424916700, by decide⟩, -- source row 1929
  pairEntry 16 21 (by decide) ⟨-691, 3988, -3988, -691, 22100, by decide⟩, -- source row 1935
  pairEntry 16 22 (by decide) ⟨-17817, 14556, -3124, 4557, 66300, by decide⟩, -- source row 1936
  pairEntry 16 24 (by decide) ⟨-5799, -10668, -4420, -3315, 66300, by decide⟩, -- source row 1938
  pairEntry 16 25 (by decide) ⟨-656, 108, -108, -656, 5525, by decide⟩, -- source row 1939
  pairEntry 16 27 (by decide) ⟨-2073, 11964, 3124, -4557, 66300, by decide⟩, -- source row 1941
  pairEntry 16 28 (by decide) ⟨5799, 10668, 4420, 3315, 66300, by decide⟩, -- source row 1942
  pairEntry 16 30 (by decide) ⟨25240329, 24557028, -20021716, 29205813, 424916700, by decide⟩, -- source row 1944
  pairEntry 16 31 (by decide) ⟨-6237711, -3550812, -13319012, 16494321, 84983340, by decide⟩, -- source row 1945
  pairEntry 16 33 (by decide) ⟨31188555, 17754060, -22289372, 27223071, 424916700, by decide⟩, -- source row 1947
  pairEntry 16 34 (by decide) ⟨-18018855, -15169260, 355188, 263591, 70819450, by decide⟩, -- source row 1948
  pairEntry 16 36 (by decide) ⟨2079237, 1183604, -1183604, 2079237, 28327780, by decide⟩, -- source row 1950
  pairEntry 16 37 (by decide) ⟨25842123, 24352236, 2199392, 1782144, 212458350, by decide⟩, -- source row 1951
  pairEntry 18 21 (by decide) ⟨-17817, 14556, 3124, -4557, 66300, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨-691, 3988, 3988, 691, 22100, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨5799, 10668, -4420, -3315, 66300, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨-2073, 11964, -3124, 4557, 66300, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨-656, 108, 108, 656, 5525, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨-5799, -10668, 4420, 3315, 66300, by decide⟩, -- source row 1983
  pairEntry 18 30 (by decide) ⟨-6237711, -3550812, 13319012, -16494321, 84983340, by decide⟩, -- source row 1985
  pairEntry 18 31 (by decide) ⟨25240329, 24557028, 20021716, -29205813, 424916700, by decide⟩, -- source row 1986
  pairEntry 18 33 (by decide) ⟨25842123, 24352236, -2199392, -1782144, 212458350, by decide⟩, -- source row 1988
  pairEntry 18 34 (by decide) ⟨2079237, 1183604, 1183604, -2079237, 28327780, by decide⟩, -- source row 1989
  pairEntry 18 36 (by decide) ⟨-18018855, -15169260, -355188, -263591, 70819450, by decide⟩, -- source row 1991
  pairEntry 18 37 (by decide) ⟨31188555, 17754060, 22289372, -27223071, 424916700, by decide⟩, -- source row 1992
  pairEntry 19 21 (by decide) ⟨-7872, 1296, -4420, -3315, 33150, by decide⟩, -- source row 1995
  pairEntry 19 22 (by decide) ⟨-17817, 14556, 3124, -4557, 66300, by decide⟩, -- source row 1996
  pairEntry 19 24 (by decide) ⟨656, -108, -108, -656, 5525, by decide⟩, -- source row 1998
  pairEntry 19 25 (by decide) ⟨5799, 10668, -4420, -3315, 66300, by decide⟩, -- source row 1999
  pairEntry 19 27 (by decide) ⟨-2073, 11964, -3124, 4557, 66300, by decide⟩, -- source row 2001
  pairEntry 19 28 (by decide) ⟨-656, 108, 108, 656, 5525, by decide⟩, -- source row 2002
  pairEntry 19 30 (by decide) ⟨-4702407, -3525924, 3881112, -4438816, 35409725, by decide⟩, -- source row 2004
  pairEntry 19 31 (by decide) ⟨-6237711, -3550812, 13319012, -16494321, 84983340, by decide⟩, -- source row 2005
  pairEntry 19 33 (by decide) ⟨20495691, 30950412, -22152844, 27624267, 424916700, by decide⟩, -- source row 2007
  pairEntry 19 34 (by decide) ⟨25842123, 24352236, -2199392, -1782144, 212458350, by decide⟩, -- source row 2008
  pairEntry 19 36 (by decide) ⟨-27860337, -21753924, -4884100, 5128305, 84983340, by decide⟩, -- source row 2010
  pairEntry 19 37 (by decide) ⟨-18018855, -15169260, -355188, -263591, 70819450, by decide⟩, -- source row 2011
  pairEntry 21 30 (by decide) ⟨-21093, 24124, 0, 0, 64090, by decide⟩, -- source row 2039
  pairEntry 21 31 (by decide) ⟨-63279, 72372, 24124, 21093, 384540, by decide⟩, -- source row 2040
  pairEntry 21 33 (by decide) ⟨21093, -24124, -24124, -21093, 128180, by decide⟩, -- source row 2042
  pairEntry 21 34 (by decide) ⟨0, 0, -24124, -21093, 192270, by decide⟩, -- source row 2043
  pairEntry 21 36 (by decide) ⟨21093, -24124, 24124, 21093, 128180, by decide⟩, -- source row 2045
  pairEntry 21 37 (by decide) ⟨63279, -72372, 24124, 21093, 384540, by decide⟩, -- source row 2046
  pairEntry 22 30 (by decide) ⟨-63279, 72372, -24124, -21093, 384540, by decide⟩, -- source row 2055
  pairEntry 22 31 (by decide) ⟨-21093, 24124, 0, 0, 64090, by decide⟩, -- source row 2056
  pairEntry 22 33 (by decide) ⟨63279, -72372, -24124, -21093, 384540, by decide⟩, -- source row 2058
  pairEntry 22 34 (by decide) ⟨21093, -24124, -24124, -21093, 128180, by decide⟩, -- source row 2059
  pairEntry 22 36 (by decide) ⟨0, 0, 24124, 21093, 192270, by decide⟩, -- source row 2061
  pairEntry 22 37 (by decide) ⟨21093, -24124, 24124, 21093, 128180, by decide⟩, -- source row 2062
  pairEntry 24 31 (by decide) ⟨63279, -72372, 24124, 21093, 384540, by decide⟩, -- source row 2085
  pairEntry 24 34 (by decide) ⟨-63279, 72372, 24124, 21093, 384540, by decide⟩, -- source row 2088
  pairEntry 24 37 (by decide) ⟨0, 0, -24124, -21093, 192270, by decide⟩, -- source row 2091
  pairEntry 25 30 (by decide) ⟨-63279, 72372, -24124, -21093, 384540, by decide⟩, -- source row 2097
  pairEntry 25 33 (by decide) ⟨63279, -72372, -24124, -21093, 384540, by decide⟩, -- source row 2100
  pairEntry 25 36 (by decide) ⟨0, 0, 24124, 21093, 192270, by decide⟩, -- source row 2103
  pairEntry 27 31 (by decide) ⟨-63279, 72372, 24124, 21093, 384540, by decide⟩, -- source row 2121
  pairEntry 27 34 (by decide) ⟨0, 0, -24124, -21093, 192270, by decide⟩, -- source row 2124
  pairEntry 27 37 (by decide) ⟨63279, -72372, 24124, 21093, 384540, by decide⟩, -- source row 2127
  pairEntry 28 30 (by decide) ⟨63279, -72372, -24124, -21093, 384540, by decide⟩, -- source row 2130
  pairEntry 28 33 (by decide) ⟨0, 0, 24124, 21093, 192270, by decide⟩, -- source row 2133
  pairEntry 28 36 (by decide) ⟨-63279, 72372, -24124, -21093, 384540, by decide⟩ -- source row 2136
]

end Option2.NativeStress.NativeT

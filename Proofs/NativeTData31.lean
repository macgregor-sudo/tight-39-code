module

public import NativeHWeights

@[expose] public section

/-! Exact source λ13; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda13 : List Entry := [
  idEntry 0 0 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 0
  idEntry 0 1 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 1
  idEntry 0 2 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 2
  idEntry 0 23 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 23
  idEntry 0 24 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 24
  idEntry 1 0 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 28
  idEntry 1 2 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 29
  idEntry 2 0 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 54
  idEntry 2 1 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 55
  idEntry 2 2 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 56
  idEntry 3 0 ⟨-3, -6, -2, 1, 30, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-3, -6, -2, 1, 30, by decide⟩, -- source row 82
  idEntry 3 2 ⟨3, 6, 2, -1, 10, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-6, -12, -4, 2, 15, by decide⟩, -- source row 84
  idEntry 3 7 ⟨7, 4, 4, 3, 20, by decide⟩, -- source row 88
  idEntry 3 8 ⟨-4, -13, -3, 4, 20, by decide⟩, -- source row 89
  idEntry 4 0 ⟨9, -12, 4, 13, 60, by decide⟩, -- source row 108
  idEntry 4 1 ⟨9, -12, 4, 13, 60, by decide⟩, -- source row 109
  idEntry 4 2 ⟨-9, 12, -4, -13, 20, by decide⟩, -- source row 110
  idEntry 4 3 ⟨-9, 12, -4, -13, 30, by decide⟩, -- source row 111
  idEntry 4 4 ⟨-4, -13, -3, 4, 10, by decide⟩, -- source row 112
  idEntry 4 7 ⟨1, -8, 0, 5, 20, by decide⟩, -- source row 115
  idEntry 4 8 ⟨8, 11, 5, 0, 20, by decide⟩, -- source row 116
  idEntry 5 7 ⟨-2, 1, -1, -2, 5, by decide⟩, -- source row 142
  idEntry 5 8 ⟨-2, 1, -1, -2, 10, by decide⟩, -- source row 143
  idEntry 6 0 ⟨9, -12, -4, -13, 60, by decide⟩, -- source row 162
  idEntry 6 1 ⟨9, -12, -4, -13, 60, by decide⟩, -- source row 163
  idEntry 6 2 ⟨-9, 12, 4, 13, 20, by decide⟩, -- source row 164
  idEntry 6 3 ⟨9, -12, -4, -13, 15, by decide⟩, -- source row 165
  idEntry 6 7 ⟨7, 4, -4, -3, 20, by decide⟩, -- source row 169
  idEntry 6 8 ⟨-4, -13, 3, -4, 20, by decide⟩, -- source row 170
  idEntry 7 0 ⟨-3, -6, 2, -1, 30, by decide⟩, -- source row 189
  idEntry 7 1 ⟨-3, -6, 2, -1, 30, by decide⟩, -- source row 190
  idEntry 7 2 ⟨3, 6, -2, 1, 10, by decide⟩, -- source row 191
  idEntry 7 3 ⟨3, 6, -2, 1, 15, by decide⟩, -- source row 192
  idEntry 7 4 ⟨-2, 1, 1, 2, 5, by decide⟩, -- source row 193
  idEntry 7 7 ⟨-2, 1, 1, 2, 5, by decide⟩, -- source row 196
  idEntry 7 8 ⟨-2, 1, 1, 2, 10, by decide⟩, -- source row 197
  idEntry 8 7 ⟨1, -8, 0, -5, 20, by decide⟩, -- source row 223
  idEntry 8 8 ⟨8, 11, -5, 0, 20, by decide⟩, -- source row 224
  idEntry 9 0 ⟨12, -6, -2, 1, 30, by decide⟩, -- source row 243
  idEntry 9 1 ⟨12, -6, -2, 1, 30, by decide⟩, -- source row 244
  idEntry 9 2 ⟨-12, 6, 2, -1, 10, by decide⟩, -- source row 245
  idEntry 9 3 ⟨24, -12, -4, 2, 15, by decide⟩, -- source row 246
  idEntry 9 7 ⟨4, -2, 0, 0, 5, by decide⟩, -- source row 250
  idEntry 9 8 ⟨2, -1, 0, 0, 5, by decide⟩, -- source row 251
  idEntry 10 0 ⟨12, -6, 2, -1, 30, by decide⟩, -- source row 270
  idEntry 10 1 ⟨12, -6, 2, -1, 30, by decide⟩, -- source row 271
  idEntry 10 2 ⟨-12, 6, -2, 1, 10, by decide⟩, -- source row 272
  idEntry 10 3 ⟨-12, 6, -2, 1, 15, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-2, 1, -4, 2, 5, by decide⟩, -- source row 274
  idEntry 10 7 ⟨-4, 2, -2, 1, 10, by decide⟩, -- source row 277
  idEntry 10 8 ⟨-2, 1, 4, -2, 10, by decide⟩, -- source row 278
  idEntry 11 7 ⟨-4, 2, 2, -1, 10, by decide⟩, -- source row 304
  idEntry 11 8 ⟨-2, 1, -4, 2, 10, by decide⟩, -- source row 305
  idEntry 12 0 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 324
  idEntry 12 1 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 325
  idEntry 12 2 ⟨-9, 12, -4, -3, 20, by decide⟩, -- source row 326
  idEntry 12 3 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 327
  idEntry 12 4 ⟨4, 3, 3, -4, 20, by decide⟩, -- source row 328
  idEntry 12 5 ⟨-9, 12, -4, -3, 15, by decide⟩, -- source row 329
  idEntry 12 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 333
  idEntry 12 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 334
  idEntry 13 0 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 351
  idEntry 13 1 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 352
  idEntry 13 2 ⟨0, 0, -4, -3, 10, by decide⟩, -- source row 353
  idEntry 13 3 ⟨-3, 4, -4, -3, 20, by decide⟩, -- source row 354
  idEntry 13 4 ⟨4, 3, -3, 4, 20, by decide⟩, -- source row 355
  idEntry 13 5 ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-4, -3, 0, 0, 5, by decide⟩, -- source row 357
  idEntry 13 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 360
  idEntry 13 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 361
  idEntry 14 3 ⟨3, -4, 0, 0, 10, by decide⟩, -- source row 381
  idEntry 14 4 ⟨-4, -3, 0, 0, 10, by decide⟩, -- source row 382
  idEntry 14 9 ⟨-1, 0, 0, 0, 2, by decide⟩, -- source row 387
  idEntry 14 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 388
  idEntry 15 0 ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 406
  idEntry 15 2 ⟨9, -12, -4, -3, 20, by decide⟩, -- source row 407
  idEntry 15 3 ⟨-3, 4, -4, -3, 20, by decide⟩, -- source row 408
  idEntry 15 4 ⟨4, 3, -3, 4, 20, by decide⟩, -- source row 409
  idEntry 15 5 ⟨9, -12, -4, -3, 15, by decide⟩, -- source row 410
  idEntry 15 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 414
  idEntry 15 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 415
  idEntry 16 0 ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 432
  idEntry 16 1 ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 433
  idEntry 16 2 ⟨9, -12, 4, 3, 20, by decide⟩, -- source row 434
  idEntry 16 3 ⟨3, -4, 0, 0, 10, by decide⟩, -- source row 435
  idEntry 16 4 ⟨-4, -3, 0, 0, 10, by decide⟩, -- source row 436
  idEntry 16 5 ⟨-9, 12, -4, -3, 30, by decide⟩, -- source row 437
  idEntry 16 6 ⟨4, 3, 3, -4, 10, by decide⟩, -- source row 438
  idEntry 16 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 441
  idEntry 16 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 442
  idEntry 17 3 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 462
  idEntry 17 4 ⟨4, 3, 3, -4, 20, by decide⟩, -- source row 463
  idEntry 17 9 ⟨1, 0, 0, -1, 4, by decide⟩, -- source row 468
  idEntry 17 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 469
  idEntry 18 0 ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 486
  idEntry 18 1 ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 487
  idEntry 18 2 ⟨0, 0, 4, 3, 10, by decide⟩, -- source row 488
  idEntry 18 3 ⟨3, -4, 0, 0, 10, by decide⟩, -- source row 489
  idEntry 18 4 ⟨-4, -3, 0, 0, 10, by decide⟩, -- source row 490
  idEntry 18 5 ⟨0, 0, 8, 6, 15, by decide⟩, -- source row 491
  idEntry 18 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 495
  idEntry 18 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 496
  idEntry 19 0 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 513
  idEntry 19 1 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 514
  idEntry 19 2 ⟨-9, 12, 4, 3, 20, by decide⟩, -- source row 515
  idEntry 19 3 ⟨-3, 4, 4, 3, 20, by decide⟩, -- source row 516
  idEntry 19 4 ⟨4, 3, 3, -4, 20, by decide⟩, -- source row 517
  idEntry 19 5 ⟨9, -12, -4, -3, 30, by decide⟩, -- source row 518
  idEntry 19 6 ⟨4, 3, -3, 4, 10, by decide⟩, -- source row 519
  idEntry 19 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 522
  idEntry 19 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 523
  idEntry 20 3 ⟨-3, 4, -4, -3, 20, by decide⟩, -- source row 543
  idEntry 20 4 ⟨4, 3, -3, 4, 20, by decide⟩, -- source row 544
  idEntry 20 9 ⟨1, 0, 0, 1, 4, by decide⟩, -- source row 549
  idEntry 20 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 550
  idEntry 21 0 ⟨3, -54, 18, 1, 130, by decide⟩, -- source row 567
  idEntry 21 1 ⟨3, -54, 18, 1, 130, by decide⟩, -- source row 568
  idEntry 21 2 ⟨-9, 162, -54, -3, 130, by decide⟩, -- source row 569
  idEntry 21 3 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 570
  idEntry 21 4 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 571
  idEntry 21 5 ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 572
  idEntry 21 6 ⟨56, -33, -33, -56, 260, by decide⟩, -- source row 573
  idEntry 21 7 ⟨-18, 324, -108, -6, 325, by decide⟩, -- source row 574
  idEntry 21 8 ⟨-24, 432, -144, -8, 325, by decide⟩, -- source row 575
  idEntry 22 0 ⟨3, -54, -18, -1, 130, by decide⟩, -- source row 594
  idEntry 22 1 ⟨3, -54, -18, -1, 130, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-9, 162, 54, 3, 130, by decide⟩, -- source row 596
  idEntry 22 3 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 597
  idEntry 22 4 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 598
  idEntry 22 5 ⟨-33, -56, 0, 0, 130, by decide⟩, -- source row 599
  idEntry 22 6 ⟨-56, 33, 0, 0, 130, by decide⟩, -- source row 600
  idEntry 22 7 ⟨-207, -174, -42, -219, 325, by decide⟩, -- source row 601
  idEntry 22 8 ⟨174, -207, -81, 158, 325, by decide⟩, -- source row 602
  idEntry 23 3 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 624
  idEntry 23 4 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 625
  idEntry 23 5 ⟨33, 56, -56, 33, 260, by decide⟩, -- source row 626
  idEntry 23 6 ⟨56, -33, 33, 56, 260, by decide⟩, -- source row 627
  idEntry 24 0 ⟨39, -52, -20, 35, 260, by decide⟩, -- source row 648
  idEntry 24 1 ⟨39, -52, -20, 35, 260, by decide⟩, -- source row 649
  idEntry 24 2 ⟨-117, 156, 60, -105, 260, by decide⟩, -- source row 650
  idEntry 24 3 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 651
  idEntry 24 4 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 652
  idEntry 24 5 ⟨-33, -56, 0, 0, 130, by decide⟩, -- source row 653
  idEntry 24 6 ⟨-56, 33, 0, 0, 130, by decide⟩, -- source row 654
  idEntry 24 7 ⟨-117, 156, 60, -105, 325, by decide⟩, -- source row 655
  idEntry 24 8 ⟨-156, 208, 80, -140, 325, by decide⟩, -- source row 656
  idEntry 25 0 ⟨36, 2, -18, -1, 130, by decide⟩, -- source row 675
  idEntry 25 1 ⟨36, 2, -18, -1, 130, by decide⟩, -- source row 676
  idEntry 25 2 ⟨-108, -6, 54, 3, 130, by decide⟩, -- source row 677
  idEntry 25 3 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 678
  idEntry 25 4 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 679
  idEntry 25 5 ⟨33, 56, -56, 33, 260, by decide⟩, -- source row 680
  idEntry 25 6 ⟨56, -33, 33, 56, 260, by decide⟩, -- source row 681
  idEntry 25 7 ⟨-108, -6, 90, 5, 325, by decide⟩, -- source row 682
  idEntry 25 8 ⟨306, 17, -180, -10, 325, by decide⟩, -- source row 683
  idEntry 26 3 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 705
  idEntry 26 4 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 706
  idEntry 26 5 ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 707
  idEntry 26 6 ⟨56, -33, -33, -56, 260, by decide⟩, -- source row 708
  idEntry 27 0 ⟨36, 2, 18, 1, 130, by decide⟩, -- source row 729
  idEntry 27 1 ⟨36, 2, 18, 1, 130, by decide⟩, -- source row 730
  idEntry 27 2 ⟨-108, -6, -54, -3, 130, by decide⟩, -- source row 731
  idEntry 27 3 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 732
  idEntry 27 4 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 733
  idEntry 27 5 ⟨33, 56, -56, 33, 260, by decide⟩, -- source row 734
  idEntry 27 6 ⟨56, -33, 33, 56, 260, by decide⟩, -- source row 735
  idEntry 27 7 ⟨-216, -12, -108, -6, 325, by decide⟩, -- source row 736
  idEntry 27 8 ⟨-288, -16, -144, -8, 325, by decide⟩, -- source row 737
  idEntry 28 0 ⟨39, -52, 20, -35, 260, by decide⟩, -- source row 756
  idEntry 28 1 ⟨39, -52, 20, -35, 260, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-117, 156, -60, 105, 260, by decide⟩, -- source row 758
  idEntry 28 3 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 759
  idEntry 28 4 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 760
  idEntry 28 5 ⟨33, 56, 56, -33, 260, by decide⟩, -- source row 761
  idEntry 28 6 ⟨56, -33, -33, -56, 260, by decide⟩, -- source row 762
  idEntry 28 7 ⟨357, -576, 216, -313, 650, by decide⟩, -- source row 763
  idEntry 28 8 ⟨-24, 107, -37, 16, 650, by decide⟩, -- source row 764
  idEntry 29 3 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 786
  idEntry 29 4 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 787
  idEntry 29 5 ⟨-33, -56, 0, 0, 130, by decide⟩, -- source row 788
  idEntry 29 6 ⟨-56, 33, 0, 0, 130, by decide⟩, -- source row 789
  idEntry 30 0 ⟨-1407, -2024, -2024, 1407, 14790, by decide⟩, -- source row 810
  idEntry 30 1 ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-1407, -2024, 2024, -1407, 14790, by decide⟩, -- source row 812
  idEntry 30 9 ⟨-37297, -19104, 21376, 9157, 167620, by decide⟩, -- source row 819
  idEntry 30 10 ⟨-57312, 111891, 47123, 102336, 502860, by decide⟩, -- source row 820
  idEntry 31 0 ⟨-1407, -2024, 2024, -1407, 14790, by decide⟩, -- source row 837
  idEntry 31 1 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-1407, -2024, 0, 0, 14790, by decide⟩, -- source row 839
  idEntry 31 9 ⟨-37297, -19104, 21376, 9157, 167620, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-57312, 111891, 47123, 102336, 502860, by decide⟩, -- source row 847
  idEntry 32 0 ⟨4221, 6072, -2024, 1407, 14790, by decide⟩, -- source row 864
  idEntry 32 1 ⟨0, 0, -2024, 1407, 14790, by decide⟩, -- source row 865
  idEntry 32 2 ⟨-1407, -2024, 4048, -2814, 14790, by decide⟩, -- source row 866
  idEntry 32 9 ⟨166833, -70944, -102336, 47123, 502860, by decide⟩, -- source row 873
  idEntry 32 10 ⟨261984, -206137, 27471, -64128, 502860, by decide⟩, -- source row 874
  idEntry 33 0 ⟨4221, 6072, -2024, 1407, 29580, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-4221, -6072, -2024, 1407, 29580, by decide⟩, -- source row 892
  idEntry 33 2 ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 893
  idEntry 33 9 ⟨30262, 8984, 10120, -7035, 83810, by decide⟩, -- source row 900
  idEntry 33 10 ⟨68568, -95699, -16192, 11256, 251430, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-1407, -2024, -2024, 1407, 14790, by decide⟩, -- source row 918
  idEntry 34 1 ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 919
  idEntry 34 2 ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 920
  idEntry 34 9 ⟨16192, -11256, -10120, 7035, 83810, by decide⟩, -- source row 927
  idEntry 34 10 ⟨91080, -63315, 16192, -11256, 251430, by decide⟩, -- source row 928
  idEntry 35 0 ⟨-1407, -2024, 6072, -4221, 29580, by decide⟩, -- source row 945
  idEntry 35 1 ⟨1407, 2024, 0, 0, 14790, by decide⟩, -- source row 946
  idEntry 35 2 ⟨-1407, -2024, 0, 0, 14790, by decide⟩, -- source row 947
  idEntry 35 9 ⟨21105, 30360, -11256, -16192, 251430, by decide⟩, -- source row 954
  idEntry 35 10 ⟨-11256, -16192, -21105, -30360, 251430, by decide⟩, -- source row 955
  idEntry 36 0 ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 972
  idEntry 36 1 ⟨2814, 4048, -2024, 1407, 14790, by decide⟩, -- source row 973
  idEntry 36 2 ⟨-4221, -6072, 2024, -1407, 29580, by decide⟩, -- source row 974
  idEntry 36 9 ⟨-65437, -59584, 19104, -37297, 167620, by decide⟩, -- source row 981
  idEntry 36 10 ⟨-12288, 176659, -111891, -57312, 502860, by decide⟩, -- source row 982
  idEntry 37 0 ⟨4221, 6072, 2024, -1407, 29580, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-4221, -6072, 2024, -1407, 29580, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨4221, 6072, -2024, 1407, 29580, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨111891, 57312, -25920, -102065, 502860, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨57312, -111891, -121717, -140544, 502860, by decide⟩, -- source row 1009
  idEntry 38 0 ⟨-2814, -4048, -2024, 1407, 14790, by decide⟩, -- source row 1026
  idEntry 38 1 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 1027
  idEntry 38 9 ⟨-27471, 64128, -19104, 37297, 502860, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨-102336, 47123, 37297, 19104, 502860, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨27471, -64128, 19104, -37297, 502860, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨102336, -47123, -37297, -19104, 502860, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨12144, -8442, -2814, -4048, 128673, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨-42504, 29547, 9849, 14168, 428910, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨-1165317, 344756, 533212, 97659, 14582940, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨1034268, 3495951, -2623611, 2289148, 43748820, by decide⟩, -- source row 1116
  sumEntry 1 7 ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1126
  sumEntry 1 8 ⟨-2, 1, -1, -2, 30, by decide⟩, -- source row 1127
  sumEntry 1 15 ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1134
  sumEntry 1 16 ⟨-8, -11, -5, 0, 60, by decide⟩, -- source row 1135
  sumEntry 1 23 ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1142
  sumEntry 1 24 ⟨-4, -13, -3, 4, 60, by decide⟩, -- source row 1143
  sumEntry 2 7 ⟨1, -8, 0, -5, 60, by decide⟩, -- source row 1153
  sumEntry 2 8 ⟨8, 11, -5, 0, 60, by decide⟩, -- source row 1154
  sumEntry 2 15 ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1161
  sumEntry 2 16 ⟨-8, -11, 5, 0, 60, by decide⟩, -- source row 1162
  sumEntry 2 23 ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1169
  sumEntry 2 24 ⟨-2, 1, 1, 2, 30, by decide⟩, -- source row 1170
  sumEntry 3 7 ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1180
  sumEntry 3 8 ⟨-2, 1, -4, 2, 30, by decide⟩, -- source row 1181
  sumEntry 3 15 ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1188
  sumEntry 3 16 ⟨-2, 1, 0, 0, 15, by decide⟩, -- source row 1189
  sumEntry 3 23 ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1196
  sumEntry 3 24 ⟨-2, 1, -4, 2, 30, by decide⟩, -- source row 1197
  sumEntry 4 3 ⟨3, -4, 0, 0, 30, by decide⟩, -- source row 1203
  sumEntry 4 4 ⟨-4, -3, 0, 0, 30, by decide⟩, -- source row 1204
  sumEntry 4 9 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1209
  sumEntry 4 10 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1210
  sumEntry 4 11 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1211
  sumEntry 4 12 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1212
  sumEntry 4 17 ⟨-3, 4, -4, -3, 60, by decide⟩, -- source row 1217
  sumEntry 4 18 ⟨-4, -3, 3, -4, 60, by decide⟩, -- source row 1218
  sumEntry 4 21 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1221
  sumEntry 4 22 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1222
  sumEntry 4 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1223
  sumEntry 4 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1224
  sumEntry 5 3 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1230
  sumEntry 5 4 ⟨4, 3, 3, -4, 60, by decide⟩, -- source row 1231
  sumEntry 5 9 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1236
  sumEntry 5 10 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1237
  sumEntry 5 11 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1238
  sumEntry 5 12 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1239
  sumEntry 5 17 ⟨-3, 4, -4, -3, 60, by decide⟩, -- source row 1244
  sumEntry 5 18 ⟨-4, -3, 3, -4, 60, by decide⟩, -- source row 1245
  sumEntry 5 21 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1248
  sumEntry 5 22 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1249
  sumEntry 5 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1250
  sumEntry 5 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1251
  sumEntry 6 3 ⟨-3, 4, -4, -3, 60, by decide⟩, -- source row 1257
  sumEntry 6 4 ⟨4, 3, -3, 4, 60, by decide⟩, -- source row 1258
  sumEntry 6 9 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1263
  sumEntry 6 10 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1264
  sumEntry 6 11 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1265
  sumEntry 6 12 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1266
  sumEntry 6 17 ⟨-3, 4, -4, -3, 60, by decide⟩, -- source row 1271
  sumEntry 6 18 ⟨-4, -3, 3, -4, 60, by decide⟩, -- source row 1272
  sumEntry 6 21 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1275
  sumEntry 6 22 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1276
  sumEntry 6 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1277
  sumEntry 6 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1278
  sumEntry 7 3 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1284
  sumEntry 7 4 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1285
  sumEntry 7 5 ⟨33, 56, -56, 33, 780, by decide⟩, -- source row 1286
  sumEntry 7 6 ⟨56, -33, 33, 56, 780, by decide⟩, -- source row 1287
  sumEntry 7 11 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1292
  sumEntry 7 12 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1293
  sumEntry 7 13 ⟨323, 36, 0, 0, 1950, by decide⟩, -- source row 1294
  sumEntry 7 14 ⟨36, -323, 0, 0, 1950, by decide⟩, -- source row 1295
  sumEntry 7 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1304
  sumEntry 7 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1305
  sumEntry 7 25 ⟨-33, -56, 56, -33, 780, by decide⟩, -- source row 1306
  sumEntry 7 26 ⟨-56, 33, -33, -56, 780, by decide⟩, -- source row 1307
  sumEntry 8 3 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1311
  sumEntry 8 4 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1312
  sumEntry 8 5 ⟨33, 56, 56, -33, 780, by decide⟩, -- source row 1313
  sumEntry 8 6 ⟨56, -33, -33, -56, 780, by decide⟩, -- source row 1314
  sumEntry 8 11 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1319
  sumEntry 8 12 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1320
  sumEntry 8 13 ⟨-323, -36, 36, -323, 3900, by decide⟩, -- source row 1321
  sumEntry 8 14 ⟨-36, 323, -323, -36, 3900, by decide⟩, -- source row 1322
  sumEntry 8 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1331
  sumEntry 8 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1332
  sumEntry 8 25 ⟨-33, -56, -56, 33, 780, by decide⟩, -- source row 1333
  sumEntry 8 26 ⟨-56, 33, 33, 56, 780, by decide⟩, -- source row 1334
  sumEntry 9 3 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1338
  sumEntry 9 4 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1339
  sumEntry 9 5 ⟨-33, -56, 0, 0, 390, by decide⟩, -- source row 1340
  sumEntry 9 6 ⟨-56, 33, 0, 0, 390, by decide⟩, -- source row 1341
  sumEntry 9 11 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1346
  sumEntry 9 12 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1347
  sumEntry 9 13 ⟨-323, -36, -36, 323, 3900, by decide⟩, -- source row 1348
  sumEntry 9 14 ⟨-36, 323, 323, 36, 3900, by decide⟩, -- source row 1349
  sumEntry 9 23 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1358
  sumEntry 9 24 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1359
  sumEntry 9 25 ⟨33, 56, 0, 0, 390, by decide⟩, -- source row 1360
  sumEntry 9 26 ⟨56, -33, 0, 0, 390, by decide⟩, -- source row 1361
  sumEntry 10 0 ⟨1407, 2024, 0, 0, 14790, by decide⟩, -- source row 1362
  sumEntry 10 1 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 1363
  sumEntry 10 2 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨-111891, -57312, 147360, 17645, 1508580, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨-19104, 37297, 18983, 61856, 502860, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨-210081, -43092, 56280, 80960, 1286730, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨14364, -70027, -19698, -28336, 428910, by decide⟩, -- source row 1376
  sumEntry 11 0 ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 1389
  sumEntry 11 9 ⟨82413, -192384, -102336, 47123, 1508580, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨102336, -47123, 9157, -21376, 502860, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨0, 0, 99372, -129121, 1286730, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨0, 0, 50329, -13972, 428910, by decide⟩, -- source row 1403
  sumEntry 12 0 ⟨-1407, -2024, 0, 0, 14790, by decide⟩, -- source row 1416
  sumEntry 12 9 ⟨51, 432, -144, 17, 1740, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨-432, 51, -17, -144, 1740, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨29547, 42504, 28140, 40480, 428910, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨28140, 40480, -29547, -42504, 428910, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨-1407, -2024, 0, 0, 7395, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨-1407, -2024, 0, 0, 14790, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 1474
  pairEntry 0 33 (by decide) ⟨4221, 6072, -2024, 1407, 29580, by decide⟩, -- source row 1475
  pairEntry 0 34 (by decide) ⟨0, 0, -2024, 1407, 14790, by decide⟩, -- source row 1476
  pairEntry 0 36 (by decide) ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨7035, 10120, -2024, 1407, 29580, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 1480
  pairEntry 1 31 (by decide) ⟨1407, 2024, -2024, 1407, 14790, by decide⟩, -- source row 1510
  pairEntry 1 37 (by decide) ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨1407, 2024, -2024, 1407, 14790, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 1552
  pairEntry 3 12 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨-7, -4, -4, -3, 60, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨1, -8, 0, 5, 60, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨2, -1, 1, 2, 15, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1569
  pairEntry 3 21 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1575
  pairEntry 3 27 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1577
  pairEntry 3 28 (by decide) ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1578
  pairEntry 4 12 (by decide) ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨-7, -4, -4, -3, 60, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨1, -8, 0, 5, 60, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨2, -1, 1, 2, 15, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨7, 4, 4, 3, 60, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1603
  pairEntry 4 21 (by decide) ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1609
  pairEntry 4 27 (by decide) ⟨-2, 1, -1, -2, 15, by decide⟩, -- source row 1611
  pairEntry 4 28 (by decide) ⟨-1, 8, 0, -5, 60, by decide⟩, -- source row 1612
  pairEntry 6 12 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨7, 4, -4, -3, 60, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨2, -1, -1, -2, 15, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨1, -8, 0, -5, 60, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-7, -4, 4, 3, 60, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1668
  pairEntry 6 21 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1674
  pairEntry 6 27 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1676
  pairEntry 6 28 (by decide) ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1677
  pairEntry 7 12 (by decide) ⟨7, 4, -4, -3, 60, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨2, -1, -1, -2, 15, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨1, -8, 0, -5, 60, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨-7, -4, 4, 3, 60, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-2, 1, 1, 2, 15, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1699
  pairEntry 7 21 (by decide) ⟨7, 4, -4, -3, 60, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨7, 4, -4, -3, 60, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1705
  pairEntry 7 27 (by decide) ⟨7, 4, -4, -3, 60, by decide⟩, -- source row 1707
  pairEntry 7 28 (by decide) ⟨-1, 8, 0, 5, 60, by decide⟩, -- source row 1708
  pairEntry 9 12 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨-4, 2, -2, 1, 30, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨4, -2, -2, 1, 30, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨4, -2, 0, 0, 15, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨4, -2, 2, -1, 30, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1758
  pairEntry 9 21 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1764
  pairEntry 9 27 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1766
  pairEntry 9 28 (by decide) ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1767
  pairEntry 10 12 (by decide) ⟨-4, 2, -2, 1, 30, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨4, -2, -2, 1, 30, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨4, -2, 0, 0, 15, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨4, -2, 2, -1, 30, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨-4, 2, 2, -1, 30, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1786
  pairEntry 10 21 (by decide) ⟨-4, 2, -2, 1, 30, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨-4, 2, -2, 1, 30, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1792
  pairEntry 10 27 (by decide) ⟨-4, 2, -2, 1, 30, by decide⟩, -- source row 1794
  pairEntry 10 28 (by decide) ⟨-4, 2, 0, 0, 15, by decide⟩, -- source row 1795
  pairEntry 12 22 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1842
  pairEntry 12 25 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1845
  pairEntry 12 28 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1848
  pairEntry 13 21 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1873
  pairEntry 15 21 (by decide) ⟨0, 0, -56, 33, 390, by decide⟩, -- source row 1913
  pairEntry 15 24 (by decide) ⟨99, 168, 56, -33, 780, by decide⟩, -- source row 1916
  pairEntry 15 27 (by decide) ⟨-99, -168, 56, -33, 780, by decide⟩, -- source row 1919
  pairEntry 16 22 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1936
  pairEntry 16 25 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1939
  pairEntry 16 28 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1942
  pairEntry 18 21 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 1983
  pairEntry 19 21 (by decide) ⟨99, 168, -56, 33, 780, by decide⟩, -- source row 1995
  pairEntry 19 24 (by decide) ⟨0, 0, 56, -33, 390, by decide⟩, -- source row 1998
  pairEntry 19 27 (by decide) ⟨-99, -168, -56, 33, 780, by decide⟩, -- source row 2001
  pairEntry 30 33 (by decide) ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨-1407, -2024, -2024, 1407, 29580, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨1407, 2024, 0, 0, 14790, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨1407, 2024, -2024, 1407, 29580, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨-1407, -2024, 2024, -1407, 14790, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨-4221, -6072, 2024, -1407, 29580, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨-1407, -2024, 2024, -1407, 29580, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨-1407, -2024, -2024, 1407, 29580, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨1407, 2024, 0, 0, 14790, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨1407, 2024, 2024, -1407, 29580, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨-1407, -2024, 0, 0, 14790, by decide⟩ -- source row 2178
]

end Option2.NativeStress.NativeT

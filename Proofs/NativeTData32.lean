module

public import NativeHWeights

@[expose] public section

/-! Exact source λ19; no cancellation or reproduction is asserted.
Source native_covectors.json SHA256 6b4aa865ec1adc3231845085a6911ff7130ec7057bf7c9a997b80639cfbde28b.
All integer fields, positive denominators and source ordering are unchanged. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH ConfigurationResidualIndices
private def traceEntry (p : Fin 39) (c : Literal) : Entry := ⟨fTrace p, c⟩

def lambda19 : List Entry := [
  idEntry 0 0 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 0
  idEntry 0 1 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 1
  idEntry 0 2 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 2
  idEntry 1 0 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 27
  idEntry 1 1 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 28
  idEntry 1 2 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 29
  idEntry 1 13 ⟨7, 24, -24, 7, 100, by decide⟩, -- source row 40
  idEntry 1 14 ⟨24, -7, 7, 24, 100, by decide⟩, -- source row 41
  idEntry 2 0 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 54
  idEntry 2 1 ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 55
  idEntry 2 2 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 56
  idEntry 3 0 ⟨-21, -72, -24, 7, 300, by decide⟩, -- source row 81
  idEntry 3 1 ⟨-21, -72, -24, 7, 300, by decide⟩, -- source row 82
  idEntry 3 2 ⟨21, 72, 24, -7, 100, by decide⟩, -- source row 83
  idEntry 3 3 ⟨-21, -72, -24, 7, 75, by decide⟩, -- source row 84
  idEntry 3 5 ⟨-7, -24, 24, -7, 100, by decide⟩, -- source row 86
  idEntry 3 6 ⟨-24, 7, -7, -24, 100, by decide⟩, -- source row 87
  idEntry 3 9 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 90
  idEntry 3 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 91
  idEntry 4 0 ⟨0, 0, -24, 7, 150, by decide⟩, -- source row 108
  idEntry 4 1 ⟨0, 0, -24, 7, 150, by decide⟩, -- source row 109
  idEntry 4 2 ⟨0, 0, 24, -7, 50, by decide⟩, -- source row 110
  idEntry 4 3 ⟨0, 0, 24, -7, 75, by decide⟩, -- source row 111
  idEntry 4 4 ⟨24, -7, 0, 0, 25, by decide⟩, -- source row 112
  idEntry 4 5 ⟨-7, -24, -24, 7, 100, by decide⟩, -- source row 113
  idEntry 4 6 ⟨-24, 7, 7, 24, 100, by decide⟩, -- source row 114
  idEntry 4 9 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 117
  idEntry 4 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 118
  idEntry 5 5 ⟨7, 24, 0, 0, 50, by decide⟩, -- source row 140
  idEntry 5 6 ⟨24, -7, 0, 0, 50, by decide⟩, -- source row 141
  idEntry 5 9 ⟨1, 0, 0, 0, 2, by decide⟩, -- source row 144
  idEntry 5 10 ⟨0, -1, 0, 0, 2, by decide⟩, -- source row 145
  idEntry 6 0 ⟨21, 72, -24, 7, 300, by decide⟩, -- source row 162
  idEntry 6 1 ⟨21, 72, -24, 7, 300, by decide⟩, -- source row 163
  idEntry 6 2 ⟨-21, -72, 24, -7, 100, by decide⟩, -- source row 164
  idEntry 6 3 ⟨21, 72, -24, 7, 75, by decide⟩, -- source row 165
  idEntry 6 5 ⟨-7, -24, -24, 7, 100, by decide⟩, -- source row 167
  idEntry 6 6 ⟨-24, 7, 7, 24, 100, by decide⟩, -- source row 168
  idEntry 6 9 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 171
  idEntry 6 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 172
  idEntry 7 0 ⟨21, 72, 24, -7, 300, by decide⟩, -- source row 189
  idEntry 7 1 ⟨21, 72, 24, -7, 300, by decide⟩, -- source row 190
  idEntry 7 2 ⟨-21, -72, -24, 7, 100, by decide⟩, -- source row 191
  idEntry 7 3 ⟨-21, -72, -24, 7, 150, by decide⟩, -- source row 192
  idEntry 7 4 ⟨-24, 7, -7, -24, 50, by decide⟩, -- source row 193
  idEntry 7 5 ⟨7, 24, 0, 0, 50, by decide⟩, -- source row 194
  idEntry 7 6 ⟨24, -7, 0, 0, 50, by decide⟩, -- source row 195
  idEntry 7 9 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 198
  idEntry 7 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 199
  idEntry 8 5 ⟨-7, -24, 24, -7, 100, by decide⟩, -- source row 221
  idEntry 8 6 ⟨-24, 7, -7, -24, 100, by decide⟩, -- source row 222
  idEntry 8 9 ⟨-1, 0, 0, -1, 4, by decide⟩, -- source row 225
  idEntry 8 10 ⟨0, 1, -1, 0, 4, by decide⟩, -- source row 226
  idEntry 9 0 ⟨0, 0, 24, -7, 150, by decide⟩, -- source row 243
  idEntry 9 1 ⟨0, 0, 24, -7, 150, by decide⟩, -- source row 244
  idEntry 9 2 ⟨0, 0, -24, 7, 50, by decide⟩, -- source row 245
  idEntry 9 3 ⟨0, 0, 48, -14, 75, by decide⟩, -- source row 246
  idEntry 9 5 ⟨7, 24, 0, 0, 50, by decide⟩, -- source row 248
  idEntry 9 6 ⟨24, -7, 0, 0, 50, by decide⟩, -- source row 249
  idEntry 9 9 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 252
  idEntry 9 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 253
  idEntry 10 0 ⟨-21, -72, 24, -7, 300, by decide⟩, -- source row 270
  idEntry 10 1 ⟨-21, -72, 24, -7, 300, by decide⟩, -- source row 271
  idEntry 10 2 ⟨21, 72, -24, 7, 100, by decide⟩, -- source row 272
  idEntry 10 3 ⟨21, 72, -24, 7, 150, by decide⟩, -- source row 273
  idEntry 10 4 ⟨-24, 7, 7, 24, 50, by decide⟩, -- source row 274
  idEntry 10 5 ⟨-7, -24, 24, -7, 100, by decide⟩, -- source row 275
  idEntry 10 6 ⟨-24, 7, -7, -24, 100, by decide⟩, -- source row 276
  idEntry 10 9 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 279
  idEntry 10 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 280
  idEntry 11 5 ⟨-7, -24, -24, 7, 100, by decide⟩, -- source row 302
  idEntry 11 6 ⟨-24, 7, 7, 24, 100, by decide⟩, -- source row 303
  idEntry 11 9 ⟨-1, 0, 0, 1, 4, by decide⟩, -- source row 306
  idEntry 11 10 ⟨0, 1, 1, 0, 4, by decide⟩, -- source row 307
  idEntry 12 0 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 324
  idEntry 12 1 ⟨9, -12, 4, 3, 60, by decide⟩, -- source row 325
  idEntry 12 2 ⟨-9, 12, -4, -3, 20, by decide⟩, -- source row 326
  idEntry 12 5 ⟨-9, 12, -4, -3, 15, by decide⟩, -- source row 329
  idEntry 12 7 ⟨-43, 24, -24, 7, 100, by decide⟩, -- source row 331
  idEntry 12 8 ⟨-24, 57, -7, -24, 100, by decide⟩, -- source row 332
  idEntry 13 0 ⟨9, -12, 4, 3, 30, by decide⟩, -- source row 351
  idEntry 13 1 ⟨9, -12, 4, 3, 30, by decide⟩, -- source row 352
  idEntry 13 2 ⟨-9, 12, -4, -3, 10, by decide⟩, -- source row 353
  idEntry 13 5 ⟨9, -12, 4, 3, 15, by decide⟩, -- source row 356
  idEntry 13 6 ⟨-4, -3, -3, 4, 5, by decide⟩, -- source row 357
  idEntry 13 7 ⟨11, -48, 0, 25, 100, by decide⟩, -- source row 358
  idEntry 13 8 ⟨48, -39, 25, 0, 100, by decide⟩, -- source row 359
  idEntry 14 7 ⟨8, 6, 6, -8, 25, by decide⟩, -- source row 385
  idEntry 14 8 ⟨-12, -9, -9, 12, 50, by decide⟩, -- source row 386
  idEntry 15 0 ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 405
  idEntry 15 1 ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 406
  idEntry 15 2 ⟨9, -12, -4, -3, 20, by decide⟩, -- source row 407
  idEntry 15 5 ⟨9, -12, -4, -3, 15, by decide⟩, -- source row 410
  idEntry 15 7 ⟨-43, 24, 24, -7, 100, by decide⟩, -- source row 412
  idEntry 15 8 ⟨-24, 57, 7, 24, 100, by decide⟩, -- source row 413
  idEntry 16 0 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 432
  idEntry 16 1 ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 433
  idEntry 16 2 ⟨-9, 12, 4, 3, 20, by decide⟩, -- source row 434
  idEntry 16 5 ⟨9, -12, -4, -3, 30, by decide⟩, -- source row 437
  idEntry 16 6 ⟨4, 3, -3, 4, 10, by decide⟩, -- source row 438
  idEntry 16 7 ⟨8, 6, -6, 8, 25, by decide⟩, -- source row 439
  idEntry 16 8 ⟨-12, -9, 9, -12, 50, by decide⟩, -- source row 440
  idEntry 17 7 ⟨11, -48, 0, -25, 100, by decide⟩, -- source row 466
  idEntry 17 8 ⟨48, -39, -25, 0, 100, by decide⟩, -- source row 467
  idEntry 18 0 ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 486
  idEntry 18 1 ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 487
  idEntry 18 2 ⟨0, 0, -4, -3, 5, by decide⟩, -- source row 488
  idEntry 18 5 ⟨0, 0, -16, -12, 15, by decide⟩, -- source row 491
  idEntry 18 7 ⟨-16, -12, 0, 0, 25, by decide⟩, -- source row 493
  idEntry 18 8 ⟨12, 9, 0, 0, 25, by decide⟩, -- source row 494
  idEntry 19 0 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 513
  idEntry 19 1 ⟨0, 0, 4, 3, 30, by decide⟩, -- source row 514
  idEntry 19 2 ⟨0, 0, -4, -3, 10, by decide⟩, -- source row 515
  idEntry 19 5 ⟨0, 0, 4, 3, 15, by decide⟩, -- source row 518
  idEntry 19 6 ⟨-4, -3, 0, 0, 5, by decide⟩, -- source row 519
  idEntry 19 7 ⟨16, 12, 12, 9, 50, by decide⟩, -- source row 520
  idEntry 19 8 ⟨-12, -9, 16, 12, 50, by decide⟩, -- source row 521
  idEntry 20 7 ⟨16, 12, -12, -9, 50, by decide⟩, -- source row 547
  idEntry 20 8 ⟨-12, -9, -16, -12, 50, by decide⟩, -- source row 548
  idEntry 21 0 ⟨0, 0, 6, 17, 65, by decide⟩, -- source row 567
  idEntry 21 1 ⟨0, 0, 6, 17, 65, by decide⟩, -- source row 568
  idEntry 21 2 ⟨0, 0, -18, -51, 65, by decide⟩, -- source row 569
  idEntry 21 3 ⟨-63, -16, 16, -63, 260, by decide⟩, -- source row 570
  idEntry 21 4 ⟨-16, 63, -63, -16, 260, by decide⟩, -- source row 571
  idEntry 21 5 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 572
  idEntry 21 6 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 573
  idEntry 21 7 ⟨0, 0, -72, -204, 325, by decide⟩, -- source row 574
  idEntry 21 8 ⟨0, 0, -96, -272, 325, by decide⟩, -- source row 575
  idEntry 22 0 ⟨51, -18, 6, 17, 130, by decide⟩, -- source row 594
  idEntry 22 1 ⟨51, -18, 6, 17, 130, by decide⟩, -- source row 595
  idEntry 22 2 ⟨-153, 54, -18, -51, 130, by decide⟩, -- source row 596
  idEntry 22 3 ⟨-63, -16, -16, 63, 260, by decide⟩, -- source row 597
  idEntry 22 4 ⟨-16, 63, 63, 16, 260, by decide⟩, -- source row 598
  idEntry 22 5 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 599
  idEntry 22 6 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 600
  idEntry 22 7 ⟨225, 150, 222, -21, 325, by decide⟩, -- source row 601
  idEntry 22 8 ⟨150, -225, -129, 122, 325, by decide⟩, -- source row 602
  idEntry 23 3 ⟨63, 16, 0, 0, 130, by decide⟩, -- source row 624
  idEntry 23 4 ⟨16, -63, 0, 0, 130, by decide⟩, -- source row 625
  idEntry 23 5 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 626
  idEntry 23 6 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 627
  idEntry 24 0 ⟨-63, -16, 40, 5, 260, by decide⟩, -- source row 648
  idEntry 24 1 ⟨-63, -16, 40, 5, 260, by decide⟩, -- source row 649
  idEntry 24 2 ⟨189, 48, -120, -15, 260, by decide⟩, -- source row 650
  idEntry 24 3 ⟨63, 16, 0, 0, 130, by decide⟩, -- source row 651
  idEntry 24 4 ⟨16, -63, 0, 0, 130, by decide⟩, -- source row 652
  idEntry 24 5 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 653
  idEntry 24 6 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 654
  idEntry 24 7 ⟨189, 48, -120, -15, 325, by decide⟩, -- source row 655
  idEntry 24 8 ⟨252, 64, -160, -20, 325, by decide⟩, -- source row 656
  idEntry 25 0 ⟨-12, -34, 6, 17, 130, by decide⟩, -- source row 675
  idEntry 25 1 ⟨-12, -34, 6, 17, 130, by decide⟩, -- source row 676
  idEntry 25 2 ⟨36, 102, -18, -51, 130, by decide⟩, -- source row 677
  idEntry 25 3 ⟨-63, -16, 16, -63, 260, by decide⟩, -- source row 678
  idEntry 25 4 ⟨-16, 63, -63, -16, 260, by decide⟩, -- source row 679
  idEntry 25 5 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 680
  idEntry 25 6 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 681
  idEntry 25 7 ⟨36, 102, -30, -85, 325, by decide⟩, -- source row 682
  idEntry 25 8 ⟨-102, -289, 60, 170, 325, by decide⟩, -- source row 683
  idEntry 26 3 ⟨-63, -16, -16, 63, 260, by decide⟩, -- source row 705
  idEntry 26 4 ⟨-16, 63, 63, 16, 260, by decide⟩, -- source row 706
  idEntry 26 5 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 707
  idEntry 26 6 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 708
  idEntry 27 0 ⟨63, 16, 40, 5, 260, by decide⟩, -- source row 729
  idEntry 27 1 ⟨63, 16, 40, 5, 260, by decide⟩, -- source row 730
  idEntry 27 2 ⟨-189, -48, -120, -15, 260, by decide⟩, -- source row 731
  idEntry 27 3 ⟨-63, -16, -16, 63, 260, by decide⟩, -- source row 732
  idEntry 27 4 ⟨-16, 63, 63, 16, 260, by decide⟩, -- source row 733
  idEntry 27 5 ⟨-3, 4, 0, 0, 10, by decide⟩, -- source row 734
  idEntry 27 6 ⟨4, 3, 0, 0, 10, by decide⟩, -- source row 735
  idEntry 27 7 ⟨-189, -48, -120, -15, 325, by decide⟩, -- source row 736
  idEntry 27 8 ⟨-252, -64, -160, -20, 325, by decide⟩, -- source row 737
  idEntry 28 0 ⟨39, -52, 28, -29, 260, by decide⟩, -- source row 756
  idEntry 28 1 ⟨39, -52, 28, -29, 260, by decide⟩, -- source row 757
  idEntry 28 2 ⟨-117, 156, -84, 87, 260, by decide⟩, -- source row 758
  idEntry 28 3 ⟨63, 16, 0, 0, 130, by decide⟩, -- source row 759
  idEntry 28 4 ⟨16, -63, 0, 0, 130, by decide⟩, -- source row 760
  idEntry 28 5 ⟨3, -4, 4, 3, 20, by decide⟩, -- source row 761
  idEntry 28 6 ⟨-4, -3, 3, -4, 20, by decide⟩, -- source row 762
  idEntry 28 7 ⟨453, -504, 240, -295, 650, by decide⟩, -- source row 763
  idEntry 28 8 ⟨-96, 53, -5, 40, 650, by decide⟩, -- source row 764
  idEntry 29 3 ⟨-63, -16, 16, -63, 260, by decide⟩, -- source row 786
  idEntry 29 4 ⟨-16, 63, -63, -16, 260, by decide⟩, -- source row 787
  idEntry 29 5 ⟨3, -4, -4, -3, 20, by decide⟩, -- source row 788
  idEntry 29 6 ⟨-4, -3, -3, 4, 20, by decide⟩, -- source row 789
  idEntry 30 0 ⟨1881, 1092, -364, 627, 8700, by decide⟩, -- source row 810
  idEntry 30 1 ⟨0, 0, 364, -627, 4350, by decide⟩, -- source row 811
  idEntry 30 2 ⟨-627, -364, 0, 0, 4350, by decide⟩, -- source row 812
  idEntry 30 9 ⟨-18587, -4084, -3196, -6047, 49300, by decide⟩, -- source row 819
  idEntry 30 10 ⟨8700, 42775, -31127, -11364, 147900, by decide⟩, -- source row 820
  idEntry 31 0 ⟨1881, 1092, 364, -627, 8700, by decide⟩, -- source row 837
  idEntry 31 1 ⟨0, 0, -364, 627, 4350, by decide⟩, -- source row 838
  idEntry 31 2 ⟨-627, -364, 364, -627, 4350, by decide⟩, -- source row 839
  idEntry 31 9 ⟨57099, 53268, 10476, -6493, 147900, by decide⟩, -- source row 846
  idEntry 31 10 ⟨-51492, 7831, 6493, 10476, 147900, by decide⟩, -- source row 847
  idEntry 32 0 ⟨-1254, -728, -364, 627, 4350, by decide⟩, -- source row 864
  idEntry 32 1 ⟨627, 364, -364, 627, 4350, by decide⟩, -- source row 865
  idEntry 32 2 ⟨-627, -364, 728, -1254, 4350, by decide⟩, -- source row 866
  idEntry 32 9 ⟨16803, -50604, -11364, 31127, 147900, by decide⟩, -- source row 873
  idEntry 32 10 ⟨54156, -81733, 18141, -9588, 147900, by decide⟩, -- source row 874
  idEntry 33 0 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 891
  idEntry 33 1 ⟨-1254, -728, -364, 627, 4350, by decide⟩, -- source row 892
  idEntry 33 2 ⟨1254, 728, 364, -627, 4350, by decide⟩, -- source row 893
  idEntry 33 9 ⟨12763, 14116, 6836, -223, 49300, by decide⟩, -- source row 900
  idEntry 33 10 ⟨-41460, 13655, 25303, 21396, 147900, by decide⟩, -- source row 901
  idEntry 34 0 ⟨-1881, -1092, 364, -627, 8700, by decide⟩, -- source row 918
  idEntry 34 1 ⟨1881, 1092, 364, -627, 8700, by decide⟩, -- source row 919
  idEntry 34 2 ⟨-627, -364, -364, 627, 4350, by decide⟩, -- source row 920
  idEntry 34 9 ⟨-38289, -42348, 21396, -25303, 147900, by decide⟩, -- source row 927
  idEntry 34 10 ⟨41460, -13655, 669, 20508, 147900, by decide⟩, -- source row 928
  idEntry 35 0 ⟨1254, 728, -364, 627, 4350, by decide⟩, -- source row 945
  idEntry 35 1 ⟨627, 364, 364, -627, 8700, by decide⟩, -- source row 946
  idEntry 35 2 ⟨-627, -364, 0, 0, 4350, by decide⟩, -- source row 947
  idEntry 35 9 ⟨12317, 444, -6836, 223, 49300, by decide⟩, -- source row 954
  idEntry 35 10 ⟨1332, -36951, -25303, -21396, 147900, by decide⟩, -- source row 955
  idEntry 36 0 ⟨0, 0, -364, 627, 4350, by decide⟩, -- source row 972
  idEntry 36 1 ⟨1881, 1092, -364, 627, 4350, by decide⟩, -- source row 973
  idEntry 36 2 ⟨-1881, -1092, 364, -627, 4350, by decide⟩, -- source row 974
  idEntry 36 9 ⟨-6493, -10476, 3640, -6270, 24650, by decide⟩, -- source row 981
  idEntry 36 10 ⟨31428, -19479, -5824, 10032, 73950, by decide⟩, -- source row 982
  idEntry 37 0 ⟨-627, -364, -364, 627, 8700, by decide⟩, -- source row 999
  idEntry 37 1 ⟨-1254, -728, 364, -627, 4350, by decide⟩, -- source row 1000
  idEntry 37 2 ⟨1881, 1092, -364, 627, 4350, by decide⟩, -- source row 1001
  idEntry 37 9 ⟨-669, -20508, -20952, 12986, 73950, by decide⟩, -- source row 1008
  idEntry 37 10 ⟨21396, -25303, -12986, -20952, 73950, by decide⟩, -- source row 1009
  idEntry 38 0 ⟨627, 364, 1092, -1881, 8700, by decide⟩, -- source row 1026
  idEntry 38 1 ⟨-627, -364, 0, 0, 4350, by decide⟩, -- source row 1027
  idEntry 38 9 ⟨223, 6836, 0, 0, 24650, by decide⟩, -- source row 1035
  idEntry 38 10 ⟨-21396, 25303, 0, 0, 73950, by decide⟩, -- source row 1036
  sumEntry 0 9 ⟨-669, -20508, 444, -12317, 147900, by decide⟩, -- source row 1101
  sumEntry 0 10 ⟨21396, -25303, -12317, -444, 147900, by decide⟩, -- source row 1102
  sumEntry 0 13 ⟨2184, -3762, -1254, -728, 37845, by decide⟩, -- source row 1105
  sumEntry 0 14 ⟨-7644, 13167, 4389, 2548, 126150, by decide⟩, -- source row 1106
  sumEntry 0 23 ⟨-267537, 237016, 154232, -40401, 4289100, by decide⟩, -- source row 1115
  sumEntry 0 24 ⟨711048, 802611, -413871, 936728, 12867300, by decide⟩, -- source row 1116
  sumEntry 1 5 ⟨7, 24, 0, 0, 150, by decide⟩, -- source row 1124
  sumEntry 1 6 ⟨24, -7, 0, 0, 150, by decide⟩, -- source row 1125
  sumEntry 1 9 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1128
  sumEntry 1 10 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1129
  sumEntry 1 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1132
  sumEntry 1 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1133
  sumEntry 1 17 ⟨1, 0, 0, -1, 12, by decide⟩, -- source row 1136
  sumEntry 1 18 ⟨0, -1, -1, 0, 12, by decide⟩, -- source row 1137
  sumEntry 1 21 ⟨-7, -24, -24, 7, 300, by decide⟩, -- source row 1140
  sumEntry 1 22 ⟨-24, 7, 7, 24, 300, by decide⟩, -- source row 1141
  sumEntry 1 25 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1144
  sumEntry 1 26 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1145
  sumEntry 2 5 ⟨-7, -24, 24, -7, 300, by decide⟩, -- source row 1151
  sumEntry 2 6 ⟨-24, 7, -7, -24, 300, by decide⟩, -- source row 1152
  sumEntry 2 9 ⟨-1, 0, 0, -1, 12, by decide⟩, -- source row 1155
  sumEntry 2 10 ⟨0, 1, -1, 0, 12, by decide⟩, -- source row 1156
  sumEntry 2 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1159
  sumEntry 2 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1160
  sumEntry 2 17 ⟨1, 0, 0, 1, 12, by decide⟩, -- source row 1163
  sumEntry 2 18 ⟨0, -1, 1, 0, 12, by decide⟩, -- source row 1164
  sumEntry 2 21 ⟨-7, -24, -24, 7, 300, by decide⟩, -- source row 1167
  sumEntry 2 22 ⟨-24, 7, 7, 24, 300, by decide⟩, -- source row 1168
  sumEntry 2 25 ⟨1, 0, 0, 0, 6, by decide⟩, -- source row 1171
  sumEntry 2 26 ⟨0, -1, 0, 0, 6, by decide⟩, -- source row 1172
  sumEntry 3 5 ⟨-7, -24, -24, 7, 300, by decide⟩, -- source row 1178
  sumEntry 3 6 ⟨-24, 7, 7, 24, 300, by decide⟩, -- source row 1179
  sumEntry 3 9 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1182
  sumEntry 3 10 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1183
  sumEntry 3 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1186
  sumEntry 3 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1187
  sumEntry 3 17 ⟨-1, 0, 0, 0, 6, by decide⟩, -- source row 1190
  sumEntry 3 18 ⟨0, 1, 0, 0, 6, by decide⟩, -- source row 1191
  sumEntry 3 21 ⟨-7, -24, -24, 7, 300, by decide⟩, -- source row 1194
  sumEntry 3 22 ⟨-24, 7, 7, 24, 300, by decide⟩, -- source row 1195
  sumEntry 3 25 ⟨-1, 0, 0, 1, 12, by decide⟩, -- source row 1198
  sumEntry 3 26 ⟨0, 1, 1, 0, 12, by decide⟩, -- source row 1199
  sumEntry 4 7 ⟨8, 6, 6, -8, 75, by decide⟩, -- source row 1207
  sumEntry 4 8 ⟨-4, -3, -3, 4, 50, by decide⟩, -- source row 1208
  sumEntry 4 13 ⟨-43, 24, -24, 7, 300, by decide⟩, -- source row 1213
  sumEntry 4 14 ⟨24, -57, 7, 24, 300, by decide⟩, -- source row 1214
  sumEntry 4 19 ⟨11, -48, 0, 25, 300, by decide⟩, -- source row 1219
  sumEntry 4 20 ⟨48, -39, 25, 0, 300, by decide⟩, -- source row 1220
  sumEntry 5 7 ⟨11, -48, 0, -25, 300, by decide⟩, -- source row 1234
  sumEntry 5 8 ⟨48, -39, -25, 0, 300, by decide⟩, -- source row 1235
  sumEntry 5 13 ⟨8, 6, -6, 8, 75, by decide⟩, -- source row 1240
  sumEntry 5 14 ⟨4, 3, -3, 4, 50, by decide⟩, -- source row 1241
  sumEntry 5 19 ⟨11, -48, 0, -25, 300, by decide⟩, -- source row 1246
  sumEntry 5 20 ⟨48, -39, -25, 0, 300, by decide⟩, -- source row 1247
  sumEntry 6 7 ⟨16, 12, -12, -9, 150, by decide⟩, -- source row 1261
  sumEntry 6 8 ⟨-12, -9, -16, -12, 150, by decide⟩, -- source row 1262
  sumEntry 6 13 ⟨16, 12, -12, -9, 150, by decide⟩, -- source row 1267
  sumEntry 6 14 ⟨12, 9, 16, 12, 150, by decide⟩, -- source row 1268
  sumEntry 6 19 ⟨-16, -12, 0, 0, 75, by decide⟩, -- source row 1273
  sumEntry 6 20 ⟨4, 3, 0, 0, 25, by decide⟩, -- source row 1274
  sumEntry 7 3 ⟨63, 16, 0, 0, 390, by decide⟩, -- source row 1284
  sumEntry 7 4 ⟨16, -63, 0, 0, 390, by decide⟩, -- source row 1285
  sumEntry 7 5 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1286
  sumEntry 7 6 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1287
  sumEntry 7 11 ⟨-5, -12, 12, -5, 156, by decide⟩, -- source row 1292
  sumEntry 7 12 ⟨-12, 5, -5, -12, 156, by decide⟩, -- source row 1293
  sumEntry 7 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1294
  sumEntry 7 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1295
  sumEntry 7 23 ⟨-63, -16, 0, 0, 390, by decide⟩, -- source row 1304
  sumEntry 7 24 ⟨16, -63, 0, 0, 390, by decide⟩, -- source row 1305
  sumEntry 7 25 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1306
  sumEntry 7 26 ⟨4, 3, 3, -4, 60, by decide⟩, -- source row 1307
  sumEntry 8 3 ⟨-63, -16, -16, 63, 780, by decide⟩, -- source row 1311
  sumEntry 8 4 ⟨-16, 63, 63, 16, 780, by decide⟩, -- source row 1312
  sumEntry 8 5 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1313
  sumEntry 8 6 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1314
  sumEntry 8 11 ⟨5, 12, 0, 0, 78, by decide⟩, -- source row 1319
  sumEntry 8 12 ⟨12, -5, 0, 0, 78, by decide⟩, -- source row 1320
  sumEntry 8 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1321
  sumEntry 8 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1322
  sumEntry 8 23 ⟨63, 16, 16, -63, 780, by decide⟩, -- source row 1331
  sumEntry 8 24 ⟨-16, 63, 63, 16, 780, by decide⟩, -- source row 1332
  sumEntry 8 25 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1333
  sumEntry 8 26 ⟨4, 3, 3, -4, 60, by decide⟩, -- source row 1334
  sumEntry 9 3 ⟨-63, -16, 16, -63, 780, by decide⟩, -- source row 1338
  sumEntry 9 4 ⟨-16, 63, -63, -16, 780, by decide⟩, -- source row 1339
  sumEntry 9 5 ⟨3, -4, -4, -3, 60, by decide⟩, -- source row 1340
  sumEntry 9 6 ⟨-4, -3, -3, 4, 60, by decide⟩, -- source row 1341
  sumEntry 9 11 ⟨-5, -12, -12, 5, 156, by decide⟩, -- source row 1346
  sumEntry 9 12 ⟨-12, 5, 5, 12, 156, by decide⟩, -- source row 1347
  sumEntry 9 13 ⟨7, 24, -24, 7, 300, by decide⟩, -- source row 1348
  sumEntry 9 14 ⟨24, -7, 7, 24, 300, by decide⟩, -- source row 1349
  sumEntry 9 23 ⟨63, 16, -16, 63, 780, by decide⟩, -- source row 1358
  sumEntry 9 24 ⟨-16, 63, -63, -16, 780, by decide⟩, -- source row 1359
  sumEntry 9 25 ⟨-3, 4, 4, 3, 60, by decide⟩, -- source row 1360
  sumEntry 9 26 ⟨4, 3, 3, -4, 60, by decide⟩, -- source row 1361
  sumEntry 10 1 ⟨627, 364, 364, -627, 8700, by decide⟩, -- source row 1363
  sumEntry 10 2 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 1364
  sumEntry 10 9 ⟨19479, 31428, 11364, -31127, 443700, by decide⟩, -- source row 1371
  sumEntry 10 10 ⟨-10476, 6493, -6047, 3196, 147900, by decide⟩, -- source row 1372
  sumEntry 10 13 ⟨17661, 60552, -50160, -29120, 378450, by decide⟩, -- source row 1375
  sumEntry 10 14 ⟨20184, -5887, 17556, 10192, 126150, by decide⟩, -- source row 1376
  sumEntry 11 1 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 1390
  sumEntry 11 9 ⟨-28215, -16380, 5016, 2912, 221850, by decide⟩, -- source row 1398
  sumEntry 11 10 ⟨5016, 2912, 3135, 1820, 73950, by decide⟩, -- source row 1399
  sumEntry 11 13 ⟨79002, 45864, -35472, 32221, 378450, by decide⟩, -- source row 1402
  sumEntry 11 14 ⟨25080, 14560, -2891, 15088, 126150, by decide⟩, -- source row 1403
  sumEntry 12 0 ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 1416
  sumEntry 12 1 ⟨-627, -364, -364, 627, 8700, by decide⟩, -- source row 1417
  sumEntry 12 9 ⟨627, 364, -364, 627, 4930, by decide⟩, -- source row 1425
  sumEntry 12 10 ⟨-2508, -1456, 1456, -2508, 36975, by decide⟩, -- source row 1426
  sumEntry 12 13 ⟨-7280, 12540, -2548, 4389, 42050, by decide⟩, -- source row 1429
  sumEntry 12 14 ⟨22932, -39501, -7280, 12540, 126150, by decide⟩, -- source row 1430
  pairEntry 0 30 (by decide) ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 1472
  pairEntry 0 31 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 1473
  pairEntry 0 32 (by decide) ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 1474
  pairEntry 0 36 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 1478
  pairEntry 0 37 (by decide) ⟨627, 364, -364, 627, 4350, by decide⟩, -- source row 1479
  pairEntry 0 38 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 1480
  pairEntry 1 30 (by decide) ⟨-1881, -1092, 364, -627, 8700, by decide⟩, -- source row 1509
  pairEntry 1 31 (by decide) ⟨-627, -364, -1092, 1881, 8700, by decide⟩, -- source row 1510
  pairEntry 1 33 (by decide) ⟨0, 0, -364, 627, 4350, by decide⟩, -- source row 1512
  pairEntry 1 34 (by decide) ⟨1881, 1092, -364, 627, 8700, by decide⟩, -- source row 1513
  pairEntry 1 36 (by decide) ⟨1881, 1092, 364, -627, 8700, by decide⟩, -- source row 1515
  pairEntry 1 37 (by decide) ⟨627, 364, 364, -627, 8700, by decide⟩, -- source row 1516
  pairEntry 2 31 (by decide) ⟨627, 364, -364, 627, 4350, by decide⟩, -- source row 1546
  pairEntry 2 37 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 1552
  pairEntry 3 12 (by decide) ⟨-11, 48, 0, -25, 300, by decide⟩, -- source row 1562
  pairEntry 3 13 (by decide) ⟨8, 6, 6, -8, 75, by decide⟩, -- source row 1563
  pairEntry 3 15 (by decide) ⟨-11, 48, 0, 25, 300, by decide⟩, -- source row 1565
  pairEntry 3 16 (by decide) ⟨-43, 24, 24, -7, 300, by decide⟩, -- source row 1566
  pairEntry 3 18 (by decide) ⟨16, 12, 0, 0, 75, by decide⟩, -- source row 1568
  pairEntry 3 19 (by decide) ⟨16, 12, 12, 9, 150, by decide⟩, -- source row 1569
  pairEntry 3 21 (by decide) ⟨-13, 104, 16, -63, 780, by decide⟩, -- source row 1571
  pairEntry 3 22 (by decide) ⟨-101, 28, -60, 25, 780, by decide⟩, -- source row 1572
  pairEntry 3 24 (by decide) ⟨101, -28, -60, 25, 780, by decide⟩, -- source row 1574
  pairEntry 3 25 (by decide) ⟨13, -104, 16, -63, 780, by decide⟩, -- source row 1575
  pairEntry 3 27 (by decide) ⟨-44, -38, 22, 19, 390, by decide⟩, -- source row 1577
  pairEntry 3 28 (by decide) ⟨44, 38, 22, 19, 390, by decide⟩, -- source row 1578
  pairEntry 4 12 (by decide) ⟨8, 6, 6, -8, 75, by decide⟩, -- source row 1596
  pairEntry 4 13 (by decide) ⟨43, -24, 24, -7, 300, by decide⟩, -- source row 1597
  pairEntry 4 15 (by decide) ⟨-43, 24, 24, -7, 300, by decide⟩, -- source row 1599
  pairEntry 4 16 (by decide) ⟨-8, -6, 6, -8, 75, by decide⟩, -- source row 1600
  pairEntry 4 18 (by decide) ⟨16, 12, 12, 9, 150, by decide⟩, -- source row 1602
  pairEntry 4 19 (by decide) ⟨-16, -12, 12, 9, 150, by decide⟩, -- source row 1603
  pairEntry 4 21 (by decide) ⟨22, 19, 19, -22, 195, by decide⟩, -- source row 1605
  pairEntry 4 22 (by decide) ⟨-13, 104, 16, -63, 780, by decide⟩, -- source row 1606
  pairEntry 4 24 (by decide) ⟨22, 19, -19, 22, 195, by decide⟩, -- source row 1608
  pairEntry 4 25 (by decide) ⟨101, -28, -60, 25, 780, by decide⟩, -- source row 1609
  pairEntry 4 27 (by decide) ⟨-44, -38, 0, 0, 195, by decide⟩, -- source row 1611
  pairEntry 4 28 (by decide) ⟨-44, -38, 22, 19, 390, by decide⟩, -- source row 1612
  pairEntry 6 12 (by decide) ⟨43, -24, 24, -7, 300, by decide⟩, -- source row 1661
  pairEntry 6 13 (by decide) ⟨11, -48, 0, 25, 300, by decide⟩, -- source row 1662
  pairEntry 6 15 (by decide) ⟨-8, -6, 6, -8, 75, by decide⟩, -- source row 1664
  pairEntry 6 16 (by decide) ⟨11, -48, 0, -25, 300, by decide⟩, -- source row 1665
  pairEntry 6 18 (by decide) ⟨-16, -12, 12, 9, 150, by decide⟩, -- source row 1667
  pairEntry 6 19 (by decide) ⟨-16, -12, 0, 0, 75, by decide⟩, -- source row 1668
  pairEntry 6 21 (by decide) ⟨-44, -38, -22, -19, 390, by decide⟩, -- source row 1670
  pairEntry 6 22 (by decide) ⟨-44, -38, 0, 0, 195, by decide⟩, -- source row 1671
  pairEntry 6 24 (by decide) ⟨101, -28, 60, -25, 780, by decide⟩, -- source row 1673
  pairEntry 6 25 (by decide) ⟨22, 19, 19, -22, 195, by decide⟩, -- source row 1674
  pairEntry 6 27 (by decide) ⟨-13, 104, -16, 63, 780, by decide⟩, -- source row 1676
  pairEntry 6 28 (by decide) ⟨22, 19, -19, 22, 195, by decide⟩, -- source row 1677
  pairEntry 7 12 (by decide) ⟨11, -48, 0, 25, 300, by decide⟩, -- source row 1692
  pairEntry 7 13 (by decide) ⟨-8, -6, -6, 8, 75, by decide⟩, -- source row 1693
  pairEntry 7 15 (by decide) ⟨11, -48, 0, -25, 300, by decide⟩, -- source row 1695
  pairEntry 7 16 (by decide) ⟨43, -24, -24, 7, 300, by decide⟩, -- source row 1696
  pairEntry 7 18 (by decide) ⟨-16, -12, 0, 0, 75, by decide⟩, -- source row 1698
  pairEntry 7 19 (by decide) ⟨-16, -12, -12, -9, 150, by decide⟩, -- source row 1699
  pairEntry 7 21 (by decide) ⟨44, 38, -22, -19, 390, by decide⟩, -- source row 1701
  pairEntry 7 22 (by decide) ⟨-44, -38, -22, -19, 390, by decide⟩, -- source row 1702
  pairEntry 7 24 (by decide) ⟨13, -104, -16, 63, 780, by decide⟩, -- source row 1704
  pairEntry 7 25 (by decide) ⟨101, -28, 60, -25, 780, by decide⟩, -- source row 1705
  pairEntry 7 27 (by decide) ⟨-101, 28, 60, -25, 780, by decide⟩, -- source row 1707
  pairEntry 7 28 (by decide) ⟨-13, 104, -16, 63, 780, by decide⟩, -- source row 1708
  pairEntry 9 12 (by decide) ⟨-8, -6, -6, 8, 75, by decide⟩, -- source row 1751
  pairEntry 9 13 (by decide) ⟨-43, 24, -24, 7, 300, by decide⟩, -- source row 1752
  pairEntry 9 15 (by decide) ⟨43, -24, -24, 7, 300, by decide⟩, -- source row 1754
  pairEntry 9 16 (by decide) ⟨8, 6, -6, 8, 75, by decide⟩, -- source row 1755
  pairEntry 9 18 (by decide) ⟨-16, -12, -12, -9, 150, by decide⟩, -- source row 1757
  pairEntry 9 19 (by decide) ⟨16, 12, -12, -9, 150, by decide⟩, -- source row 1758
  pairEntry 9 21 (by decide) ⟨-22, -19, 19, -22, 195, by decide⟩, -- source row 1760
  pairEntry 9 22 (by decide) ⟨-101, 28, 60, -25, 780, by decide⟩, -- source row 1761
  pairEntry 9 24 (by decide) ⟨44, 38, 0, 0, 195, by decide⟩, -- source row 1763
  pairEntry 9 25 (by decide) ⟨44, 38, -22, -19, 390, by decide⟩, -- source row 1764
  pairEntry 9 27 (by decide) ⟨-22, -19, -19, 22, 195, by decide⟩, -- source row 1766
  pairEntry 9 28 (by decide) ⟨13, -104, -16, 63, 780, by decide⟩, -- source row 1767
  pairEntry 10 12 (by decide) ⟨-43, 24, -24, 7, 300, by decide⟩, -- source row 1779
  pairEntry 10 13 (by decide) ⟨-11, 48, 0, -25, 300, by decide⟩, -- source row 1780
  pairEntry 10 15 (by decide) ⟨8, 6, -6, 8, 75, by decide⟩, -- source row 1782
  pairEntry 10 16 (by decide) ⟨-11, 48, 0, 25, 300, by decide⟩, -- source row 1783
  pairEntry 10 18 (by decide) ⟨16, 12, -12, -9, 150, by decide⟩, -- source row 1785
  pairEntry 10 19 (by decide) ⟨16, 12, 0, 0, 75, by decide⟩, -- source row 1786
  pairEntry 10 21 (by decide) ⟨13, -104, 16, -63, 780, by decide⟩, -- source row 1788
  pairEntry 10 22 (by decide) ⟨-22, -19, 19, -22, 195, by decide⟩, -- source row 1789
  pairEntry 10 24 (by decide) ⟨44, 38, 22, 19, 390, by decide⟩, -- source row 1791
  pairEntry 10 25 (by decide) ⟨44, 38, 0, 0, 195, by decide⟩, -- source row 1792
  pairEntry 10 27 (by decide) ⟨-101, 28, -60, 25, 780, by decide⟩, -- source row 1794
  pairEntry 10 28 (by decide) ⟨-22, -19, -19, 22, 195, by decide⟩, -- source row 1795
  pairEntry 12 22 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1842
  pairEntry 12 25 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1845
  pairEntry 12 28 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1848
  pairEntry 13 21 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1866
  pairEntry 13 22 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1867
  pairEntry 13 24 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1869
  pairEntry 13 25 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1870
  pairEntry 13 27 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1872
  pairEntry 13 28 (by decide) ⟨-9, 12, -4, -3, 60, by decide⟩, -- source row 1873
  pairEntry 15 21 (by decide) ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 1913
  pairEntry 15 24 (by decide) ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 1916
  pairEntry 15 27 (by decide) ⟨9, -12, -4, -3, 60, by decide⟩, -- source row 1919
  pairEntry 16 22 (by decide) ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 1936
  pairEntry 16 25 (by decide) ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 1939
  pairEntry 16 28 (by decide) ⟨-9, 12, 4, 3, 60, by decide⟩, -- source row 1942
  pairEntry 18 21 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1976
  pairEntry 18 22 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1977
  pairEntry 18 24 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1979
  pairEntry 18 25 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1980
  pairEntry 18 27 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1982
  pairEntry 18 28 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1983
  pairEntry 19 21 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1995
  pairEntry 19 24 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 1998
  pairEntry 19 27 (by decide) ⟨0, 0, -4, -3, 30, by decide⟩, -- source row 2001
  pairEntry 30 33 (by decide) ⟨627, 364, 0, 0, 4350, by decide⟩, -- source row 2150
  pairEntry 30 34 (by decide) ⟨-627, -364, -364, 627, 8700, by decide⟩, -- source row 2151
  pairEntry 30 36 (by decide) ⟨-627, -364, -364, 627, 8700, by decide⟩, -- source row 2153
  pairEntry 30 38 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 2155
  pairEntry 31 34 (by decide) ⟨-627, -364, 0, 0, 4350, by decide⟩, -- source row 2158
  pairEntry 31 36 (by decide) ⟨-627, -364, 364, -627, 4350, by decide⟩, -- source row 2160
  pairEntry 31 37 (by decide) ⟨0, 0, 364, -627, 4350, by decide⟩, -- source row 2161
  pairEntry 31 38 (by decide) ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 2162
  pairEntry 32 33 (by decide) ⟨627, 364, 364, -627, 8700, by decide⟩, -- source row 2163
  pairEntry 33 36 (by decide) ⟨-627, -364, 364, -627, 8700, by decide⟩, -- source row 2171
  pairEntry 33 37 (by decide) ⟨627, 364, 0, 0, 4350, by decide⟩, -- source row 2172
  pairEntry 34 37 (by decide) ⟨627, 364, -364, 627, 8700, by decide⟩, -- source row 2176
  pairEntry 35 36 (by decide) ⟨-627, -364, 0, 0, 4350, by decide⟩ -- source row 2178
]

end Option2.NativeStress.NativeT

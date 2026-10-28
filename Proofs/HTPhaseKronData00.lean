module

public import NativeHEquilibriumCore

@[expose] public section

/-! Pure T covector for Book T component 00 with its Laurent phase tags (first-party data).
Source: agents/PHASE/py/T_pure_covectors.json sha256 c1a14a205203f9443f103b1f5152be4bd9566085e93483ac96637b689f0658e0.
Entry = original typed row label + literal coefficient (A+Bi+C√3+Di√3)/N; tag = exponent of u = ξ/ξ_base.
No property is asserted here. -/

set_option autoImplicit false
set_option maxRecDepth 8192
namespace Option2.NativeStress.HTPhaseKron
open NativeH ConfigurationResidualIndices

/-- Exponent vectors of the four literal phase variables. -/
abbrev Ex := Int × Int × Int × Int

/-- A covector entry carrying its Laurent phase monomial. -/
structure PEntry where
  e : Entry
  x : Ex

def covT00 : List PEntry := [
  ⟨idEntry 12 11 ⟨1, 0, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 335
  ⟨idEntry 12 12 ⟨0, -1, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 336
  ⟨idEntry 13 11 ⟨1, 0, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 362
  ⟨idEntry 13 12 ⟨0, -1, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 363
  ⟨idEntry 14 11 ⟨1, 0, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 389
  ⟨idEntry 14 12 ⟨0, -1, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩, -- row 390
  ⟨idEntry 15 11 ⟨-1, 0, 0, 1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 416
  ⟨idEntry 15 12 ⟨0, 1, 1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 417
  ⟨idEntry 16 11 ⟨-1, 0, 0, 1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 443
  ⟨idEntry 16 12 ⟨0, 1, 1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 444
  ⟨idEntry 17 11 ⟨-1, 0, 0, 1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 470
  ⟨idEntry 17 12 ⟨0, 1, 1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 471
  ⟨idEntry 18 11 ⟨-1, 0, 0, -1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 497
  ⟨idEntry 18 12 ⟨0, 1, -1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 498
  ⟨idEntry 19 11 ⟨-1, 0, 0, -1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 524
  ⟨idEntry 19 12 ⟨0, 1, -1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 525
  ⟨idEntry 20 11 ⟨-1, 0, 0, -1, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 551
  ⟨idEntry 20 12 ⟨0, 1, -1, 0, 4, by decide⟩, (0, 0, 0, 0)⟩, -- row 552
  ⟨idEntry 21 3 ⟨837, -116, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 570
  ⟨idEntry 21 4 ⟨116, 837, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 571
  ⟨idEntry 22 3 ⟨837, -116, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 597
  ⟨idEntry 22 4 ⟨116, 837, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 598
  ⟨idEntry 23 3 ⟨837, -116, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 624
  ⟨idEntry 23 4 ⟨116, 837, 0, 0, 1690, by decide⟩, (-1, -2, 0, 0)⟩, -- row 625
  ⟨idEntry 24 3 ⟨-837, 116, 116, 837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 651
  ⟨idEntry 24 4 ⟨-116, -837, -837, 116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 652
  ⟨idEntry 25 3 ⟨-837, 116, 116, 837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 678
  ⟨idEntry 25 4 ⟨-116, -837, -837, 116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 679
  ⟨idEntry 26 3 ⟨-837, 116, 116, 837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 705
  ⟨idEntry 26 4 ⟨-116, -837, -837, 116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 706
  ⟨idEntry 27 3 ⟨-837, 116, -116, -837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 732
  ⟨idEntry 27 4 ⟨-116, -837, 837, -116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 733
  ⟨idEntry 28 3 ⟨-837, 116, -116, -837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 759
  ⟨idEntry 28 4 ⟨-116, -837, 837, -116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 760
  ⟨idEntry 29 3 ⟨-837, 116, -116, -837, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 786
  ⟨idEntry 29 4 ⟨-116, -837, 837, -116, 3380, by decide⟩, (-1, -2, 0, 0)⟩, -- row 787
  ⟨idEntry 30 19 ⟨-475, -132, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 829
  ⟨idEntry 30 20 ⟨132, -475, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 830
  ⟨idEntry 31 19 ⟨-475, -132, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 856
  ⟨idEntry 31 20 ⟨132, -475, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 857
  ⟨idEntry 32 19 ⟨-475, -132, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 883
  ⟨idEntry 32 20 ⟨132, -475, 0, 0, 986, by decide⟩, (0, 0, -1, 1)⟩, -- row 884
  ⟨idEntry 33 19 ⟨475, 132, 132, -475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 910
  ⟨idEntry 33 20 ⟨-132, 475, 475, 132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 911
  ⟨idEntry 34 19 ⟨475, 132, 132, -475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 937
  ⟨idEntry 34 20 ⟨-132, 475, 475, 132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 938
  ⟨idEntry 35 19 ⟨475, 132, 132, -475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 964
  ⟨idEntry 35 20 ⟨-132, 475, 475, 132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 965
  ⟨idEntry 36 19 ⟨475, 132, -132, 475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 991
  ⟨idEntry 36 20 ⟨-132, 475, -475, -132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 992
  ⟨idEntry 37 19 ⟨475, 132, -132, 475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 1018
  ⟨idEntry 37 20 ⟨-132, 475, -475, -132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 1019
  ⟨idEntry 38 19 ⟨475, 132, -132, 475, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 1045
  ⟨idEntry 38 20 ⟨-132, 475, -475, -132, 1972, by decide⟩, (0, 0, -1, 1)⟩, -- row 1046
  ⟨sumEntry 4 11 ⟨1, 0, 0, 0, 6, by decide⟩, (0, 0, 0, 0)⟩, -- row 1211
  ⟨sumEntry 4 12 ⟨0, -1, 0, 0, 6, by decide⟩, (0, 0, 0, 0)⟩, -- row 1212
  ⟨sumEntry 5 11 ⟨-1, 0, 0, 1, 12, by decide⟩, (0, 0, 0, 0)⟩, -- row 1238
  ⟨sumEntry 5 12 ⟨0, 1, 1, 0, 12, by decide⟩, (0, 0, 0, 0)⟩, -- row 1239
  ⟨sumEntry 6 11 ⟨-1, 0, 0, -1, 12, by decide⟩, (0, 0, 0, 0)⟩, -- row 1265
  ⟨sumEntry 6 12 ⟨0, 1, -1, 0, 12, by decide⟩, (0, 0, 0, 0)⟩, -- row 1266
  ⟨sumEntry 7 3 ⟨837, -116, 0, 0, 5070, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1284
  ⟨sumEntry 7 4 ⟨116, 837, 0, 0, 5070, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1285
  ⟨sumEntry 8 3 ⟨-837, 116, 116, 837, 10140, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1311
  ⟨sumEntry 8 4 ⟨-116, -837, -837, 116, 10140, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1312
  ⟨sumEntry 9 3 ⟨-837, 116, -116, -837, 10140, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1338
  ⟨sumEntry 9 4 ⟨-116, -837, 837, -116, 10140, by decide⟩, (-1, -2, 0, 0)⟩, -- row 1339
  ⟨sumEntry 10 19 ⟨-475, -132, 0, 0, 2958, by decide⟩, (0, 0, -1, 1)⟩, -- row 1381
  ⟨sumEntry 10 20 ⟨132, -475, 0, 0, 2958, by decide⟩, (0, 0, -1, 1)⟩, -- row 1382
  ⟨sumEntry 11 19 ⟨475, 132, 132, -475, 5916, by decide⟩, (0, 0, -1, 1)⟩, -- row 1408
  ⟨sumEntry 11 20 ⟨-132, 475, 475, 132, 5916, by decide⟩, (0, 0, -1, 1)⟩, -- row 1409
  ⟨sumEntry 12 19 ⟨475, 132, -132, 475, 5916, by decide⟩, (0, 0, -1, 1)⟩, -- row 1435
  ⟨sumEntry 12 20 ⟨-132, 475, -475, -132, 5916, by decide⟩, (0, 0, -1, 1)⟩, -- row 1436
  ⟨pairEntry 12 22 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1842
  ⟨pairEntry 12 23 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1843
  ⟨pairEntry 12 25 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1845
  ⟨pairEntry 12 26 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1846
  ⟨pairEntry 12 28 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1848
  ⟨pairEntry 12 29 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1849
  ⟨pairEntry 12 30 (by decide) ⟨-15, 8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1850
  ⟨pairEntry 12 31 (by decide) ⟨-135, 72, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1851
  ⟨pairEntry 12 32 (by decide) ⟨-135, 72, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1852
  ⟨pairEntry 12 33 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1853
  ⟨pairEntry 12 34 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1854
  ⟨pairEntry 12 35 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1855
  ⟨pairEntry 12 36 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1856
  ⟨pairEntry 12 37 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1857
  ⟨pairEntry 12 38 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1858
  ⟨pairEntry 13 21 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1866
  ⟨pairEntry 13 23 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1868
  ⟨pairEntry 13 24 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1869
  ⟨pairEntry 13 26 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1871
  ⟨pairEntry 13 27 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1872
  ⟨pairEntry 13 29 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1874
  ⟨pairEntry 13 30 (by decide) ⟨-135, 72, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1875
  ⟨pairEntry 13 31 (by decide) ⟨-15, 8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1876
  ⟨pairEntry 13 32 (by decide) ⟨-135, 72, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1877
  ⟨pairEntry 13 33 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1878
  ⟨pairEntry 13 34 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1879
  ⟨pairEntry 13 35 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1880
  ⟨pairEntry 13 36 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1881
  ⟨pairEntry 13 37 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1882
  ⟨pairEntry 13 38 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1883
  ⟨pairEntry 14 21 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1890
  ⟨pairEntry 14 22 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1891
  ⟨pairEntry 14 24 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1893
  ⟨pairEntry 14 25 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1894
  ⟨pairEntry 14 27 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1896
  ⟨pairEntry 14 28 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1897
  ⟨pairEntry 14 30 (by decide) ⟨-135, 72, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1899
  ⟨pairEntry 14 31 (by decide) ⟨-135, 72, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1900
  ⟨pairEntry 14 32 (by decide) ⟨-15, 8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1901
  ⟨pairEntry 14 33 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1902
  ⟨pairEntry 14 34 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1903
  ⟨pairEntry 14 35 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1904
  ⟨pairEntry 14 36 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1905
  ⟨pairEntry 14 37 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1906
  ⟨pairEntry 14 38 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1907
  ⟨pairEntry 15 22 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1914
  ⟨pairEntry 15 23 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1915
  ⟨pairEntry 15 25 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1917
  ⟨pairEntry 15 26 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1918
  ⟨pairEntry 15 28 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1920
  ⟨pairEntry 15 29 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1921
  ⟨pairEntry 15 30 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1922
  ⟨pairEntry 15 31 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1923
  ⟨pairEntry 15 32 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1924
  ⟨pairEntry 15 34 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1926
  ⟨pairEntry 15 35 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1927
  ⟨pairEntry 15 37 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1929
  ⟨pairEntry 15 38 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1930
  ⟨pairEntry 16 21 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1935
  ⟨pairEntry 16 23 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1937
  ⟨pairEntry 16 24 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1938
  ⟨pairEntry 16 26 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1940
  ⟨pairEntry 16 27 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1941
  ⟨pairEntry 16 29 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1943
  ⟨pairEntry 16 30 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1944
  ⟨pairEntry 16 31 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1945
  ⟨pairEntry 16 32 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1946
  ⟨pairEntry 16 33 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1947
  ⟨pairEntry 16 35 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1949
  ⟨pairEntry 16 36 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1950
  ⟨pairEntry 16 38 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1952
  ⟨pairEntry 17 21 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1956
  ⟨pairEntry 17 22 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1957
  ⟨pairEntry 17 24 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1959
  ⟨pairEntry 17 25 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1960
  ⟨pairEntry 17 27 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1962
  ⟨pairEntry 17 28 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1963
  ⟨pairEntry 17 30 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1965
  ⟨pairEntry 17 31 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1966
  ⟨pairEntry 17 32 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1967
  ⟨pairEntry 17 33 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1968
  ⟨pairEntry 17 34 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1969
  ⟨pairEntry 17 36 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1971
  ⟨pairEntry 17 37 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1972
  ⟨pairEntry 18 22 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1977
  ⟨pairEntry 18 23 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1978
  ⟨pairEntry 18 25 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1980
  ⟨pairEntry 18 26 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1981
  ⟨pairEntry 18 28 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1983
  ⟨pairEntry 18 29 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1984
  ⟨pairEntry 18 30 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 1985
  ⟨pairEntry 18 31 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1986
  ⟨pairEntry 18 32 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1987
  ⟨pairEntry 18 34 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1989
  ⟨pairEntry 18 35 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1990
  ⟨pairEntry 18 37 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1992
  ⟨pairEntry 18 38 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 1993
  ⟨pairEntry 19 21 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1995
  ⟨pairEntry 19 23 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1997
  ⟨pairEntry 19 24 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 1998
  ⟨pairEntry 19 26 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2000
  ⟨pairEntry 19 27 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2001
  ⟨pairEntry 19 29 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2003
  ⟨pairEntry 19 30 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2004
  ⟨pairEntry 19 31 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 2005
  ⟨pairEntry 19 32 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2006
  ⟨pairEntry 19 33 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2007
  ⟨pairEntry 19 35 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2009
  ⟨pairEntry 19 36 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2010
  ⟨pairEntry 19 38 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2012
  ⟨pairEntry 20 21 (by decide) ⟨-99, -168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2013
  ⟨pairEntry 20 22 (by decide) ⟨0, 0, 56, -33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2014
  ⟨pairEntry 20 24 (by decide) ⟨0, 0, -56, 33, 1170, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2016
  ⟨pairEntry 20 25 (by decide) ⟨-99, -168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2017
  ⟨pairEntry 20 27 (by decide) ⟨99, 168, 56, -33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2019
  ⟨pairEntry 20 28 (by decide) ⟨99, 168, -56, 33, 2340, by decide⟩, (-1, -1, 0, 0)⟩, -- row 2020
  ⟨pairEntry 20 30 (by decide) ⟨45, -24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2022
  ⟨pairEntry 20 31 (by decide) ⟨45, -24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2023
  ⟨pairEntry 20 32 (by decide) ⟨15, -8, 0, 0, 102, by decide⟩, (0, 0, -1, 0)⟩, -- row 2024
  ⟨pairEntry 20 33 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2025
  ⟨pairEntry 20 34 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2026
  ⟨pairEntry 20 36 (by decide) ⟨-45, 24, -8, -15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2028
  ⟨pairEntry 20 37 (by decide) ⟨-45, 24, 8, 15, 612, by decide⟩, (0, 0, -1, 0)⟩, -- row 2029
  ⟨pairEntry 21 31 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2040
  ⟨pairEntry 21 32 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2041
  ⟨pairEntry 21 34 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2043
  ⟨pairEntry 21 35 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2044
  ⟨pairEntry 21 37 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2046
  ⟨pairEntry 21 38 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2047
  ⟨pairEntry 22 30 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2055
  ⟨pairEntry 22 32 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2057
  ⟨pairEntry 22 33 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2058
  ⟨pairEntry 22 35 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2060
  ⟨pairEntry 22 36 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2061
  ⟨pairEntry 22 38 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2063
  ⟨pairEntry 23 30 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2070
  ⟨pairEntry 23 31 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2071
  ⟨pairEntry 23 33 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2073
  ⟨pairEntry 23 34 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2074
  ⟨pairEntry 23 36 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2076
  ⟨pairEntry 23 37 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2077
  ⟨pairEntry 24 31 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2085
  ⟨pairEntry 24 32 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2086
  ⟨pairEntry 24 34 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2088
  ⟨pairEntry 24 35 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2089
  ⟨pairEntry 24 37 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2091
  ⟨pairEntry 24 38 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2092
  ⟨pairEntry 25 30 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2097
  ⟨pairEntry 25 32 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2099
  ⟨pairEntry 25 33 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2100
  ⟨pairEntry 25 35 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2102
  ⟨pairEntry 25 36 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2103
  ⟨pairEntry 25 38 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2105
  ⟨pairEntry 26 30 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2109
  ⟨pairEntry 26 31 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2110
  ⟨pairEntry 26 33 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2112
  ⟨pairEntry 26 34 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2113
  ⟨pairEntry 26 36 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2115
  ⟨pairEntry 26 37 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2116
  ⟨pairEntry 27 31 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2121
  ⟨pairEntry 27 32 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2122
  ⟨pairEntry 27 34 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2124
  ⟨pairEntry 27 35 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2125
  ⟨pairEntry 27 37 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2127
  ⟨pairEntry 27 38 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2128
  ⟨pairEntry 28 30 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2130
  ⟨pairEntry 28 32 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2132
  ⟨pairEntry 28 33 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2133
  ⟨pairEntry 28 35 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2135
  ⟨pairEntry 28 36 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2136
  ⟨pairEntry 28 38 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2138
  ⟨pairEntry 29 30 (by decide) ⟨0, 0, -152, -345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2139
  ⟨pairEntry 29 31 (by decide) ⟨1035, -456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2140
  ⟨pairEntry 29 33 (by decide) ⟨1035, -456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2142
  ⟨pairEntry 29 34 (by decide) ⟨0, 0, 152, 345, 6786, by decide⟩, (0, -1, 0, 1)⟩, -- row 2143
  ⟨pairEntry 29 36 (by decide) ⟨-1035, 456, 152, 345, 13572, by decide⟩, (0, -1, 0, 1)⟩, -- row 2145
  ⟨pairEntry 29 37 (by decide) ⟨-1035, 456, -152, -345, 13572, by decide⟩, (0, -1, 0, 1)⟩ -- row 2146
  ]

end Option2.NativeStress.HTPhaseKron

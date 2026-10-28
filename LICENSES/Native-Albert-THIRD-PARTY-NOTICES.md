# Native Albert: retained upstream dependencies and attribution

The upstream compact-albert-recognition project at `40d3b344180d9ddb78aaa2876873377c1e631515` is licensed under Apache-2.0. Robert MacGregor directs its AI-generated Lean development and is the maintainer. Reused code and dependencies retain their original credits and licenses. This notice has been adapted for the present distribution by clarifying upstream scope and replacing historical relative references with the retained grant and exact public sources; no original grant or material attribution is removed.

The build uses the following pinned dependencies. Their original license and
copyright notices remain in the isolated dependency checkout. The source package
does not vendor dependency source or compiled objects.

* Lean `v4.35.0-rc2`, official release compiler commit
  `11acb17ec6b07a8f9e9173e6845197929540936b`, Apache-2.0.
* Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, Apache-2.0,
  <https://github.com/leanprover-community/mathlib4>.
* Transitive locked packages and their complete commits are recorded in
  the upstream `lake-manifest.json`; the present lockfile is [../lake-manifest.json](../lake-manifest.json). Original notices remain in each dependency. Verification
  records bind their exact source versions rather than a moving branch name.
  All inspected packages use Apache-2.0 except `Cli`, which uses MIT. Exact
  source revisions are recorded in the lockfile.

`Glennie/Native/CubicJordan.lean` adapts the general cubic-identity implication
from `AlbertLean/CubicJordan.lean` in the Apache-2.0 licensed
albert-lean repository, commit `dd06ef5d423a0e4a5d814d2c221e999b98887ee1`.
The original source SHA256 is
`cc885b590ac2317fbde15b490d8205d684fafbf7dbe4ffd883155275a0986826`.
The original file has no separate copyright/author header. Its documentation
and proof structure are preserved; the adaptation changes ℚ to ℝ, namespace,
and module API. The full upstream license is retained at
[Native-Albert-Apache-2.0.txt](Native-Albert-Apache-2.0.txt), byte-identical to
the ancestor grant previously named `licenses/albert-lean-CubicJordan-LICENSE`.
The exact source is [albert-frame-triple-invariants](https://github.com/macgregor-sudo/albert-frame-triple-invariants/blob/dd06ef5d423a0e4a5d814d2c221e999b98887ee1/AlbertLean/CubicJordan.lean). This is a general algebraic lemma;
the native compact cubic identity must be independently proved, and no split
Albert theorem is transported by a type-name substitution.

`CompositionAlgebras/Conic/Doubling.lean` is a reading reference, not a
source or dependency of the selected proofs. Its source repository is
`skipgaribaldi/CompositionAlgebras-lean`, commit
`5f902d1d6c090b7a4c29178253ddbb4d03310da0`, Apache-2.0. The file has SHA256
`bdafd08e166f557017067ab457a805495a8230fc72951c1ce11fa29739949322`
and copyright (c) 2026 Skip Garibaldi. Its original upstream notice referred to
`licenses/CompositionAlgebras-Doubling-LICENSE`; the public source and grant are
at [the pinned source repository](https://github.com/skipgaribaldi/CompositionAlgebras-lean/tree/5f902d1d6c090b7a4c29178253ddbb4d03310da0). That reading-only license file is not part of this package. No adaptation
of this file is distributed in this repository.

The original software-source bibliography is [the pinned upstream BIBLIOGRAPHY.bib](https://github.com/macgregor-sudo/compact-albert-recognition/blob/40d3b344180d9ddb78aaa2876873377c1e631515/BIBLIOGRAPHY.bib); the public relocation/excerpt map is [../THIRD_PARTY_NOTICES.md](../THIRD_PARTY_NOTICES.md#native-albert-code). These distinguish the adapted cubic lemma from the doubling reading reference. Neither attribution nor licensing asserts source-author endorsement or independent human mathematical review.

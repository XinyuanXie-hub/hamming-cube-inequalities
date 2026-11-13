# Reproduce the verified solution

This archive contains the approved Challenge.lean, its unchanged comparator
configuration, the complete Solution.lean and Solution/ proof modules, and the
pinned template configuration. Exploratory Gaussian/Arb files are not required.

Use Linux with Python 3, bubblewrap with working user namespaces, and the Lean
toolchain selected by lean-toolchain (Lean 4.35.0). From the extracted root:

    lake exe cache get
    lake build Challenge
    lake build Solution
    bash scripts/verify-comparator.sh

The final command invokes the unchanged template workflow, including Lean,
NanoDa and con-ron. Compilation alone is not the final check. A host that
restricts user namespaces must use its supported approved execution mechanism;
do not remove the comparator sandbox or any checker.

Challenge contains the three intentional sorry placeholders of the reviewed
reference. Solution and every imported proof module are complete and contain
no sorry or added axioms. The final comparator log and source SHA-256 hashes
are included in evidence/ and VERIFICATION.json.

REVIEW.md is the historical stage-1 review and provisioning record.
OPTIMIZATION.md records the mathematical simplification and measured comparison.
Theorem 1.1's additional sharpness prose is outside the approved challenge.
The original archive was unpublished; it has now been imported into this repository. The archived verification evidence predates publication.

**Structure for VCoT-Bench**:

- **org**: the ground-truth, generated from [Verus-Bench](https://github.com/microsoft/verus-proof-synthesis).

- **ratio**: Sub-dataset for ratio dimension. Each subdirectory corresponds to a specific removal rate (e.g., “10” denotes a 10% removal rate).

- **type**: Sub-dataset for type dimension. Each subdirectory corresponds to the removal of a specific proof type (e.g., “invariant” denotes that all loop invariants are removed).

- **loc**: Sub-dataset for location dimension. Each subdirectory corresponds to a specific location of semantic block removal (e.g. "front" denotes all front blocks are removed).

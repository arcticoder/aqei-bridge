# Uploading Lean Proofs to DeSci Nodes

This guide covers how to prepare, package, and publish the `aqei-bridge` Lean 4
formal proofs to DeSci Nodes.

For the **complete API reference** (endpoint details, auth, the full `publish.mjs`
script), see
[`energy/docs/desci-nodes-upload.md`](../../energy/docs/desci-nodes-upload.md).

---

## Project layout

```
lean/
├── lakefile.lean          ← root build descriptor (package + Mathlib dep)
└── src/
    ├── AqeiBridge.lean    ← root module (imports all submodules)
    └── AqeiBridge/        ← 37 source files, ~5 150 LOC
        ├── CausalPoset.lean
        ├── StressEnergy.lean
        ├── AQEI_Cone.lean
        ├── Conjecture.lean
        ├── ...             (see below for full list)
        └── Examples/
            └── DiamondPresheaf.lean
```

### What **not** to upload

| Path | Reason |
|------|--------|
| `lean/.lake/` | Build artifacts, toolchain cache — very large (~GB), reproducible from source |
| `lean/.lake/packages/mathlib/` | 100k+ file upstream dependency |

---

## What to upload

| Component | File | DeSci component type |
|-----------|------|----------------------|
| Lean source tree | `aqei-bridge-lean-src.zip` | `code` |
| Generated HTML docs (optional) | `AqeiBridge-docs.tar.gz` | `supplements` |
| Exported PDF summary (optional) | `aqei-bridge-axioms.pdf` | `pdf` |

---

## Step 1 — Create the source archive

```bash
cd /home/echo_/Code/asciimath/aqei-bridge

zip -r aqei-bridge-lean-src.zip lean/ \
    --exclude "lean/.lake/*"

# Verify (should list lean/lakefile.lean and lean/src/... only)
unzip -l aqei-bridge-lean-src.zip | head -20
```

Approximate size: ~0.5 MB (source only, no build artifacts).

---

## Step 2 — (Optional) Generate HTML documentation

[`doc-gen4`](https://github.com/leanprover/doc-gen4) produces browsable HTML docs
from Lean 4 source and docstrings.

```bash
cd lean/

# Add doc-gen4 to lakefile.lean (one-time setup)
cat >> lakefile.lean <<'EOF'

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
EOF

lake build AqeiBridge:docs

# Output lands in .lake/build/doc/
tar -czf ../AqeiBridge-docs.tar.gz -C .lake/build doc/
```

> **Note**: `lake build AqeiBridge:docs` triggers a full Mathlib build on first
> run (~60–90 min). Subsequent runs with a warmed cache are fast.

---

## Step 3 — (Optional) Export a theorem summary PDF

A plain-text or LaTeX proof summary can be extracted via:

```bash
# Dump all theorem/lemma/def lines with their locations
grep -rn "^theorem\|^lemma\|^def\|^noncomputable def\|^abbrev" \
     lean/src/AqeiBridge/ \
  | sed 's|lean/src/||' \
  > aqei-bridge-theorem-index.txt

# Then compile to PDF using any LaTeX or markdown→PDF pipeline
```

---

## Step 4 — Upload to DeSci Nodes

Prerequisites:

- Node.js ≥ 18
- `DESCI_NODES_API_KEY` set (in `/home/echo_/Code/asciimath/energy/.env` or
  `export DESCI_NODES_API_KEY=...`)
- `npm install @desci-labs/nodes-lib ethers` (run once in a temp dir)

### 4a. Create a draft node

```js
// createDraft.mjs
import fetch from "node-fetch";

const API = "https://nodes-api.desci.com";
const KEY = process.env.DESCI_NODES_API_KEY;

const res = await fetch(`${API}/v1/nodes/createDraft`, {
  method: "POST",
  headers: { "api-key": KEY, "Content-Type": "application/json" },
  body: JSON.stringify({
    title: "AqeiBridge: Lean 4 Formal Proofs of Causal Stability under AQEI Perturbations",
    defaultLicense: "CC-BY-4.0",
    researchFields: [
      { id: 1, name: "Mathematics" },
      { id: 45, name: "Mathematical Logic and Foundations" },
    ],
  }),
});
const { node } = await res.json();
console.log("uuid:", node.uuid);   // save this
```

```bash
node createDraft.mjs
```

### 4b. Upload the source zip

```js
// uploadSource.mjs
import { createReadStream } from "fs";
import FormData from "form-data";
import fetch from "node-fetch";

const API  = "https://nodes-api.desci.com";
const KEY  = process.env.DESCI_NODES_API_KEY;
const UUID = "<uuid-from-step-4a>";

const form = new FormData();
form.append("uuid", UUID);
form.append("contextPath", "/");
form.append("componentType", "code");
form.append("files", createReadStream("aqei-bridge-lean-src.zip"), {
  filename: "aqei-bridge-lean-src.zip",
});

const res = await fetch(`${API}/v1/data/update`, {
  method: "POST",
  headers: { "api-key": KEY, ...form.getHeaders() },
  body: form,
});
console.log(await res.json());
```

Repeat for any additional files (HTML docs tarball, PDF, etc.), changing
`componentType` and the filename/path accordingly.

### 4c. Publish

```js
// publish.mjs  (identical to the script in energy/docs/desci-nodes-upload.md)
import { getPublishClient } from "@desci-labs/nodes-lib/browser";
import { ethers } from "ethers";

const { signerFromPkey } = await import("@desci-labs/nodes-lib/browser");

const API  = "https://nodes-api.desci.com";
const KEY  = process.env.DESCI_NODES_API_KEY;
const UUID = "<uuid-from-step-4a>";

const wallet  = ethers.Wallet.createRandom();
const signer  = await signerFromPkey(wallet.privateKey);
const client  = getPublishClient({ apiUrl: API, apiKey: KEY }, signer);

const result  = await client.publishNode(UUID);
console.log(JSON.stringify(result, null, 2));
// result contains: dpid, ceramicStream, manifestCid
```

---

## Suggested metadata

```json
{
  "title": "AqeiBridge: Lean 4 Formal Proofs of Causal Stability under AQEI Perturbations",
  "defaultLicense": "CC-BY-4.0",
  "researchFields": [
    { "id": 1,  "name": "Mathematics" },
    { "id": 45, "name": "Mathematical Logic and Foundations" }
  ]
}
```

> **Finding field IDs**: `GET https://nodes-api.desci.com/v1/researchFields?q=logic`

---

## After publishing

The output of `publish.mjs` includes:

| Field | Example |
|-------|---------|
| `dpid` | `1029` |
| `nodeUrl` | `https://nodes.desci.com/node/<uuid>` |
| `dpidUrl` | `https://dpid.org/1029` |
| `ceramicStream` | `kjzl6kcym7w8y...` |
| `manifestCid` | `bafkrei...` |

Add these to `docs/TODO-completed.md` and the repo README.

---

## Full module list (`lean/src/AqeiBridge/`)

| File | Topic |
|------|-------|
| `AqeiBridge.lean` | Root module (imports all) |
| `Spacetime.lean` | Spacetime type definitions |
| `CausalPoset.lean` | Causal partial-order structure |
| `CausalIntervals.lean` | Alexandrov intervals |
| `CausalContinuity.lean` | Continuity in causal order |
| `CausalStability.lean` | Stability lemmas |
| `SpacetimeCausalPoset.lean` | Spacetime ↔ causal-poset bridge |
| `StressEnergy.lean` | Stress-energy tensor formalization |
| `AQEI_Cone.lean` | Averaged quantum energy inequality cone |
| `AlexandrovPresheaf.lean` | Alexandrov-topology presheaf |
| `AlexandrovPresheafMathlib.lean` | Mathlib integration for above |
| `Chambers.lean` | Chamber decomposition |
| `ChamberConstancy.lean` | Constancy of fields across chambers |
| `ChamberIndexedModel.lean` | Chamber-indexed model structure |
| `ChamberClosedChamberBridge.lean` | Open/closed chamber bridge |
| `Conjecture.lean` | Interface-level conjecture statements |
| `GlobalConjectures.lean` | Global formulations |
| `GeneratedPosetConjectures.lean` | Auto-generated poset conjectures |
| `DiscreteChronology.lean` | Discrete causal chronology |
| `DiscreteCausality.lean` | Discrete causality framework |
| `DiscreteCausalPoset.lean` | Discrete causal partial orders |
| `DiscreteH1QuantitativeUpgrade.lean` | Quantitative H₁ upgrade |
| `DiscreteHomologyProxy.lean` | Discrete H₁ homology proxy |
| `DiscreteStabilityBridge.lean` | Stability bridge (discrete) |
| `DiscreteChamberStability.lean` | Chamber stability (discrete) |
| `DiscreteConnectedComponents.lean` | π₀ of discrete poset |
| `DiscreteFutureContinuity.lean` | Future-continuity (discrete) |
| `DiscreteHausdorff.lean` | Hausdorff separation (discrete) |
| `PosetHomologyProxy.lean` | Poset homology proxy |
| `OrderComplexProxy.lean` | Order-complex proxy construction |
| `OrderComplexBridge.lean` | Order complex ↔ chain complex |
| `H1Stability.lean` | H₁ stability theorem |
| `Cech01.lean` | Čech 0/1-cochains |
| `GraphDistance.lean` | Graph-distance on posets |
| `FiniteCausalPoset.lean` | Finite causal posets |
| `Examples/DiamondPresheaf.lean` | Diamond poset example |
| `Tactics/Linear.lean` | Custom linear-arithmetic tactic |

# AI Assurance as a Category-Theoretic Preservation Structure

A Lean 4 formalization of the mathematical core of AI assurance, using the Grothendieck construction over an operational category.

## What this repository contains

The main file is the Lean 4 formalization: `AIAssurance.lean`.

It does **not** prove that any real-world AI system is safe or compliant. It proves that a specific mathematical structure, an indexed evidence fibration over an operational category, has the preservation properties required for inspectable AI governance.

The formalization proves five components:

1. **IndexedAssurance structure**  
   The operational category `O`, evidence fiber family `F`, forward transport `push`, backward audit `pull`, adjunction `push ⊣ pull`, standard section, and Beck-Chevalley field.

2. **EvidenceCategory as Grothendieck construction**  
   The total evidence category `E = ∫_O F` is derived, not a free parameter.

3. **Standard section faithfulness**  
   `S : O ⥤ E` is faithful because `S ⋙ U = 𝟭 O`.

4. **Opcartesian and cartesian universal properties**  
   `opcart_factor` and `cart_factor` prove TotalCategory-level unique factorization through the canonical lifts.

5. **Collapse counterexample**  
   `CollapseCounterexample` proves that without a faithful evidence layer, governance-relevant distinctions can collapse. Theorem: `forgetting_trace_layer_can_collapse_distinctions`.

## What is NOT proven

`beck_chevalley` is a field, an external structural assumption, not derived from `adj + push_comp + pull_comp`. It holds for specific instances but is not proven in general.

This formalization does not cover:

- real-world AI systems or deployments
- EU AI Act compliance
- completeness of the evidence layer
- the translation from formal model to operational practice

## Requirements

- Lean 4
- Mathlib, current stable
- Lake

Verification:

```bash
lake update
lake exe cache get
lake env lean AIAssurance.lean
```

Successful verification returns to prompt with no output.

## Mathematical interpretation

The operational category `O` represents the observable actions of an AI system across organizational boundaries. The evidence fiber family `F` assigns, to each operational state, a category of audit traces, responsibility records, and judgment grounds. The Grothendieck construction `∫_O F` is the total category in which both operational transitions and their evidence travel together. The faithfulness of the standard section `S` means that distinct operational transitions cannot be collapsed by the evidence layer.

## Positioning

This formalization is the mathematical verification core for the ADIC (Advanced Data Integrity by Ledger of Computation) architecture. It establishes that the preservation structure required for inspectable AI governance, traceability, accountability, and auditability after composition, has a precise category-theoretic characterization that can be machine-checked independently.


# Typed Mereology of Linguistics -- Formalization Target

## Goal

Formalize the core axiom system from "Toward a Typed Mereology of Linguistics" (Reynolds 2025) in Lean 4. The paper defines a typed mereological framework where parthood is indexed to analytical lenses (phenomena, methods, theory, institutions).

## Definitions

### Universe

We have a type `Entity` representing linguistic objects (subfields, categories, constructions, etc.).

### Typed Parthood Relations

Four partial orders over `Entity`:

- `phen_le : Entity → Entity → Prop` (phenomena lens)
- `meth_le : Entity → Entity → Prop` (methods lens)
- `theory_le : Entity → Entity → Prop` (theory lens)
- `inst_le : Entity → Entity → Prop` (institutional lens)

### Axioms (per lens)

Each typed parthood relation is a partial order:

1. **Reflexive**: ∀ x, lens_le x x
2. **Transitive**: ∀ x y z, lens_le x y → lens_le y z → lens_le x z
3. **Antisymmetric**: ∀ x y, lens_le x y → lens_le y x → x = y

### Overlap

Two entities overlap under a lens iff they share a common part:

`overlap_lens (x y : Entity) : Prop := ∃ z, lens_le z x ∧ lens_le z y`

### Fusion

The fusion of x and y under a lens is the least upper bound:

`fusion_lens (x y : Entity) : Entity` such that:
- `lens_le x (fusion_lens x y)`
- `lens_le y (fusion_lens x y)`
- ∀ w, lens_le x w → lens_le y w → lens_le (fusion_lens x y) w

### Subfields as Bundles

A subfield is a triple `⟨P, M, T⟩` where P, M, T are sets of entities. Lens-relative parthood is componentwise:

`S₁ phen_le S₂ iff P₁ ⊆ P₂`
`S₁ meth_le S₂ iff M₁ ⊆ M₂`
`S₁ theory_le S₂ iff T₁ ⊆ T₂`

### Adjacency

`adj (x y : Entity) : Prop` -- x and y are distinct but systematically interact. Adjacency is:
- Symmetric: adj x y → adj y x
- Irreflexive: ¬ adj x x

## Theorems to Prove

### T1: Independence of lenses
Two entities can be related under one lens but not another:
∃ x y, phen_le x y ∧ ¬ meth_le x y

### T2: Consistent multi-lens decomposition
The same entity can have different parts under different lenses without contradiction. Formally: the four partial orders can coexist on the same carrier set without producing inconsistency.

### T3: Overlap under one lens does not entail overlap under another
∃ x y, overlap_phen x y ∧ ¬ overlap_meth x y

### T4: Fusion respects lens typing
fusion_phen x y need not equal fusion_meth x y (fusions are lens-relative)

### T5: Adjacency is distinct from overlap
∃ x y, adj x y ∧ ¬ overlap_phen x y (adjacency does not require shared parts)

### T6: Bundle parthood is componentwise
If S₁ phen_le S₂ and S₁ meth_le S₂, it does NOT follow that S₁ theory_le S₂ (lenses are independent in bundles)

### T7: Adjacency is bidirectional and homeostatic (structural constraint)
If adj x y, then there exist lens₁ and lens₂ such that x contributes to maintaining y under lens₁ and y contributes to maintaining x under lens₂. (This formalizes the bidirectional interface claim.)

## Notes for the Formalizer

- The four lenses are independent partial orders on the same carrier type. This is the core structural claim.
- T2 is the key consistency result: typed parthood with different lenses doesn't produce contradictions.
- T1, T3, T4, T5, T6 are existence/separation results showing the lenses genuinely come apart.
- T7 is the most ambitious: it tries to formalize the "homeostatic interface" claim. If this is too hard, skip it -- T1-T6 are the core contribution.
- The framework should be parametric: it should work for any number of lenses, not just four. The four specific lenses (phenomena, methods, theory, institutions) are instances.
- Prefer Mathlib conventions where applicable.

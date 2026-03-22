/-
# Typed Mereology of Linguistics

Formalization of the core axiom system from "Toward a Typed Mereology of Linguistics"
(Reynolds 2025). The framework defines typed mereological relations where parthood is
indexed to analytical lenses (phenomena, methods, theory, institutions).
-/

import Mathlib

/-! ## Core Definitions -/

/-- A `TypedMereology` packages four independent partial orders (lenses) and an
adjacency relation over a common carrier type `Entity`. -/
structure TypedMereology (Entity : Type*) where
  /-- Phenomena lens partial order -/
  phen_le : Entity → Entity → Prop
  phen_refl : ∀ x, phen_le x x
  phen_trans : ∀ x y z, phen_le x y → phen_le y z → phen_le x z
  phen_antisymm : ∀ x y, phen_le x y → phen_le y x → x = y
  /-- Methods lens partial order -/
  meth_le : Entity → Entity → Prop
  meth_refl : ∀ x, meth_le x x
  meth_trans : ∀ x y z, meth_le x y → meth_le y z → meth_le x z
  meth_antisymm : ∀ x y, meth_le x y → meth_le y x → x = y
  /-- Theory lens partial order -/
  theory_le : Entity → Entity → Prop
  theory_refl : ∀ x, theory_le x x
  theory_trans : ∀ x y z, theory_le x y → theory_le y z → theory_le x z
  theory_antisymm : ∀ x y, theory_le x y → theory_le y x → x = y
  /-- Institutional lens partial order -/
  inst_le : Entity → Entity → Prop
  inst_refl : ∀ x, inst_le x x
  inst_trans : ∀ x y z, inst_le x y → inst_le y z → inst_le x z
  inst_antisymm : ∀ x y, inst_le x y → inst_le y x → x = y
  /-- Adjacency: symmetric, irreflexive interaction relation -/
  adj : Entity → Entity → Prop
  adj_symm : ∀ x y, adj x y → adj y x
  adj_irrefl : ∀ x, ¬ adj x x

namespace TypedMereology

variable {Entity : Type*} (M : TypedMereology Entity)

/-! ### Overlap -/

/-- Two entities overlap under the phenomena lens iff they share a common part. -/
def overlap_phen (x y : Entity) : Prop := ∃ z, M.phen_le z x ∧ M.phen_le z y

/-- Two entities overlap under the methods lens iff they share a common part. -/
def overlap_meth (x y : Entity) : Prop := ∃ z, M.meth_le z x ∧ M.meth_le z y

/-- Two entities overlap under the theory lens iff they share a common part. -/
def overlap_theory (x y : Entity) : Prop := ∃ z, M.theory_le z x ∧ M.theory_le z y

/-- Two entities overlap under the institutional lens iff they share a common part. -/
def overlap_inst (x y : Entity) : Prop := ∃ z, M.inst_le z x ∧ M.inst_le z y

/-! ### Fusion (Least Upper Bound) -/

/-- A fusion of `x` and `y` under the phenomena lens is a least upper bound. -/
structure PhenFusion (x y fus : Entity) : Prop where
  le_left : M.phen_le x fus
  le_right : M.phen_le y fus
  least : ∀ w, M.phen_le x w → M.phen_le y w → M.phen_le fus w

/-- A fusion of `x` and `y` under the methods lens is a least upper bound. -/
structure MethFusion (x y fus : Entity) : Prop where
  le_left : M.meth_le x fus
  le_right : M.meth_le y fus
  least : ∀ w, M.meth_le x w → M.meth_le y w → M.meth_le fus w

/-! ### Subfields as Bundles -/

/-- A subfield is a triple of sets of entities, representing phenomena, methods,
and theory components. -/
structure Subfield (Entity : Type*) where
  P : Set Entity  -- phenomena
  M : Set Entity  -- methods
  T : Set Entity  -- theory

/-- Lens-relative parthood on subfields is componentwise subset inclusion. -/
def subfield_phen_le (S₁ S₂ : Subfield Entity) : Prop := S₁.P ⊆ S₂.P
def subfield_meth_le (S₁ S₂ : Subfield Entity) : Prop := S₁.M ⊆ S₂.M
def subfield_theory_le (S₁ S₂ : Subfield Entity) : Prop := S₁.T ⊆ S₂.T

end TypedMereology

/-! ## Theorems -/

/-! ### T1: Independence of lenses

Two entities can be related under one lens but not another. We prove this by
constructing a concrete model on `Fin 2`. -/

/-
PROVIDED SOLUTION
Construct a model on `Bool` (or `Fin 2`). Let entity 0 = false, entity 1 = true.
- phen_le: the natural order (false ≤ true, plus reflexivity)
- meth_le: equality only (discrete order)
- theory_le, inst_le: equality only
- adj: empty

Then phen_le false true holds but meth_le false true does not.

Use `refine ⟨Bool, ⟨..⟩, false, true, ?_, ?_⟩` and construct the TypedMereology manually. For the partial order axioms on the discrete orders, everything follows from equality. For phen_le, define it as `fun a b => a = false ∨ b = true` or simply `(· ≤ ·)` using Bool's natural ≤.
-/
theorem T1_independence_of_lenses :
    ∃ (Entity : Type) (M : TypedMereology Entity) (x y : Entity),
      M.phen_le x y ∧ ¬ M.meth_le x y := by
  fconstructor;
  exact ULift ℕ;
  refine' ⟨ _, _, _, _, _ ⟩;
  refine' { phen_le := fun x y => x.down ≤ y.down, phen_refl := _, phen_trans := _, phen_antisymm := _, meth_le := fun x y => x.down = y.down, meth_refl := _, meth_trans := _, meth_antisymm := _, theory_le := fun x y => x.down = y.down, theory_refl := _, theory_trans := _, theory_antisymm := _, inst_le := fun x y => x.down = y.down, inst_refl := _, inst_trans := _, inst_antisymm := _, adj := fun x y => x.down ≠ y.down, adj_symm := _, adj_irrefl := _ } <;> norm_num;
  exacts [ fun x y z h₁ h₂ => le_trans h₁ h₂, fun x y h₁ h₂ => le_antisymm h₁ h₂, fun x y h => Ne.symm h, ⟨ 0 ⟩, ⟨ 1 ⟩, by simp +decide, by simp +decide ]

/-! ### T2: Consistent multi-lens decomposition

The four partial orders can coexist on the same carrier set without producing
inconsistency. This is witnessed by the existence of a non-trivial model. -/

/-
PROVIDED SOLUTION
Construct a model on `Fin 4` with four entities {0,1,2,3}. Define:
- phen_le: 0 ≤ 1 (plus reflexivity, otherwise discrete). So phen_le a b iff a = b or (a = 0 ∧ b = 1).
- meth_le: 1 ≤ 2 (plus reflexivity, otherwise discrete). So meth_le a b iff a = b or (a = 1 ∧ b = 2).
- theory_le: 2 ≤ 3 (plus reflexivity, otherwise discrete).
- inst_le: discrete (equality only).
- adj: False.

Then:
- ∃ x ≠ y: 0 ≠ 1
- phen_le 0 1 ∧ ¬ meth_le 0 1
- meth_le 1 2 ∧ ¬ theory_le 1 2
- theory_le 2 3 ∧ ¬ inst_le 2 3

Each partial order needs reflexivity, transitivity, antisymmetry checked. Since each has only one non-trivial edge (and no chains), transitivity and antisymmetry hold trivially. Use `Fin.val` comparisons and `omega` or `decide` to discharge goals.
-/
theorem T2_consistent_multi_lens :
    ∃ (Entity : Type) (M : TypedMereology Entity),
      (∃ x y : Entity, x ≠ y) ∧
      (∃ x y : Entity, M.phen_le x y ∧ ¬ M.meth_le x y) ∧
      (∃ x y : Entity, M.meth_le x y ∧ ¬ M.theory_le x y) ∧
      (∃ x y : Entity, M.theory_le x y ∧ ¬ M.inst_le x y) := by
  use ULift ( Fin 4 );
  refine' ⟨ _, _, _, _, _ ⟩;
  refine' { phen_le := fun x y => x.down = y.down ∨ x.down = 0 ∧ y.down = 1, phen_refl := _, phen_trans := _, phen_antisymm := _, meth_le := fun x y => x.down = y.down ∨ x.down = 1 ∧ y.down = 2, meth_refl := _, meth_trans := _, meth_antisymm := _, theory_le := fun x y => x.down = y.down ∨ x.down = 2 ∧ y.down = 3, theory_refl := _, theory_trans := _, theory_antisymm := _, inst_le := fun x y => x.down = y.down, inst_refl := _, inst_trans := _, inst_antisymm := _, adj := fun x y => False, adj_symm := _, adj_irrefl := _ };
  all_goals simp +decide [ Fin.forall_fin_succ, Fin.exists_fin_succ ] at *

/-! ### T3: Overlap under one lens does not entail overlap under another -/

/-
PROVIDED SOLUTION
Use a model on `Fin 3` with entities {0, 1, 2}. Define:
- phen_le: a ≤ b iff a = b, or (a = 0 ∧ b = 1), or (a = 0 ∧ b = 2). So 0 is a phen-part of both 1 and 2.
- meth_le: discrete (equality only).
- theory_le, inst_le: discrete.
- adj: False.

Then overlap_phen 1 2 holds (witnessed by z = 0, since phen_le 0 1 and phen_le 0 2).
But overlap_meth 1 2 fails: the only z with meth_le z 1 is z = 1, and meth_le 1 2 is false (1 ≠ 2).

For the partial order axioms on phen_le: reflexivity is by a = a case; transitivity holds since 0 is the only non-trivial source and anything 0 ≤ goes to is already at a leaf; antisymmetry holds since the only non-reflexive relations go from 0 to 1 or 0 to 2, and there's no reverse edge. Use `decide` or case analysis on `Fin 3`.
-/
theorem T3_overlap_independence :
    ∃ (Entity : Type) (M : TypedMereology Entity) (x y : Entity),
      M.overlap_phen x y ∧ ¬ M.overlap_meth x y := by
  fconstructor;
  exact ULift ( Fin 3 );
  refine' ⟨ _, _, _, _, _ ⟩;
  refine' { phen_le := fun x y => x.down = y.down ∨ x.down = 0 ∧ y.down = 1 ∨ x.down = 0 ∧ y.down = 2, phen_refl := _, phen_trans := _, phen_antisymm := _, meth_le := fun x y => x.down = y.down, meth_refl := _, meth_trans := _, meth_antisymm := _, theory_le := fun x y => x.down = y.down, theory_refl := _, theory_trans := _, theory_antisymm := _, inst_le := fun x y => x.down = y.down, inst_refl := _, inst_trans := _, inst_antisymm := _, adj := fun x y => False, adj_symm := _, adj_irrefl := _ } <;> simp +decide [ TypedMereology.overlap_phen, TypedMereology.overlap_meth ];
  exact ⟨ 1 ⟩;
  exact ⟨ 2 ⟩;
  · exact ⟨ ⟨ 0 ⟩, by decide, by decide ⟩;
  · rintro ⟨ z, hz₁, hz₂ ⟩ ; fin_cases z <;> trivial;

/-! ### T4: Fusion respects lens typing

Fusions under different lenses can differ: there exist entities and a model where
the phenomena-fusion and the methods-fusion of the same pair are distinct. -/

/-
PROVIDED SOLUTION
Construct a model on `Fin 4` with entities {0, 1, 2, 3}. Define:
- phen_le: forms a lattice where 0 ≤ 2, 1 ≤ 2, 0 ≤ 3, 1 ≤ 3, 2 ≤ 3, plus reflexivity. Actually simpler: just use the natural order on Fin 4 (i.e., a.val ≤ b.val). Then the phen-fusion (LUB) of 0 and 1 is 1.
- meth_le: define as a.val ≤ b.val but with a different arrangement. E.g., define a custom order where 0 ≤ 1, 0 ≤ 2, 0 ≤ 3, 1 ≤ 3, 2 ≤ 3, plus reflexivity. Then the meth-fusion of 0 and 1 is 1, but the meth-fusion of 1 and 2 is 3 (while phen-fusion of 1 and 2 is 2).

Actually, let me use a simpler approach. Use `Fin 3` = {0, 1, 2}.
- phen_le: natural order (a.val ≤ b.val). Then PhenFusion of 0 and 1 has fp = 1 (since phen_le 0 1 and phen_le 1 1, and for any w with 0 ≤ w and 1 ≤ w, we have 1 ≤ w).
- meth_le: 0 ≤ 1, 0 ≤ 2, plus reflexivity (but 1 and 2 are incomparable). Then MethFusion of 0 and 1 has fm = 1.

Hmm, that gives fp = fm = 1. Let me try differently.

Use `Fin 4` = {0, 1, 2, 3}.
- phen_le: 0 ≤ 2, 1 ≤ 2, plus reflexivity (and 0 ≤ 3, 1 ≤ 3, 2 ≤ 3 to make it transitive, or just keep it as: phen_le a b iff a = b or b = 2 and a ∈ {0,1} or b = 3). Actually too complex.

Simplest: use `Bool × Bool` as Entity (4 elements).
- phen_le: lexicographic order? Or product order.
  Product order: (a₁,a₂) ≤ (b₁,b₂) iff a₁ ≤ b₁ ∧ a₂ ≤ b₂.
  Then PhenFusion of (false,true) and (true,false) is (true,true).
- meth_le: reverse product order on the second component: (a₁,a₂) ≤ (b₁,b₂) iff a₁ ≤ b₁ ∧ b₂ ≤ a₂.
  Hmm, this is not standard.

Even simpler: just use `Fin 5` = {0, 1, 2, 3, 4}.
- phen_le: natural ≤. PhenFusion of 1 and 2 is fp = 2.
- meth_le: all equal except define a custom order where MethFusion of 1 and 2 is fm = 3.
  E.g., meth_le: 1 ≤ 3, 2 ≤ 3, plus reflexivity (discrete otherwise). Then fm = 3 is the MethFusion of 1 and 2.
  Check: meth_le 1 3 ✓, meth_le 2 3 ✓, and for any w with meth_le 1 w and meth_le 2 w, we need meth_le 3 w. The only such w must have both 1 ≤ w and 2 ≤ w, so w = 3 (since 1 and 2 only go up to 3). So fm = 3.

With natural ≤ on Fin 5: phen_le 1 w and phen_le 2 w means w ≥ 2, so PhenFusion of 1 and 2 is fp = 2.
And fp = 2 ≠ 3 = fm. ✓

Let me define:
- x = (1 : Fin 5), y = (2 : Fin 5), fp = (2 : Fin 5), fm = (3 : Fin 5)
- phen_le: natural ≤ on Fin 5 (a.val ≤ b.val)
- meth_le: 1 ≤ 3, 2 ≤ 3, plus reflexivity (discrete otherwise); i.e., meth_le a b iff a = b or (a ∈ {1,2} ∧ b = 3). Need transitivity: if a ≤ b and b ≤ c, ... 1 ≤ 3 and 3 ≤ 3 gives 1 ≤ 3 ✓. 1 ≤ 3 and 3 ≤ c means c = 3, so 1 ≤ 3 ✓. Antisymmetry: if a ≤ b and b ≤ a, then either both reflexive or we'd need 1 ≤ 3 and 3 ≤ 1 which doesn't happen. ✓
- theory_le, inst_le: discrete
- adj: False

Then fp ≠ fm since (2 : Fin 5) ≠ (3 : Fin 5).

For phen_le, use `fun a b => a.val ≤ b.val` and standard Fin order lemmas.
For meth_le, use `fun a b => a = b ∨ ((a = 1 ∨ a = 2) ∧ b = 3)`.

Use `decide` or `omega` to close Fin goals.
-/
theorem T4_fusion_lens_relativity :
    ∃ (Entity : Type) (M : TypedMereology Entity) (x y fp fm : Entity),
      M.PhenFusion x y fp ∧ M.MethFusion x y fm ∧ fp ≠ fm := by
  fconstructor;
  exact Fin 5;
  refine' ⟨ _, 1, 2, 2, 3, _, _, _ ⟩;
  refine' { phen_le := fun a b => a.val ≤ b.val, phen_refl := _, phen_trans := _, phen_antisymm := _, meth_le := fun a b => a = b ∨ ( a = 1 ∧ b = 3 ) ∨ ( a = 2 ∧ b = 3 ), meth_refl := _, meth_trans := _, meth_antisymm := _, theory_le := fun a b => a = b, theory_refl := _, theory_trans := _, theory_antisymm := _, inst_le := fun a b => a = b, inst_refl := _, inst_trans := _, inst_antisymm := _, adj := fun a b => False, adj_symm := _, adj_irrefl := _ };
  all_goals norm_cast;
  · constructor <;> norm_cast;
  · constructor <;> simp +decide [ * ]

/-! ### T5: Adjacency is distinct from overlap -/

/-
PROVIDED SOLUTION
Construct a model on `Fin 2` = {0, 1}. Define:
- phen_le: discrete (equality only), i.e., phen_le a b iff a = b.
- meth_le, theory_le, inst_le: discrete.
- adj: adj 0 1 and adj 1 0 (and nothing else). I.e., adj a b iff a ≠ b.

Then adj 0 1 holds.
overlap_phen 0 1 requires ∃ z, phen_le z 0 ∧ phen_le z 1, i.e., ∃ z, z = 0 ∧ z = 1, which is impossible since 0 ≠ 1.

For partial order axioms: trivial since all are equality.
For adj_symm: a ≠ b → b ≠ a. ✓
For adj_irrefl: ¬(a ≠ a). ✓

Use `decide` for Fin 2 goals.
-/
theorem T5_adjacency_distinct_from_overlap :
    ∃ (Entity : Type) (M : TypedMereology Entity) (x y : Entity),
      M.adj x y ∧ ¬ M.overlap_phen x y := by
  fconstructor;
  exact ULift ℕ;
  fconstructor;
  constructor;
  case h.w.adj => exact fun x y => x.down ≠ y.down;
  any_goals tauto;
  all_goals norm_num [ TypedMereology.overlap_phen ];
  exists 0, 1

/-! ### T6: Bundle parthood is componentwise

Subfield parthood under phenomena and methods does NOT entail parthood under theory. -/

/-
PROVIDED SOLUTION
Use Entity = Bool. Let S₁ = ⟨∅, ∅, {true}⟩ and S₂ = ⟨∅, ∅, ∅⟩ (or similar). Then P₁ ⊆ P₂ (both empty), M₁ ⊆ M₂ (both empty), but T₁ ⊄ T₂. Concretely:
- S₁ = ⟨∅, ∅, {true}⟩
- S₂ = ⟨Set.univ, Set.univ, ∅⟩
Then subfield_phen_le holds (∅ ⊆ univ), subfield_meth_le holds (∅ ⊆ univ), but subfield_theory_le fails ({true} ⊄ ∅). Use `Set.not_subset` to show the last part.
-/
theorem T6_bundle_componentwise :
    ∃ (Entity : Type) (S₁ S₂ : TypedMereology.Subfield Entity),
      TypedMereology.subfield_phen_le S₁ S₂ ∧
      TypedMereology.subfield_meth_le S₁ S₂ ∧
      ¬ TypedMereology.subfield_theory_le S₁ S₂ := by
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact Bool;
  exact ⟨ ∅, ∅, { Bool.true } ⟩;
  exact ⟨ Set.univ, Set.univ, ∅ ⟩;
  · exact Set.empty_subset _;
  · exact Set.empty_subset _;
  · exact fun h => by simpa using h ( Set.mem_singleton _ ) ;

/-! ### T7: Adjacency is bidirectional and homeostatic

If two entities are adjacent, there exist lenses under which each contributes to
maintaining the other. We model "contributes to maintaining y under a lens" as
"there exists a common part under that lens" (overlap), capturing the idea that
the entities share structural resources. -/

/-- An enumeration of the four lenses, used in T7. -/
inductive Lens | phen | meth | theory | inst

/-- Overlap under a given lens. -/
def TypedMereology.overlap_lens {Entity : Type*} (M : TypedMereology Entity)
    (l : Lens) (x y : Entity) : Prop :=
  match l with
  | .phen => M.overlap_phen x y
  | .meth => M.overlap_meth x y
  | .theory => M.overlap_theory x y
  | .inst => M.overlap_inst x y

/-
PROVIDED SOLUTION
Use a model where adj is always False (no adjacent pairs). Then the universal statement `∀ x y, M.adj x y → ...` is vacuously true. Construct the model on Unit or PUnit with all four lenses being equality (the discrete/trivial order) and adj := fun _ _ => False. The adj_symm and adj_irrefl axioms are trivially satisfied. The conclusion follows from False.elim.
-/
theorem T7_adjacency_bidirectional_homeostatic :
    ∃ (Entity : Type) (M : TypedMereology Entity),
      (∀ x y, M.adj x y →
        ∃ l₁ l₂ : Lens, M.overlap_lens l₁ x y ∧ M.overlap_lens l₂ y x) := by
  fconstructor;
  exact PUnit;
  refine' ⟨ _, _ ⟩;
  refine' { .. } <;> norm_num;
  any_goals tauto;
  norm_num +zetaDelta at *
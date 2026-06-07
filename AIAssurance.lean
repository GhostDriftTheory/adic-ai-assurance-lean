import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Closed Grothendieck version of AI assurance

This version removes the free evidence category parameter `E`.
The evidence category is the Mathlib Grothendieck construction
`Grothendieck A.toCatFunctor`.
-/

universe uO vO uF vF

namespace AIAssurance

open CategoryTheory

attribute [local simp] CategoryTheory.eqToHom_map

variable {O : Type uO} [Category.{vO} O]

/-- Indexed assurance data over an operational category.

The total evidence category is not a parameter.  It is derived as the
Grothendieck construction of `toCatFunctor`. -/
structure IndexedAssurance (O : Type uO) [Category.{vO} O] where
  Fiber : O → Type uF
  fiberCategory : ∀ X : O, Category.{vF} (Fiber X)
  push :
    ∀ {X Y : O}, (X ⟶ Y) →
      @Functor (Fiber X) (fiberCategory X) (Fiber Y) (fiberCategory Y)
  pull :
    ∀ {X Y : O}, (X ⟶ Y) →
      @Functor (Fiber Y) (fiberCategory Y) (Fiber X) (fiberCategory X)
  adj : ∀ {X Y : O} (f : X ⟶ Y), push f ⊣ pull f
  push_id :
    ∀ X : O,
      push (𝟙 X) = @Functor.id (Fiber X) (fiberCategory X)
  push_comp :
    ∀ {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z),
      push (f ≫ g) =
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber Y) (fiberCategory Y)
          (Fiber Z) (fiberCategory Z)
          (push f) (push g)
  pull_id :
    ∀ X : O,
      pull (𝟙 X) = @Functor.id (Fiber X) (fiberCategory X)
  pull_comp :
    ∀ {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z),
      pull (f ≫ g) =
        @Functor.comp
          (Fiber Z) (fiberCategory Z)
          (Fiber Y) (fiberCategory Y)
          (Fiber X) (fiberCategory X)
          (pull g) (pull f)
  standard : ∀ X : O, Fiber X
  standard_push :
    ∀ {X Y : O} (f : X ⟶ Y),
      @Functor.obj
        (Fiber X) (fiberCategory X)
        (Fiber Y) (fiberCategory Y)
        (push f) (standard X) = standard Y
  beck_chevalley :
    ∀ {X' X Y' Y : O}
      (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y),
      u ≫ f = f' ≫ v →
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber Y) (fiberCategory Y)
          (Fiber Y') (fiberCategory Y')
          (push f) (pull v) =
        @Functor.comp
          (Fiber X) (fiberCategory X)
          (Fiber X') (fiberCategory X')
          (Fiber Y') (fiberCategory Y')
          (pull u) (push f')

namespace IndexedAssurance

variable (A : IndexedAssurance.{uO, vO, uF, vF} O)

attribute [local instance] IndexedAssurance.fiberCategory

/-- The Cat-valued functor whose Grothendieck construction is the evidence category. -/
def toCatFunctor : O ⥤ Cat.{vF, uF} where
  obj X := Cat.of (A.Fiber X)
  map {X Y} f := (A.push f).toCatHom
  map_id X := by
    apply Cat.ext
    exact A.push_id X
  map_comp {X Y Z} f g := by
    apply Cat.ext
    exact A.push_comp f g

/-- The derived total evidence category. -/
abbrev EvidenceCategory (A : IndexedAssurance.{uO, vO, uF, vF} O) :=
  Grothendieck (A.toCatFunctor)

/-- Forget evidence and recover the base operational category. -/
def forget (A : IndexedAssurance.{uO, vO, uF, vF} O) : EvidenceCategory A ⥤ O :=
  Grothendieck.forget A.toCatFunctor

/-- The standard evidence section. -/
def standardSection (A : IndexedAssurance.{uO, vO, uF, vF} O) : O ⥤ EvidenceCategory A where
  obj X := ⟨X, A.standard X⟩
  map {X Y} f :=
    { base := f
      fiber := eqToHom (A.standard_push f) }
  map_id X := by
    refine Grothendieck.ext _ _ (by rfl) ?_
    dsimp [Grothendieck.id]
    simp
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext _ _ (by rfl) ?_
    dsimp [Grothendieck.comp]
    simp [eqToHom_trans]

/-- The standard section forgets to the identity functor on operations. -/
theorem section_eq : A.standardSection ⋙ A.forget = 𝟭 O := by
  rfl

/-- A section of a forgetful functor is faithful. -/
def faithful_of_section
    {E : Type*} [Category E]
    (U : E ⥤ O) (S : O ⥤ E)
    (hsection : S ⋙ U = 𝟭 O) : S.Faithful where
  map_injective {X Y} f g hfg := by
    have hmap : (S ⋙ U).map f = (S ⋙ U).map g := by
      change U.map (S.map f) = U.map (S.map g)
      rw [hfg]
    have hmap_id : (𝟭 O).map f = (𝟭 O).map g := by
      rw [hsection] at hmap
      exact hmap
    simpa using hmap_id

/-- Standard evidence tracing is faithful. -/
theorem section_faithful : A.standardSection.Faithful :=
  faithful_of_section A.forget A.standardSection A.section_eq

/-- Opcartesian lift candidate supplied by the Grothendieck construction. -/
def opcartLift {X Y : O} (f : X ⟶ Y) (a : A.Fiber X) :
    (⟨X, a⟩ : EvidenceCategory A) ⟶
      ⟨Y, @Functor.obj
        (A.Fiber X) (A.fiberCategory X)
        (A.Fiber Y) (A.fiberCategory Y)
        (A.push f) a⟩ :=
  Grothendieck.toTransport (F := A.toCatFunctor) (⟨X, a⟩ : EvidenceCategory A) f

/-- Cartesian lift candidate built from the counit of `push f ⊣ pull f`. -/
def cartLift {X Y : O} (f : X ⟶ Y) (b : A.Fiber Y) :
    (⟨X, @Functor.obj
      (A.Fiber Y) (A.fiberCategory Y)
      (A.Fiber X) (A.fiberCategory X)
      (A.pull f) b⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩ where
  base := f
  fiber := (A.adj f).counit.app b

/-- Strict split law for forward transport. -/
theorem push_opcart_split
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) (a : A.Fiber X) :
    @Functor.obj
      (A.Fiber X) (A.fiberCategory X)
      (A.Fiber Z) (A.fiberCategory Z)
      (A.push (f ≫ g)) a =
    @Functor.obj
      (A.Fiber Y) (A.fiberCategory Y)
      (A.Fiber Z) (A.fiberCategory Z)
      (A.push g)
      (@Functor.obj
        (A.Fiber X) (A.fiberCategory X)
        (A.Fiber Y) (A.fiberCategory Y)
        (A.push f) a) := by
  rw [A.push_comp f g]
  rfl

/-- Fiber-level universal property of the opcartesian lift: a map out of
`push (f ≫ g) a` is uniquely the same as a map out of
`push g (push f a)` after the split identification. -/
theorem opcart_univ
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : A.Fiber X) (c : A.Fiber Z)
    (γ :
      @Functor.obj
        (A.Fiber X) (A.fiberCategory X)
        (A.Fiber Z) (A.fiberCategory Z)
        (A.push (f ≫ g)) a ⟶ c) :
    ∃! (δ :
      @Functor.obj
        (A.Fiber Y) (A.fiberCategory Y)
        (A.Fiber Z) (A.fiberCategory Z)
        (A.push g)
        (@Functor.obj
          (A.Fiber X) (A.fiberCategory X)
          (A.Fiber Y) (A.fiberCategory Y)
          (A.push f) a) ⟶ c),
      δ = eqToHom (A.push_opcart_split f g a).symm ≫ γ := by
  refine ⟨eqToHom (A.push_opcart_split f g a).symm ≫ γ, rfl, ?_⟩
  intro δ hδ
  exact hδ

/-- Strict split law for backward audit pullback. -/
theorem pull_cart_split
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) (b : A.Fiber Z) :
    @Functor.obj
      (A.Fiber Z) (A.fiberCategory Z)
      (A.Fiber X) (A.fiberCategory X)
      (A.pull (f ≫ g)) b =
    @Functor.obj
      (A.Fiber Y) (A.fiberCategory Y)
      (A.Fiber X) (A.fiberCategory X)
      (A.pull f)
      (@Functor.obj
        (A.Fiber Z) (A.fiberCategory Z)
        (A.Fiber Y) (A.fiberCategory Y)
        (A.pull g) b) := by
  rw [A.pull_comp f g]
  rfl

/-- Fiber-level universal property of the cartesian lift, expressed through
the adjunction `push f ⊣ pull f`. -/
theorem cart_univ
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : A.Fiber Y) (c : A.Fiber Z)
    (α :
      @Functor.obj
        (A.Fiber Z) (A.fiberCategory Z)
        (A.Fiber Y) (A.fiberCategory Y)
        (A.push (k ≫ f)) c ⟶ b) :
    ∃! (β :
      @Functor.obj
        (A.Fiber Z) (A.fiberCategory Z)
        (A.Fiber X) (A.fiberCategory X)
        (A.push k) c ⟶
      @Functor.obj
        (A.Fiber Y) (A.fiberCategory Y)
        (A.Fiber X) (A.fiberCategory X)
        (A.pull f) b),
      β =
        (A.adj f).homEquiv
          (@Functor.obj
            (A.Fiber Z) (A.fiberCategory Z)
            (A.Fiber X) (A.fiberCategory X)
            (A.push k) c)
          b
          (eqToHom (A.push_opcart_split k f c).symm ≫ α) := by
  refine ⟨
    (A.adj f).homEquiv
      (@Functor.obj
        (A.Fiber Z) (A.fiberCategory Z)
        (A.Fiber X) (A.fiberCategory X)
        (A.push k) c)
      b
      (eqToHom (A.push_opcart_split k f c).symm ≫ α),
    rfl,
    ?_⟩
  intro β hβ
  exact hβ

/-- Total-category-level opcartesian universal property.

Any evidence morphism `h : ⟨X, a⟩ ⟶ ⟨Z, c⟩` whose base equals `f ≫ g`
factors uniquely through the opcartesian lift
`opcartLift f a : ⟨X, a⟩ ⟶ ⟨Y, push f a⟩`. The unique factoring
morphism has base `g` and fiber component determined by `h.fiber` after
the strict split identification. -/
theorem opcart_factor
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z)
    (a : A.Fiber X) (c : A.Fiber Z)
    (h : (⟨X, a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩)
    (hbase : h.base = f ≫ g) :
    ∃! (δ : (⟨Y,
            @Functor.obj
              (A.Fiber X) (A.fiberCategory X)
              (A.Fiber Y) (A.fiberCategory Y)
              (A.push f) a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩),
        δ.base = g ∧
          A.opcartLift f a ≫ δ = h := by
  cases h with
  | mk hb hf =>
  dsimp at hbase
  subst hb
  let δ₀ :
      (⟨Y,
        @Functor.obj
          (A.Fiber X) (A.fiberCategory X)
          (A.Fiber Y) (A.fiberCategory Y)
          (A.push f) a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩ :=
    { base := g
      fiber := by
        change (A.push g).obj ((A.push f).obj a) ⟶ c
        exact eqToHom (A.push_opcart_split f g a).symm ≫ hf }
  refine ⟨δ₀, ⟨rfl, ?_⟩, ?_⟩
  · refine Grothendieck.ext
      (A.opcartLift f a ≫ δ₀)
      { base := f ≫ g, fiber := hf } (by rfl) ?_
    simp [δ₀, opcartLift, Grothendieck.toTransport]
  · intro δ hδ
    rcases hδ with ⟨hδbase, hδfact⟩
    refine Grothendieck.ext δ δ₀ hδbase ?_
    have hfib := congr_arg_heq
      (fun q : (⟨X, a⟩ : EvidenceCategory A) ⟶ ⟨Z, c⟩ => q.fiber)
      hδfact
    simp [opcartLift, Grothendieck.toTransport] at hfib
    exact eq_of_heq <|
      (eqToHom_comp_heq δ.fiber (by rw [hδbase])).trans <|
        hfib.trans (eqToHom_comp_heq hf (A.push_opcart_split f g a).symm).symm

/-- Total-category-level cartesian universal property.

Any evidence morphism `h : ⟨Z, c⟩ ⟶ ⟨Y, b⟩` whose base equals `k ≫ f`
factors uniquely through the cartesian lift
`cartLift f b : ⟨X, pull f b⟩ ⟶ ⟨Y, b⟩`. The unique factoring morphism
has base `k` and fiber component determined by the adjunction hom-equivalence
applied to `h.fiber`. -/
theorem cart_factor
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : A.Fiber Y) (c : A.Fiber Z)
    (h : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩)
    (hbase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : EvidenceCategory A) ⟶
            ⟨X,
            @Functor.obj
              (A.Fiber Y) (A.fiberCategory Y)
              (A.Fiber X) (A.fiberCategory X)
              (A.pull f) b⟩),
        δ.base = k ∧
          δ ≫ A.cartLift f b = h := by
  cases h with
  | mk hb hf =>
  dsimp at hbase
  subst hb
  set ev_wit :=
    (A.adj f).homEquiv
      (@Functor.obj
        (A.Fiber Z) (A.fiberCategory Z)
        (A.Fiber X) (A.fiberCategory X)
        (A.push k) c)
      b
      (eqToHom (A.push_opcart_split k f c).symm ≫ hf)
    with ev_wit_def
  let δ₀ :
      (⟨Z, c⟩ : EvidenceCategory A) ⟶
        ⟨X,
        @Functor.obj
          (A.Fiber Y) (A.fiberCategory Y)
          (A.Fiber X) (A.fiberCategory X)
          (A.pull f) b⟩ :=
    { base := k
      fiber := by
        change (A.push k).obj c ⟶ (A.pull f).obj b
        exact ev_wit }
  refine ⟨δ₀, ⟨rfl, ?_⟩, ?_⟩
  · refine Grothendieck.ext
      (δ₀ ≫ A.cartLift f b)
      { base := k ≫ f, fiber := hf } (by rfl) ?_
    dsimp [δ₀, cartLift, Grothendieck.comp]
    rw [ev_wit_def, ← Adjunction.homEquiv_counit]
    change 𝟙 ((A.push (k ≫ f)).obj c) ≫
        eqToHom (A.push_opcart_split k f c) ≫
          ((A.adj f).homEquiv ((A.push k).obj c) b).symm
            (((A.adj f).homEquiv ((A.push k).obj c) b)
              (eqToHom (A.push_opcart_split k f c).symm ≫ hf)) =
      hf
    rw [Equiv.symm_apply_apply]
    simp
  · intro δ hδ
    rcases hδ with ⟨hδbase, hδfact⟩
    refine Grothendieck.ext δ δ₀ hδbase ?_
    have hfib := congr_arg_heq
      (fun q : (⟨Z, c⟩ : EvidenceCategory A) ⟶ ⟨Y, b⟩ => q.fiber)
      hδfact
    simp [cartLift] at hfib
    apply (((A.adj f).homEquiv ((A.push k).obj c) b).symm).injective
    dsimp [δ₀]
    rw [ev_wit_def]
    rw [Equiv.symm_apply_apply]
    rw [Adjunction.homEquiv_counit]
    rw [Functor.map_comp, eqToHom_map]
    rw [Category.assoc]
    exact eq_of_heq <|
      (eqToHom_comp_heq
        ((A.push f).map δ.fiber ≫ (A.adj f).counit.app b)
        (by rw [hδbase]; rfl)).trans <|
        hfib.trans (eqToHom_comp_heq hf (A.push_opcart_split k f c).symm).symm

/-- Governance quotient induced by a functor. -/
abbrev GovernanceQuotient {D : Type*} [Category D] (F : EvidenceCategory A ⥤ D) : Type _ :=
  CategoryTheory.Quotient F.homRel

/-- Quotient functor identifying exactly arrows with the same meaning. -/
def governanceQuotientFunctor {D : Type*} [Category D] (F : EvidenceCategory A ⥤ D) :
    EvidenceCategory A ⥤ GovernanceQuotient A F :=
  CategoryTheory.Quotient.functor F.homRel

/-- Governance identification is a theorem by quotient construction. -/
theorem governance_identifies_by_quotient
    {D : Type*} [Category D] (F : EvidenceCategory A ⥤ D)
    {X Y : EvidenceCategory A} (f g : X ⟶ Y) :
    F.map f = F.map g ↔
      (governanceQuotientFunctor A F).map f =
        (governanceQuotientFunctor A F).map g := by
  constructor
  · intro h
    exact CategoryTheory.Quotient.sound (r := F.homRel) h
  · intro h
    exact (CategoryTheory.Quotient.functor_map_eq_iff (F.homRel) f g).1 h

/-- Yoneda reflects isomorphisms. -/
theorem yoneda_reflects_iso {X Y : EvidenceCategory A} (f : X ⟶ Y)
    (h : IsIso ((yoneda (C := EvidenceCategory A)).map f)) : IsIso f := by
  haveI : IsIso ((yoneda (C := EvidenceCategory A)).map f) := h
  exact isIso_of_reflects_iso f (yoneda (C := EvidenceCategory A))

end IndexedAssurance

namespace CollapseCounterexample

/-!
## Collapse counterexample

This finite counterexample is independent from the indexed construction above:
it shows that forgetting the trace layer can identify distinct
governance-relevant evidence morphisms.
-/

/-- Evidence objects: a single object carrying two distinct evidence traces. -/
inductive EObj : Type
  | pt : EObj

/-- Evidence morphisms: two distinct traces over the same visible operation. -/
inductive EHom : EObj → EObj → Type
  | traceA : EHom EObj.pt EObj.pt
  | traceB : EHom EObj.pt EObj.pt

instance : Category EObj where
  Hom := EHom
  id := fun X =>
    match X with
    | .pt => .traceA
  comp := fun {X Y Z} f g =>
    match f, g with
    | .traceA, .traceA => .traceA
    | .traceA, .traceB => .traceB
    | .traceB, .traceA => .traceB
    | .traceB, .traceB => .traceB
  id_comp := by
    intro X Y f
    cases f <;> rfl
  comp_id := by
    intro X Y f
    cases f <;> rfl
  assoc := by
    intro X Y Z W f g h
    cases f <;> cases g <;> cases h <;> rfl

theorem traceA_ne_traceB : EHom.traceA ≠ EHom.traceB := by
  intro h
  cases h

/-- Operational objects: a single observable state. -/
inductive OObj : Type
  | pt : OObj

/-- Operational morphisms: a single visible operation. -/
inductive OHom : OObj → OObj → Type
  | op : OHom OObj.pt OObj.pt

instance : Category OObj where
  Hom := OHom
  id := fun X =>
    match X with
    | .pt => .op
  comp := fun {X Y Z} f g =>
    match f, g with
    | .op, .op => .op
  id_comp := by
    intro X Y f
    cases f <;> rfl
  comp_id := by
    intro X Y f
    cases f <;> rfl
  assoc := by
    intro X Y Z W f g h
    cases f <;> cases g <;> cases h <;> rfl

instance OHom_subsingleton {X Y : OObj} : Subsingleton (OHom X Y) where
  elim f g := by
    cases f <;> cases g <;> rfl

/-- Forgetful operational view: both evidence traces become the same operation. -/
def U : EObj ⥤ OObj where
  obj := fun X =>
    match X with
    | .pt => .pt
  map := fun {X Y} f =>
    match f with
    | .traceA => OHom.op
    | .traceB => OHom.op
  map_id := fun X =>
    match X with
    | .pt => rfl
  map_comp := fun f g =>
    match f, g with
    | .traceA, .traceA => rfl
    | .traceA, .traceB => rfl
    | .traceB, .traceA => rfl
    | .traceB, .traceB => rfl

theorem trace_distinction_collapses :
    EHom.traceA ≠ EHom.traceB ∧
      U.map EHom.traceA = U.map EHom.traceB := by
  exact ⟨traceA_ne_traceB, rfl⟩

theorem U_not_faithful : ¬ U.Faithful := by
  intro hF
  have hEq : EHom.traceA = EHom.traceB := hF.map_injective (by rfl)
  exact traceA_ne_traceB hEq

/-- Finite counterexample: operational sameness does not imply governance
sameness.

Two morphisms representing distinct judgment grounds or responsibility paths
can map to the same visible operation under a forgetful functor. Therefore a
forgetful functor need not be faithful, and governance-relevant distinctions
can be permanently lost.

Paper interpretation: if AI governance requires those distinctions to remain
inspectable after composition, a faithful trace/evidence layer is structurally
required. This theorem establishes the counterexample component of the
necessity direction. -/
theorem forgetting_trace_layer_can_collapse_distinctions :
    ∃ (E : Type) (_ : Category.{0} E)
      (O : Type) (_ : Category.{0} O)
      (U : E ⥤ O),
      ¬ U.Faithful := by
  exact ⟨EObj, inferInstance, OObj, inferInstance, U, U_not_faithful⟩

end CollapseCounterexample

end AIAssurance

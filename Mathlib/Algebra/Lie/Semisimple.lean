/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Solvable
import Mathlib.Order.Atoms

#align_import algebra.lie.semisimple from "leanprover-community/mathlib"@"356447fe00e75e54777321045cdff7c9ea212e60"

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we define simple and semisimple Lie algebras
and prove some basic related results.

## Main definitions

  * `LieModule.IsIrreducible`
  * `LieAlgebra.IsSimple`
  * `LieAlgebra.HasTrivialRadical`
  * `LieAlgebra.IsSemisimple`
  * `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
  * `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
  * `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/


universe u v w w₁ w₂

section Irreducible

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- A nontrivial Lie module is *irreducible* if its only Lie submodules are `⊥` and `⊤`. -/
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)
#align lie_module.is_irreducible LieModule.IsIrreducible

lemma LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0

end Irreducible

namespace LieAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L
#align lie_algebra.is_simple LieAlgebra.IsSimple

instance [IsSimple R L] : LieModule.IsIrreducible R L L := by
  have : Nontrivial (LieIdeal R L) := by
    constructor
    by_contra! H
    apply IsSimple.non_abelian R (L := L)
    constructor
    intro x y
    rw [← LieSubmodule.mem_bot (R := R) (L := L), H ⊥ ⊤]
    trivial
  constructor
  apply IsSimple.eq_bot_or_eq_top

/--
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algebras.
-/
class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥
#align lie_algebra.is_semisimple LieAlgebra.HasTrivialRadical

export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot

/--
A *semisimple* Lie algebra is one that is a direct sum of simple Lie algebras.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
class IsSemisimple : Prop where
  sSup_isAtom_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  setIndependent_isAtom : CompleteLattice.SetIndependent {I : LieIdeal R L | IsAtom I}
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

lemma isSimple_of_isAtom [IsSemisimple R L] (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
    non_abelian := IsSemisimple.non_abelian_of_isAtom I hI
    eq_bot_or_eq_top := by
      intro J
      let J' : LieIdeal R L :=
      { __ := J.toSubmodule.map I.incl.toLinearMap
        lie_mem := by
          rintro x _ ⟨y, hy, rfl⟩
          dsimp
          have hx : x ∈ I ⊔ sSup ({I' : LieIdeal R L | IsAtom I'} \ {I}) := by
            nth_rewrite 1 [← sSup_singleton (a := I)]
            rw [← sSup_union, Set.union_diff_self, Set.union_eq_self_of_subset_left,
              IsSemisimple.sSup_isAtom_eq_top]
            · apply LieSubmodule.mem_top
            · simp only [Set.singleton_subset_iff, Set.mem_setOf_eq, hI]
          rw [LieSubmodule.mem_sup] at hx
          obtain ⟨a, ha, b, hb, rfl⟩ := hx
          simp only [add_lie, AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
            Submodule.mem_toAddSubmonoid]
          apply add_mem
          · simp only [Submodule.mem_map, LieSubmodule.mem_coeSubmodule, Submodule.coeSubtype,
              Subtype.exists, exists_and_right, exists_eq_right, ha, lie_mem_left, exists_true_left]
            exact lie_mem_right R I J ⟨a, ha⟩ y hy
          · suffices ⁅b, y.val⁆ = 0 by simp only [this, zero_mem]
            rw [← LieSubmodule.mem_bot (R := R) (L := L),
                ← (IsSemisimple.setIndependent_isAtom hI).eq_bot]
            exact ⟨lie_mem_right R L I b y y.2, lie_mem_left _ _ _ _ _ hb⟩ }
      rw [or_iff_not_imp_right]
      intro hJ
      suffices J' = ⊥ by
        have aux : (fun J : LieIdeal R I ↦ J.toSubmodule.map I.incl.toLinearMap).Injective := by
          intro J₁ J₂ h
          ext x
          rw [SetLike.ext_iff] at h
          specialize h x
          simpa only [LieIdeal.incl_coe, LieIdeal.coe_to_lieSubalgebra_to_submodule,
            Submodule.mem_map, LieSubmodule.mem_coeSubmodule, Submodule.coeSubtype,
            SetLike.coe_eq_coe, exists_eq_right] using h
        apply aux
        simpa [J'] using this
      apply hI.2
      rw [lt_iff_le_and_ne]
      constructor
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      contrapose! hJ
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      rw [← hJ] at hx
      rcases hx with ⟨y, hy, rfl⟩
      exact hy

-- TODO: show that the atomic ideals of a semisimple Lie algebra are simple

variable {R L} in
theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable R I] : I = ⊥ :=
  sSup_eq_bot.mp radical_eq_bot _ hI

variable {R L} in
theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥) :
    HasTrivialRadical R L :=
  ⟨sSup_eq_bot.mpr h⟩

theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable R I → I = ⊥ :=
  ⟨@HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, hasTrivialRadical_of_no_solvable_ideals⟩
#align lie_algebra.is_semisimple_iff_no_solvable_ideals LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals

theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · apply h₁; exact LieAlgebra.ofAbelianIsSolvable R I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]; apply h₁
    exact abelian_derivedAbelianOfIdeal I
#align lie_algebra.is_semisimple_iff_no_abelian_ideals LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals

@[simp]
theorem center_eq_bot_of_hasTrivialRadical [h : HasTrivialRadical R L] : center R L = ⊥ := by
  rw [hasTrivialRadical_iff_no_abelian_ideals] at h; apply h; infer_instance
#align lie_algebra.center_eq_bot_of_semisimple LieAlgebra.center_eq_bot_of_hasTrivialRadical

variable {R L} in
lemma eq_top_of_isAtom [IsSimple R L] (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ :=
  (IsSimple.eq_bot_or_eq_top I).resolve_left hI.1

lemma isAtom_top [IsSimple R L] : IsAtom (⊤ : LieIdeal R L) := by
  constructor
  · intro h
    apply IsSimple.non_abelian R (L := L)
    constructor
    intro x y
    rw [← LieSubmodule.mem_bot (R := R) (L := L), ← h]
    trivial
  · intro I hI
    have := IsSimple.eq_bot_or_eq_top I
    contrapose! this
    exact ⟨this, hI.ne⟩

variable {R L} in
lemma isAtom_iff_eq_top [IsSimple R L] (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ :=
  ⟨eq_top_of_isAtom I, fun h ↦ h ▸ isAtom_top R L⟩

-- move this to `Mathlib.Order.SupIndep`
lemma _root_.CompleteLattice.setIndependent_singleton {α : Type w} [CompleteLattice α] (a : α) :
    CompleteLattice.SetIndependent ({a} : Set α) := by
  intro i hi
  simp_all

/-- A simple Lie algebra is semisimple. -/
instance (priority := 100) isSemisimple_of_isSimple [h : IsSimple R L] :
    IsSemisimple R L := by
  have aux : {I : LieIdeal R L | IsAtom I} = {⊤} := by
    ext I
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, isAtom_iff_eq_top]
  constructor
  · simp [aux]
  · simpa [aux] using _root_.CompleteLattice.setIndependent_singleton _
  · intro I hI₁ hI₂
    rw [isAtom_iff_eq_top] at hI₁
    subst I
    obtain @⟨-, h₂⟩ := id h
    rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂
    contradiction

-- move this
lemma _root_.Submodule.exists_sum_of_mem_sSup {R : Type u} {M : Type v} [Ring R] [AddCommGroup M]
    [Module R M] (S : Set (Submodule R M)) (x : M) (hx : x ∈ sSup S) :
    ∃ (T : Finset (Submodule R M)) (_ : ↑T ⊆ S) (f : Submodule R M → M),
      T.sum f = x ∧ ∀ N ∈ T, f N ∈ N := by
  rw [← Submodule.span_singleton_le_iff_mem] at hx
  obtain ⟨T, h₁, h₂⟩ := Submodule.singleton_span_isCompactElement _ _ hx
  rw [Submodule.span_singleton_le_iff_mem] at h₂
  use T, h₁
  clear h₁ hx S
  revert x
  classical
  refine T.induction_on (by simp) ?_
  intro N s hNs IH x hx
  rw [Finset.sup_insert, Submodule.mem_sup] at hx
  obtain ⟨n, hn : n ∈ N, x, hx, rfl⟩ := hx
  obtain ⟨f, rfl, hf⟩ := IH x hx
  use Function.update f N n
  simp only [hNs, not_false_eq_true, Finset.sum_insert, Function.update_same, add_right_inj,
    Finset.mem_insert, forall_eq_or_imp, hn, true_and]
  constructor
  · apply Finset.sum_congr rfl
    intro M hM
    rw [Function.update_noteq]
    rintro rfl
    contradiction
  · intro M hM
    rw [Function.update_noteq]
    · exact hf M hM
    rintro rfl
    contradiction

-- instance (priority := 100) [h : IsSemisimple R L] :
--     ComplementedLattice (LieIdeal R L) where
--       exists_isCompl := _

-- instance (priority := 100) [h : IsSemisimple R L] :
--     BooleanAlgebra (LieIdeal R L) where
--   __ := (inferInstance : CompleteLattice (LieIdeal R L))
--   le_sup_inf := _
--   compl := _
--   inf_compl_le_bot := _
--   top_le_sup_compl := _
--   sdiff := _
--   himp := _
--   sdiff_eq := _
--   himp_eq := _

lemma exists_unique_sum [IsSemisimple R L] (x : L) :
    ∃! a : {I : LieIdeal R L // IsAtom I} →₀ L, a.sum (fun _ ↦ id) = x ∧ ∀ I, a I ∈ I.1 := by
  have hx : x ∈ (⊤ : LieIdeal R L) := trivial
  rw [← IsSemisimple.sSup_isAtom_eq_top] at hx
  obtain ⟨T, hT, f, rfl, hf⟩ := Submodule.exists_sum_of_mem_sSup _ _ hx
  classical
  let a : {I : LieIdeal R L // IsAtom I} →₀ L :=
  { toFun := fun I ↦ if (I : Submodule R L) ∈ T then f I else 0
    support := (T.preimage ?coe ?inj).filter fun I ↦ f I ≠ 0
    mem_support_toFun := ?cond }
  case coe => exact fun I ↦ I
  case cond => intro I; simp
  case inj =>
   intro I hI J hJ hIJ
   ext
   rw [SetLike.ext_iff] at hIJ
   apply hIJ
  refine ⟨a, ?_, ?_⟩
  · sorry
  · intro b hb
    ext ⟨I, hI⟩
    sorry

lemma _root_.LieIdeal.sSup_inter [IsSemisimple R L] (S T : Set (LieIdeal R L))
    (hS : S ⊆ {I | IsAtom I}) (hT : T ⊆ {I | IsAtom I}) :
    sSup (S ∩ T) = (sSup S) ⊓ (sSup T) := by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup (Set.inter_subset_left S T)
    · apply sSup_le_sSup (Set.inter_subset_right S T)
  rintro x ⟨hxS, hxT⟩
  sorry

lemma _root_.LieIdeal.sSup_atoms_le_eq [IsSemisimple R L] (J : LieIdeal R L) :
    sSup {I | IsAtom I ∧ I ≤ J} = J := by
  apply le_antisymm
  · apply sSup_le
    rintro I ⟨hI, hIJ⟩
    exact hIJ
  -- intro x hx
  sorry

instance (priority := 100) [IsSemisimple R L] : DistribLattice (LieIdeal R L) where
  __ := (inferInstance : CompleteLattice (LieIdeal R L))
  le_sup_inf I₁ I₂ I₃ := by
    apply le_of_eq
    rw [← I₁.sSup_atoms_le_eq, ← I₂.sSup_atoms_le_eq, ← I₃.sSup_atoms_le_eq,
        ← sSup_union, ← sSup_union, ← LieIdeal.sSup_inter, ← LieIdeal.sSup_inter, ← sSup_union]
    · congr 1
      ext
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      tauto
    all_goals simp (config := { contextual := true })

instance (priority := 100) [IsSemisimple R L] :
    ComplementedLattice (LieIdeal R L) where
  exists_isCompl J := by
    use sSup {I | IsAtom I ∧ ¬ I ≤ J}
    nth_rewrite 1 [← J.sSup_atoms_le_eq]
    constructor
    · rw [disjoint_iff, ← LieIdeal.sSup_inter]
      · simp only [sSup_eq_bot, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
        intro I _ h₁ _ h₂
        contradiction
      · simp only [Set.setOf_subset_setOf, and_imp]
        intro I hI _
        exact hI
      · simp only [Set.setOf_subset_setOf, and_imp]
        intro I hI _
        exact hI
    · rw [codisjoint_iff, ← sSup_union]
      · suffices {I | IsAtom I ∧ I ≤ J} ∪ {I | IsAtom I ∧ ¬I ≤ J} = {I | IsAtom I} by
          rw [this, IsSemisimple.sSup_isAtom_eq_top]
        ext
        simp only [Set.mem_union, Set.mem_setOf_eq]
        tauto

/-- A semisimple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSemisimple [IsSemisimple R L] :
    HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (eq_bot_or_exists_atom_le I).resolve_right
  rintro ⟨J, hJ, hJ'⟩
  apply IsSemisimple.non_abelian_of_isAtom J hJ
  constructor
  intro x y
  ext
  simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, ZeroMemClass.coe_zero]
  have : (⁅(⟨x, hJ' x.2⟩ : I), ⟨y, hJ' y.2⟩⁆ : I) = 0 := trivial_lie_zero _ _ _ _
  apply_fun Subtype.val at this
  exact this

/-- A simple Lie algebra has trivial radical. -/
instance (priority := 100) hasTrivialRadical_of_isSimple [IsSimple R L] :
    HasTrivialRadical R L := inferInstance
#align lie_algebra.is_semisimple_of_is_simple LieAlgebra.hasTrivialRadical_of_isSimple

/-- An abelian Lie algebra with trivial radical is trivial. -/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, center_eq_bot_of_hasTrivialRadical] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)
#align lie_algebra.subsingleton_of_semisimple_lie_abelian LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian

theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.radical_eq_bot]; infer_instance
#align lie_algebra.abelian_radical_of_semisimple LieAlgebra.abelian_radical_of_hasTrivialRadical

/-- The two properties shown to be equivalent here are possible definitions for a Lie algebra
to be reductive.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable R I → IsLieAbelian I := by
  constructor
  · rintro h₁ I h₂
    rw [LieIdeal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).isLieAbelian h₁
  · intro h; apply h; infer_instance
#align lie_algebra.abelian_radical_iff_solvable_is_abelian LieAlgebra.abelian_radical_iff_solvable_is_abelian

theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp
#align lie_algebra.ad_ker_eq_bot_of_semisimple LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical

end LieAlgebra

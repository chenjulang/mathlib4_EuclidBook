/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Order.Bounded
import Mathlib.SetTheory.Cardinal.PartENat
import Mathlib.SetTheory.Ordinal.Principal
import Mathlib.Tactic.Linarith

/-!
# Cardinals and ordinals

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `Cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `Cardinal.aleph/idx`.
  `aleph' n = n`, `aleph' ω = ℵ₀`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `Cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on. The notation `ω_` combines the latter with `Cardinal.ord`,
  giving an enumeration of (infinite) initial ordinals.
  Thus `ω_ 0 = ω` and `ω₁ = ω_ 1` is the first uncountable ordinal.
* The function `Cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Main Statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `List α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

assert_not_exists Module
assert_not_exists Finsupp

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

section UsingOrdinals

theorem ord_isLimit {c} (co : ℵ₀ ≤ c) : (ord c).IsLimit := by
  refine ⟨fun h => aleph0_ne_zero ?_, fun a => lt_imp_lt_of_le_imp_le fun h => ?_⟩
  · rw [← Ordinal.le_zero, ord_le] at h
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h
  · rw [ord_le] at h ⊢
    rwa [← @add_one_of_aleph0_le (card a), ← card_succ]
    rw [← ord_le, ← le_succ_of_isLimit, ord_le]
    · exact co.trans h
    · rw [ord_aleph0]
      exact omega_isLimit

theorem noMaxOrder {c} (h : ℵ₀ ≤ c) : NoMaxOrder c.ord.toType :=
  toType_noMax_of_succ_lt (ord_isLimit h).2

/-! ### Aleph cardinals -/

section aleph

/-- The `aleph'` function gives the cardinals listed by their ordinal index. `aleph' n = n`,
`aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.

For the more common aleph function skipping over finite cardinals, see `Cardinal.aleph`. -/
def aleph' : Ordinal.{u} ≃o Cardinal.{u} := by
  let f := RelEmbedding.collapse Cardinal.ord.orderEmbedding.ltEmbedding.{u}
  refine (OrderIso.ofRelIsoLT <| RelIso.ofSurjective f ?_).symm
  apply f.eq_or_principal.resolve_right
  rintro ⟨o, e⟩
  have : ∀ c, f c < o := fun c => (e _).2 ⟨_, rfl⟩
  refine Ordinal.inductionOn o ?_ this
  intro α r _ h
  let s := ⨆ a, invFun f (Ordinal.typein r a)
  apply (lt_succ s).not_le
  have I : Injective f := f.toEmbedding.injective
  simpa only [typein_enum, leftInverse_invFun I (succ s)] using
    le_ciSup
      (Cardinal.bddAbove_range.{u, u} fun a : α => invFun f (Ordinal.typein r a))
      (Ordinal.enum r ⟨_, h (succ s)⟩)

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `alephIdx`.
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ℵ₀ = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `alephIdx`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  aleph'.symm.toRelIsoLT

/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `alephIdx n = n`, `alephIdx ω = ω`,
  `alephIdx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `AlephIdx.rel_iso`. -/
@[deprecated aleph' (since := "2024-08-28")]
def alephIdx : Cardinal → Ordinal :=
  aleph'.symm

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx.initialSeg_coe : (alephIdx.initialSeg : Cardinal → Ordinal) = alephIdx :=
  rfl

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx_lt {a b} : alephIdx a < alephIdx b ↔ a < b :=
  alephIdx.initialSeg.toRelEmbedding.map_rel_iff

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx_le {a b} : alephIdx a ≤ alephIdx b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, alephIdx_lt]

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx.init {a b} : b < alephIdx a → ∃ c, alephIdx c = b :=
  alephIdx.initialSeg.init

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx :=
  rfl

@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id]
  exact Quotient.sound ⟨aleph'.symm.toRelIsoLT⟩

@[simp]
theorem mk_cardinal : #Cardinal = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal

/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
@[deprecated aleph' (since := "2024-08-28")]
def Aleph'.relIso :=
  aleph'

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl

theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  aleph'.lt_iff_lt

theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  aleph'.le_iff_le

theorem aleph'_max (o₁ o₂ : Ordinal) : aleph' (max o₁ o₂) = max (aleph' o₁) (aleph' o₂) :=
  aleph'.monotone.map_max

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c

set_option linter.deprecated false in
@[deprecated (since := "2024-08-28")]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o

@[simp]
theorem aleph'_zero : aleph' 0 = 0 :=
  aleph'.map_bot

@[simp]
theorem aleph'_succ (o : Ordinal) : aleph' (succ o) = succ (aleph' o) :=
  aleph'.map_succ o

@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
  | 0 => aleph'_zero
  | n + 1 => show aleph' (succ n) = n.succ by rw [aleph'_succ, aleph'_nat n, nat_succ]

theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
  ⟨fun h o' h' => (aleph'_le.2 <| h'.le).trans h, fun h => by
    rw [← aleph'.apply_symm_apply c, aleph'_le, limit_le l]
    intro x h'
    rw [← aleph'_le, aleph'.apply_symm_apply]
    exact h _ h'⟩

theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a := by
  refine le_antisymm ?_ (ciSup_le' fun i => aleph'_le.2 (le_of_lt i.2))
  rw [aleph'_le_of_limit ho]
  exact fun a ha => le_ciSup (bddAbove_of_small _) (⟨a, ha⟩ : Iio o)

@[simp]
theorem aleph'_omega : aleph' ω = ℵ₀ :=
  eq_of_forall_ge_iff fun c => by
    simp only [aleph'_le_of_limit omega_isLimit, lt_omega, exists_imp, aleph0_le]
    exact forall_swap.trans (forall_congr' fun n => by simp only [forall_eq, aleph'_nat])

set_option linter.deprecated false in
/-- `aleph'` and `aleph_idx` form an equivalence between `Ordinal` and `Cardinal` -/
@[deprecated aleph' (since := "2024-08-28")]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩

@[simp]
theorem lift_aleph' (o : Ordinal.{u}) : lift.{v} (aleph' o) = aleph' (o.lift.{v}) := by
  change (InitialSeg.ofIso aleph').trans lift o =
      Ordinal.lift.initialSeg.trans (InitialSeg.ofIso aleph') o
  congr!
  subsingleton

/-- The `aleph` function gives the infinite cardinals listed by their ordinal index. `aleph 0 = ℵ₀`,
`aleph 1 = succ ℵ₀` is the first uncountable cardinal, and so on.

For a version including finite cardinals, see `Cardinal.aleph'`. -/
def aleph : Ordinal ↪o Cardinal :=
  OrderEmbedding.ofMapLEIff
    (fun o => aleph' (ω + o)) fun _ _=> aleph'_le.trans (add_le_add_iff_left ω)

theorem aleph_eq_aleph' (o : Ordinal) : aleph o = aleph' (ω + o) :=
  rfl

theorem aleph_lt {o₁ o₂ : Ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph.lt_iff_lt

theorem aleph_le {o₁ o₂ : Ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  aleph.le_iff_le

theorem aleph_max (o₁ o₂ : Ordinal) : aleph (max o₁ o₂) = max (aleph o₁) (aleph o₂) :=
  aleph.monotone.map_max

@[deprecated aleph_max (since := "2024-08-28")]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) :=
  (aleph_max o₁ o₂).symm

@[simp]
theorem aleph_succ (o : Ordinal) : aleph (succ o) = succ (aleph o) := by
  rw [aleph_eq_aleph', add_succ, aleph'_succ, aleph_eq_aleph']

@[simp]
theorem aleph_zero : aleph 0 = ℵ₀ := by rw [aleph_eq_aleph', add_zero, aleph'_omega]

theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : aleph o = ⨆ a : Iio o, aleph a := by
  apply le_antisymm _ (ciSup_le' _)
  · rw [aleph_eq_aleph', aleph'_limit (ho.add _)]
    refine ciSup_mono' (bddAbove_of_small _) ?_
    rintro ⟨i, hi⟩
    cases' lt_or_le i ω with h h
    · rcases lt_omega.1 h with ⟨n, rfl⟩
      use ⟨0, ho.pos⟩
      simpa using (nat_lt_aleph0 n).le
    · exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, aleph'_le.2 (le_add_sub _ _)⟩
  · exact fun i => aleph_le.2 (le_of_lt i.2)

@[simp]
theorem lift_aleph (o : Ordinal.{u}) : lift.{v} (aleph o) = aleph (Ordinal.lift.{v} o) := by
  rw [aleph, aleph, lift_aleph', Ordinal.lift_add, lift_omega]

theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by rw [← aleph'_omega, aleph'_le]

theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ aleph o := by
  rw [aleph_eq_aleph', aleph0_le_aleph']
  apply Ordinal.le_add_right

theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by rwa [← aleph'_zero, aleph'_lt]

theorem aleph_pos (o : Ordinal) : 0 < aleph o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)

@[simp]
theorem aleph_toNat (o : Ordinal) : toNat (aleph o) = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o

@[simp]
theorem aleph_toPartENat (o : Ordinal) : toPartENat (aleph o) = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o

instance nonempty_toType_aleph (o : Ordinal) : Nonempty (aleph o).ord.toType := by
  rw [toType_nonempty_iff_ne_zero, ← ord_zero]
  exact fun h => (ord_injective h).not_gt (aleph_pos o)

theorem ord_aleph_isLimit (o : Ordinal) : (aleph o).ord.IsLimit :=
  ord_isLimit <| aleph0_le_aleph _

instance (o : Ordinal) : NoMaxOrder (aleph o).ord.toType :=
  toType_noMax_of_succ_lt (ord_aleph_isLimit o).2

theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
    ⟨aleph'.symm c - ω, by
      rw [aleph_eq_aleph', Ordinal.add_sub_cancel_of_le, aleph'.apply_symm_apply]
      rwa [← aleph0_le_aleph', aleph'.apply_symm_apply]⟩,
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩

theorem aleph'_isNormal : IsNormal (ord ∘ aleph') :=
  ⟨fun o => ord_lt_ord.2 <| aleph'_lt.2 <| lt_succ o, fun o l a => by
    simp [ord_le, aleph'_le_of_limit l]⟩

theorem aleph_isNormal : IsNormal (ord ∘ aleph) :=
  aleph'_isNormal.trans <| add_isNormal ω

theorem succ_aleph0 : succ ℵ₀ = aleph 1 := by rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]

theorem aleph0_lt_aleph_one : ℵ₀ < aleph 1 := by
  rw [← succ_aleph0]
  apply lt_succ

theorem countable_iff_lt_aleph_one {α : Type*} (s : Set α) : s.Countable ↔ #s < aleph 1 := by
  rw [← succ_aleph0, lt_succ_iff, le_aleph0_iff_set_countable]

/-- Ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩

theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
  ⟨aleph'.symm o.card, by simpa using ho⟩

/-- `ord ∘ aleph'` enumerates the ordinals that are cardinals. -/
theorem ord_aleph'_eq_enum_card : ord ∘ aleph' = enumOrd { b : Ordinal | b.card.ord = b } := by
  rw [← eq_enumOrd _ ord_card_unbounded, range_eq_iff]
  exact
    ⟨aleph'_isNormal.strictMono,
      ⟨fun a => by
        dsimp
        rw [card_ord], fun b hb => eq_aleph'_of_eq_card_ord hb⟩⟩

/-- Infinite ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ ω ≤ b } :=
  (unbounded_lt_inter_le ω).2 ord_card_unbounded

theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
    ∃ a, (aleph a).ord = o := by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  use a - ω
  rwa [aleph_eq_aleph', Ordinal.add_sub_cancel_of_le]
  rwa [← aleph0_le_aleph', ← ord_le_ord, ha, ord_aleph0]

/-- `ord ∘ aleph` enumerates the infinite ordinals that are cardinals. -/
theorem ord_aleph_eq_enum_card :
    ord ∘ aleph = enumOrd { b : Ordinal | b.card.ord = b ∧ ω ≤ b } := by
  rw [← eq_enumOrd _ ord_card_unbounded']
  use aleph_isNormal.strictMono
  rw [range_eq_iff]
  refine ⟨fun a => ⟨?_, ?_⟩, fun b hb => eq_aleph_of_eq_card_ord hb.1 hb.2⟩
  · rw [Function.comp_apply, card_ord]
  · rw [← ord_aleph0, Function.comp_apply, ord_le_ord]
    exact aleph0_le_aleph _

@[simp]
theorem aleph1_le_lift {c : Cardinal.{u}} : aleph 1 ≤ lift.{v} c ↔ aleph 1 ≤ c := by
  rw [← Ordinal.lift_one.{u, v}, ← lift_aleph, lift_le]

@[simp]
theorem lift_le_aleph1 {c : Cardinal.{u}} : lift.{v} c ≤ aleph 1 ↔ c ≤ aleph 1 := by
  rw [← Ordinal.lift_one.{u, v}, ← lift_aleph, lift_le]

@[simp]
theorem aleph1_lt_lift {c : Cardinal.{u}} : aleph 1 < lift.{v} c ↔ aleph 1 < c := by
  rw [← Ordinal.lift_one.{u, v}, ← lift_aleph, lift_lt]

@[simp]
theorem lift_lt_aleph1 {c : Cardinal.{u}} : lift.{v} c < aleph 1 ↔ c < aleph 1 := by
  rw [← Ordinal.lift_one.{u, v}, ← lift_aleph, lift_lt]

end aleph

/-! ### Beth cardinals -/
section beth

/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ (beth o)`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o aleph0 (fun _ x => (2 : Cardinal) ^ x) fun a _ IH => ⨆ b : Iio a, IH b.1 b.2

@[simp]
theorem beth_zero : beth 0 = aleph0 :=
  limitRecOn_zero _ _ _

@[simp]
theorem beth_succ (o : Ordinal) : beth (succ o) = 2 ^ beth o :=
  limitRecOn_succ _ _ _ _

theorem beth_limit {o : Ordinal} : o.IsLimit → beth o = ⨆ a : Iio o, beth a :=
  limitRecOn_limit _ _ _ _

theorem beth_strictMono : StrictMono beth := by
  intro a b
  induction' b using Ordinal.induction with b IH generalizing a
  intro h
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · exact (Ordinal.not_lt_zero a h).elim
  · rw [lt_succ_iff] at h
    rw [beth_succ]
    apply lt_of_le_of_lt _ (cantor _)
    rcases eq_or_lt_of_le h with (rfl | h)
    · rfl
    exact (IH c (lt_succ c) h).le
  · apply (cantor _).trans_le
    rw [beth_limit hb, ← beth_succ]
    exact le_ciSup (bddAbove_of_small _) (⟨_, hb.succ_lt h⟩ : Iio b)

theorem beth_mono : Monotone beth :=
  beth_strictMono.monotone

@[simp]
theorem beth_lt {o₁ o₂ : Ordinal} : beth o₁ < beth o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt

@[simp]
theorem beth_le {o₁ o₂ : Ordinal} : beth o₁ ≤ beth o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le

theorem aleph_le_beth (o : Ordinal) : aleph o ≤ beth o := by
  induction o using limitRecOn with
  | H₁ => simp
  | H₂ o h =>
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  | H₃ o ho IH =>
    rw [aleph_limit ho, beth_limit ho]
    exact ciSup_mono (bddAbove_of_small _) fun x => IH x.1 x.2

theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ beth o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o

theorem beth_pos (o : Ordinal) : 0 < beth o :=
  aleph0_pos.trans_le <| aleph0_le_beth o

theorem beth_ne_zero (o : Ordinal) : beth o ≠ 0 :=
  (beth_pos o).ne'

theorem beth_normal : IsNormal.{u} fun o => (beth o).ord :=
  (isNormal_iff_strictMono_limit _).2
    ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha => by
      rw [beth_limit ho, ord_le]
      exact ciSup_le' fun b => ord_le.1 (ha _ b.2)⟩

end beth

/-! ### Properties of `mul` -/
section mulOrdinals

/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c * c = c := by
  refine le_antisymm ?_ (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans h) c)
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine Acc.recOn (Cardinal.lt_wf.apply c) (fun c _ => Quotient.inductionOn c fun α IH ol => ?_) h
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩
  classical
  letI := linearOrderOfSTO r
  haveI : IsWellOrder α (· < ·) := wo
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := fun p => max p.1 p.2
  let f : α × α ↪ Ordinal × α × α :=
    ⟨fun p : α × α => (typein (· < ·) (g p), p), fun p q => congr_arg Prod.snd⟩
  let s := f ⁻¹'o Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  -- this is a well order on `α × α`.
  haveI : IsWellOrder _ s := (RelEmbedding.preimage _ _).isWellOrder
  /- it suffices to show that this well order is smaller than `r`
       if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
      `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
      same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
      contradiction. -/
  suffices type s ≤ type r by exact card_le_card this
  refine le_of_forall_lt fun o h => ?_
  rcases typein_surj s h with ⟨p, rfl⟩
  rw [← e, lt_ord]
  refine lt_of_le_of_lt
    (?_ : _ ≤ card (succ (typein (· < ·) (g p))) * card (succ (typein (· < ·) (g p)))) ?_
  · have : { q | s q p } ⊆ insert (g p) { x | x < g p } ×ˢ insert (g p) { x | x < g p } := by
      intro q h
      simp only [s, f, Preimage, Embedding.coeFn_mk, Prod.lex_def, typein_lt_typein,
        typein_inj, mem_setOf_eq] at h
      exact max_le_iff.1 (le_iff_lt_or_eq.2 <| h.imp_right And.left)
    suffices H : (insert (g p) { x | r x (g p) } : Set α) ≃ { x | r x (g p) } ⊕ PUnit from
      ⟨(Set.embeddingOfSubset _ _ this).trans
        ((Equiv.Set.prod _ _).trans (H.prodCongr H)).toEmbedding⟩
    refine (Equiv.Set.insert ?_).trans ((Equiv.refl _).sumCongr punitEquivPUnit)
    apply @irrefl _ r
  cases' lt_or_le (card (succ (typein (· < ·) (g p)))) ℵ₀ with qo qo
  · exact (mul_lt_aleph0 qo qo).trans_le ol
  · suffices (succ (typein LT.lt (g p))).card < ⟦α⟧ from (IH _ this qo).trans_lt this
    rw [← lt_ord]
    apply (ord_isLimit ol).2
    rw [mk'_def, e]
    apply typein_lt_type

end mulOrdinals

end UsingOrdinals

/-! Properties of `mul`, not requiring ordinals -/
section mul

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph0.trans hb) a)
      (by simpa only [one_mul] using mul_le_mul_right' (one_le_aleph0.trans ha) b)

@[simp]
theorem mul_mk_eq_max {α β : Type u} [Infinite α] [Infinite β] : #α * #β = max #α #β :=
  mul_eq_max (aleph0_le_mk α) (aleph0_le_mk β)

@[simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : aleph o₁ * aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (aleph0_le_aleph o₁) (aleph0_le_aleph o₂), aleph_max]

@[simp]
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_right ha)

@[simp]
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_left ha)

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α :=
  aleph0_mul_eq (aleph0_le_mk α)

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α :=
  mul_aleph0_eq (aleph0_le_mk α)

@[simp]
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * aleph o = aleph o :=
  aleph0_mul_eq (aleph0_le_aleph o)

@[simp]
theorem aleph_mul_aleph0 (o : Ordinal) : aleph o * ℵ₀ = aleph o :=
  mul_aleph0_eq (aleph0_le_aleph o)

theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
  (mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (mul_lt_aleph0 h h).trans_le hc) fun h => by
      rw [mul_eq_self h]
      exact max_lt h1 h2

theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b := by
  convert mul_le_mul' (le_max_left a b) (le_max_right a b) using 1
  rw [mul_eq_self]
  exact h.trans (le_max_left a b)

theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) :
    a * b = max a b := by
  rcases le_or_lt ℵ₀ b with hb | hb
  · exact mul_eq_max h hb
  refine (mul_le_max_of_aleph0_le_left h).antisymm ?_
  have : b ≤ a := hb.le.trans h
  rw [max_eq_left this]
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') a
  rw [mul_one]

theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by
  simpa only [mul_comm b, max_comm b] using mul_le_max_of_aleph0_le_left h

theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by
  rw [mul_comm, max_comm]
  exact mul_eq_max_of_aleph0_le_left h h'

theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b := by
  rcases aleph0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  · exact mul_eq_max_of_aleph0_le_left ha' hb
  · exact mul_eq_max_of_aleph0_le_right ha hb'

theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ := by
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rcases eq_or_ne b 0 with (rfl | hb0); · simp
  rcases le_or_lt ℵ₀ a with ha | ha
  · rw [mul_eq_max_of_aleph0_le_left ha hb0]
    exact le_max_left _ _
  · rcases le_or_lt ℵ₀ b with hb | hb
    · rw [mul_comm, mul_eq_max_of_aleph0_le_left hb ha0, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (mul_lt_aleph0 ha hb).le

theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph0_le_left ha hb', max_eq_left hb]

theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']

theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) a
  rw [one_mul]

theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by
  rw [mul_comm]
  exact le_mul_left h

theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_lt ℵ₀ a with ha | ha
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_lt aleph0_pos
      left
      rw [and_assoc]
      use ha
      constructor
      · rw [← not_lt]
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
      · rintro rfl
        apply this
        rw [mul_zero] at h
        exact h.symm
    right
    by_cases h2a : a = 0
    · exact Or.inr h2a
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      exact h.symm
    left
    rw [← h, mul_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    · contradiction
    · contradiction
    rw [← Ne] at h2a
    rw [← one_le_iff_ne_zero] at h2a hb
    norm_cast at h2a hb h ⊢
    apply le_antisymm _ hb
    rw [← not_lt]
    apply fun h2b => ne_of_gt _ h
    conv_rhs => left; rw [← mul_one n]
    rw [mul_lt_mul_left]
    · exact id
    apply Nat.lt_of_succ_le h2a
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph0_le_left ha hb, max_eq_left hab]
    all_goals simp

end mul

/-! ### Properties of `add` -/
section add

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by
      convert mul_le_mul_right' ((nat_lt_aleph0 2).le.trans h) c using 1
      <;> simp [two_mul, mul_eq_self h])
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
  le_antisymm
      (add_eq_self (ha.trans (le_max_left a b)) ▸
        add_le_add (le_max_left _ _) (le_max_right _ _)) <|
    max_le (self_le_add_right _ _) (self_le_add_left _ _)

theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]

@[simp]
theorem add_mk_eq_max {α β : Type u} [Infinite α] : #α + #β = max #α #β :=
  add_eq_max (aleph0_le_mk α)

@[simp]
theorem add_mk_eq_max' {α β : Type u} [Infinite β] : #α + #β = max #α #β :=
  add_eq_max' (aleph0_le_mk β)

theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ := by
  rcases le_or_lt ℵ₀ a with ha | ha
  · rw [add_eq_max ha]
    exact le_max_left _ _
  · rcases le_or_lt ℵ₀ b with hb | hb
    · rw [add_comm, add_eq_max hb, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (add_lt_aleph0 ha hb).le

theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eq <| add_eq_self hc

theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  (add_le_add (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (add_lt_aleph0 h h).trans_le hc) fun h => by
      rw [add_eq_self h]; exact max_lt h1 h2

theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by
  apply le_antisymm
  · rw [← h]
    apply self_le_add_left
  rw [← not_lt]; intro hb
  have : a + b < c := add_lt_of_lt hc ha hb
  simp [h, lt_irrefl] at this

theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_left hb]

theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_comm, add_eq_left hb ha]

theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_lt ℵ₀ a with ha | ha
    · left
      use ha
      rw [← not_lt]
      apply fun hb => ne_of_gt _ h
      intro hb
      exact hb.trans_le (self_le_add_left b a)
    right
    rw [← h, add_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    norm_cast at h ⊢
    rw [← add_right_inj, h, add_zero]
  · rintro (⟨h1, h2⟩ | h3)
    · rw [add_eq_max h1, max_eq_left h2]
    · rw [h3, add_zero]

theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by
  rw [add_comm, add_eq_left_iff]

theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
  add_eq_left ha ((nat_lt_aleph0 _).le.trans ha)

theorem nat_add_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : n + a = a := by
  rw [add_comm, add_nat_eq n ha]

theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
  add_one_of_aleph0_le ha

-- Porting note (#10618): removed `simp`, `simp` can prove it
theorem mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α :=
  add_one_eq (aleph0_le_mk α)

protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  rcases le_or_lt ℵ₀ b with hb | hb
  · have : a < b := ha.trans_le hb
    rw [add_eq_right hb this.le, eq_comm] at h
    rw [eq_of_add_eq_of_aleph0_le h this hb]
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph0 ha hb
    rw [lt_aleph0] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast at h ⊢
    apply add_left_cancel h

protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb

end add

section ciSup

variable {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v})

section add

variable [Nonempty ι] [Nonempty ι']

protected theorem ciSup_add (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    (⨆ i, f i) + c = ⨆ i, f i + c := by
  have : ∀ i, f i + c ≤ (⨆ i, f i) + c := fun i ↦ add_le_add_right (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · + c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_le (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isLimit
      f hf _ (fun h ↦ hs.not_le h.aleph0_le) rfl
    exact hi ▸ le_ciSup bdd i
  rw [add_eq_max hs, max_le_iff]
  exact ⟨ciSup_mono bdd fun i ↦ self_le_add_right _ c,
    (self_le_add_left _ _).trans (le_ciSup bdd <| Classical.arbitrary ι)⟩

protected theorem add_ciSup (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    c + (⨆ i, f i) = ⨆ i, c + f i := by
  rw [add_comm, Cardinal.ciSup_add f hf]; simp_rw [add_comm]

protected theorem ciSup_add_ciSup (hf : BddAbove (range f)) (g : ι' → Cardinal.{v})
    (hg : BddAbove (range g)) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ (i) (j), f i + g j := by
  simp_rw [Cardinal.ciSup_add f hf, Cardinal.add_ciSup g hg]

end add

protected theorem ciSup_mul (c : Cardinal.{v}) : (⨆ i, f i) * c = ⨆ i, f i * c := by
  cases isEmpty_or_nonempty ι; · simp
  obtain rfl | h0 := eq_or_ne c 0; · simp
  by_cases hf : BddAbove (range f); swap
  · have hfc : ¬ BddAbove (range (f · * c)) := fun bdd ↦ hf
      ⟨⨆ i, f i * c, forall_mem_range.mpr fun i ↦ (le_mul_right h0).trans (le_ciSup bdd i)⟩
    simp [iSup, csSup_of_not_bddAbove, hf, hfc]
  have : ∀ i, f i * c ≤ (⨆ i, f i) * c := fun i ↦ mul_le_mul_right' (le_ciSup hf i) c
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · * c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_le (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_of_iSup_eq_of_not_isLimit
      f hf _ (fun h ↦ hs.not_le h.aleph0_le) rfl
    exact hi ▸ le_ciSup bdd i
  rw [mul_eq_max_of_aleph0_le_left hs h0, max_le_iff]
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup' (one_lt_aleph0.trans_le hs)
  exact ⟨ciSup_mono bdd fun i ↦ le_mul_right h0,
    (le_mul_left (zero_lt_one.trans hi).ne').trans (le_ciSup bdd i)⟩

protected theorem mul_ciSup (c : Cardinal.{v}) : c * (⨆ i, f i) = ⨆ i, c * f i := by
  rw [mul_comm, Cardinal.ciSup_mul f]; simp_rw [mul_comm]

protected theorem ciSup_mul_ciSup (g : ι' → Cardinal.{v}) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ (i) (j), f i * g j := by
  simp_rw [Cardinal.ciSup_mul f, Cardinal.mul_ciSup g]

end ciSup

@[simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : aleph o₁ + aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (aleph0_le_aleph o₁), aleph_max]

theorem principal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Ordinal.Principal (· + ·) c.ord :=
  fun a b ha hb => by
  rw [lt_ord, Ordinal.card_add] at *
  exact add_lt_of_lt hc ha hb

theorem principal_add_aleph (o : Ordinal) : Ordinal.Principal (· + ·) (aleph o).ord :=
  principal_add_ord <| aleph0_le_aleph o

theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β :=
  ⟨fun h => Cardinal.eq_of_add_eq_add_right h γ₀, fun h => congr_arg (· + γ) h⟩

@[simp]
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β :=
  add_right_inj_of_lt_aleph0 (nat_lt_aleph0 _)

@[simp]
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β :=
  add_right_inj_of_lt_aleph0 one_lt_aleph0

theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < Cardinal.aleph0) :
    α + γ ≤ β + γ ↔ α ≤ β := by
  refine ⟨fun h => ?_, fun h => add_le_add_right h γ⟩
  contrapose h
  rw [not_le, lt_iff_le_and_ne, Ne] at h ⊢
  exact ⟨add_le_add_right h.1 γ, mt (add_right_inj_of_lt_aleph0 γ₀).1 h.2⟩

@[simp]
theorem add_nat_le_add_nat_iff {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 (nat_lt_aleph0 n)

@[deprecated (since := "2024-02-12")]
alias add_nat_le_add_nat_iff_of_lt_aleph_0 := add_nat_le_add_nat_iff

@[simp]
theorem add_one_le_add_one_iff {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 one_lt_aleph0

@[deprecated (since := "2024-02-12")]
alias add_one_le_add_one_iff_of_lt_aleph_0 := add_one_le_add_one_iff

/-! ### Properties about power -/
section pow

theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_aleph0.1 H2
  H3.symm ▸
    Quotient.inductionOn κ
      (fun α H1 =>
        Nat.recOn n
          (lt_of_lt_of_le
              (by
                rw [Nat.cast_zero, power_zero]
                exact one_lt_aleph0)
              H1).le
          fun n ih =>
          le_of_le_of_eq
            (by
              rw [Nat.cast_succ, power_add, power_one]
              exact mul_le_mul_right' ih _)
            (mul_eq_self H1))
      H1

theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2

theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c := by
  apply ((power_le_power_right <| (cantor c).le).trans _).antisymm
  · exact power_le_power_right ((nat_lt_aleph0 2).le.trans h)
  · rw [← power_mul, mul_eq_self h]

theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} #ι) : prod c = 2 ^ lift.{v} #ι := by
  rw [← lift_id'.{u, v} (prod.{u, v} c), lift_prod, ← lift_two_power]
  apply le_antisymm
  · refine (prod_le_prod _ _ h₂).trans_eq ?_
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph0_le_mk ι), lift_umax.{u, v}]
  · rw [← prod_const', lift_prod]
    refine prod_le_prod _ _ fun i => ?_
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    exact h₁ i

theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)

theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h (by assumption_mod_cast) ((nat_lt_aleph0 n).le.trans h)

theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c :=
  pow_le h (nat_lt_aleph0 n)

theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
  pow_eq h1 (mod_cast h2) (nat_lt_aleph0 n)

theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ := by
  rcases le_or_lt ℵ₀ c with hc | hc
  · exact le_max_of_le_left (power_nat_le hc)
  · exact le_max_of_le_right (power_lt_aleph0 hc (nat_lt_aleph0 _)).le

theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c := by
  apply le_antisymm
  · rw [powerlt_le]
    intro c'
    rw [lt_aleph0]
    rintro ⟨n, rfl⟩
    apply power_nat_le h
  convert le_powerlt c one_lt_aleph0; rw [power_one]

theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ := by
  rcases le_or_lt ℵ₀ c with h | h
  · rw [powerlt_aleph0 h]
    apply le_max_left
  rw [powerlt_le]
  exact fun c' hc' => (power_lt_aleph0 h hc').le.trans (le_max_right _ _)

end pow

/-! ### Computing cardinality of various types -/
section computing

section Function

variable {α β : Type u} {β' : Type v}

theorem mk_equiv_eq_zero_iff_lift_ne : #(α ≃ β') = 0 ↔ lift.{v} #α ≠ lift.{u} #β' := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_eq']

theorem mk_equiv_eq_zero_iff_ne : #(α ≃ β) = 0 ↔ #α ≠ #β := by
  rw [mk_equiv_eq_zero_iff_lift_ne, lift_id, lift_id]

/-- This lemma makes lemmas assuming `Infinite α` applicable to the situation where we have
  `Infinite β` instead. -/
theorem mk_equiv_comm : #(α ≃ β') = #(β' ≃ α) :=
  (ofBijective _ symm_bijective).cardinal_eq

theorem mk_embedding_eq_zero_iff_lift_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v} #α := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_le', not_le]

theorem mk_embedding_eq_zero_iff_lt : #(α ↪ β) = 0 ↔ #β < #α := by
  rw [mk_embedding_eq_zero_iff_lift_lt, lift_lt]

theorem mk_arrow_eq_zero_iff : #(α → β') = 0 ↔ #α ≠ 0 ∧ #β' = 0 := by
  simp_rw [mk_eq_zero_iff, mk_ne_zero_iff, isEmpty_fun]

theorem mk_surjective_eq_zero_iff_lift :
    #{f : α → β' | Surjective f} = 0 ↔ lift.{v} #α < lift.{u} #β' ∨ (#α ≠ 0 ∧ #β' = 0) := by
  rw [← not_iff_not, not_or, not_lt, lift_mk_le', ← Ne, not_and_or, not_ne_iff, and_comm]
  simp_rw [mk_ne_zero_iff, mk_eq_zero_iff, nonempty_coe_sort,
    Set.Nonempty, mem_setOf, exists_surjective_iff, nonempty_fun]

theorem mk_surjective_eq_zero_iff :
    #{f : α → β | Surjective f} = 0 ↔ #α < #β ∨ (#α ≠ 0 ∧ #β = 0) := by
  rw [mk_surjective_eq_zero_iff_lift, lift_lt]

variable (α β')

theorem mk_equiv_le_embedding : #(α ≃ β') ≤ #(α ↪ β') := ⟨⟨_, Equiv.toEmbedding_injective⟩⟩

theorem mk_embedding_le_arrow : #(α ↪ β') ≤ #(α → β') := ⟨⟨_, DFunLike.coe_injective⟩⟩

variable [Infinite α] {α β'}

theorem mk_perm_eq_self_power : #(Equiv.Perm α) = #α ^ #α :=
  ((mk_equiv_le_embedding α α).trans (mk_embedding_le_arrow α α)).antisymm <| by
    suffices Nonempty ((α → Bool) ↪ Equiv.Perm (α × Bool)) by
      obtain ⟨e⟩ : Nonempty (α ≃ α × Bool) := by
        erw [← Cardinal.eq, mk_prod, lift_uzero, mk_bool,
          lift_natCast, mul_two, add_eq_self (aleph0_le_mk α)]
      erw [← le_def, mk_arrow, lift_uzero, mk_bool, lift_natCast 2] at this
      rwa [← power_def, power_self_eq (aleph0_le_mk α), e.permCongr.cardinal_eq]
    refine ⟨⟨fun f ↦ Involutive.toPerm (fun x ↦ ⟨x.1, xor (f x.1) x.2⟩) fun x ↦ ?_, fun f g h ↦ ?_⟩⟩
    · simp_rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    · ext a; rw [← (f a).xor_false, ← (g a).xor_false]; exact congr(($h ⟨a, false⟩).2)

theorem mk_perm_eq_two_power : #(Equiv.Perm α) = 2 ^ #α := by
  rw [mk_perm_eq_self_power, power_self_eq (aleph0_le_mk α)]

theorem mk_equiv_eq_arrow_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') :
    #(α ≃ β') = #(α → β') := by
  obtain ⟨e⟩ := lift_mk_eq'.mp leq
  have e₁ := lift_mk_eq'.mpr ⟨.equivCongr (.refl α) e⟩
  have e₂ := lift_mk_eq'.mpr ⟨.arrowCongr (.refl α) e⟩
  rw [lift_id'.{u,v}] at e₁ e₂
  rw [← e₁, ← e₂, lift_inj, mk_perm_eq_self_power, power_def]

theorem mk_equiv_eq_arrow_of_eq (eq : #α = #β) : #(α ≃ β) = #(α → β) :=
  mk_equiv_eq_arrow_of_lift_eq congr(lift $eq)

theorem mk_equiv_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = 2 ^ lift.{v} #α := by
  erw [← (lift_mk_eq'.2 ⟨.equivCongr (.refl α) (lift_mk_eq'.1 leq).some⟩).trans (lift_id'.{u,v} _),
    lift_umax.{u,v}, mk_perm_eq_two_power, lift_power, lift_natCast]; rfl

theorem mk_equiv_of_eq (eq : #α = #β) : #(α ≃ β) = 2 ^ #α := by
  rw [mk_equiv_of_lift_eq (lift_inj.mpr eq), lift_id]

theorem mk_embedding_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #(β' ↪ α) = #(β' → α) :=
  (mk_embedding_le_arrow _ _).antisymm <| by
    conv_rhs => rw [← (Equiv.embeddingCongr (.refl _)
      (Cardinal.eq.mp <| mul_eq_self <| aleph0_le_mk α).some).cardinal_eq]
    obtain ⟨e⟩ := lift_mk_le'.mp lle
    exact ⟨⟨fun f ↦ ⟨fun b ↦ ⟨e b, f b⟩, fun _ _ h ↦ e.injective congr(Prod.fst $h)⟩,
      fun f g h ↦ funext fun b ↦ congr(Prod.snd <| $h b)⟩⟩

theorem mk_embedding_eq_arrow_of_le (le : #β ≤ #α) : #(β ↪ α) = #(β → α) :=
  mk_embedding_eq_arrow_of_lift_le (lift_le.mpr le)

theorem mk_surjective_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #{f : α → β' | Surjective f} = #(α → β') :=
  (mk_set_le _).antisymm <|
    have ⟨e⟩ : Nonempty (α ≃ α ⊕ β') := by
      simp_rw [← lift_mk_eq', mk_sum, lift_add, lift_lift]; rw [lift_umax.{u,v}, eq_comm]
      exact add_eq_left (aleph0_le_lift.mpr <| aleph0_le_mk α) lle
    ⟨⟨fun f ↦ ⟨fun a ↦ (e a).elim f id, fun b ↦ ⟨e.symm (.inr b), congr_arg _ (e.right_inv _)⟩⟩,
      fun f g h ↦ funext fun a ↦ by
        simpa only [e.apply_symm_apply] using congr_fun (Subtype.ext_iff.mp h) (e.symm <| .inl a)⟩⟩

theorem mk_surjective_eq_arrow_of_le (le : #β ≤ #α) : #{f : α → β | Surjective f} = #(α → β) :=
  mk_surjective_eq_arrow_of_lift_le (lift_le.mpr le)

end Function

@[simp]
theorem mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α :=
  have H1 : ℵ₀ ≤ #α := aleph0_le_mk α
  Eq.symm <|
    le_antisymm ((le_def _ _).2 ⟨⟨fun a => [a], fun _ => by simp⟩⟩) <|
      calc
        #(List α) = sum fun n : ℕ => #α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun _ : ℕ => #α := sum_le_sum _ _ fun n => pow_le H1 <| nat_lt_aleph0 n
        _ = #α := by simp [H1]

theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀ :=
  mk_le_aleph0.antisymm (aleph0_le_mk _)

theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀ := by
  cases finite_or_infinite α
  · rw [mk_list_eq_aleph0, eq_comm, max_eq_right]
    exact mk_le_aleph0
  · rw [mk_list_eq_mk, eq_comm, max_eq_left]
    exact aleph0_le_mk α

theorem mk_list_le_max (α : Type u) : #(List α) ≤ max ℵ₀ #α := by
  cases finite_or_infinite α
  · exact mk_le_aleph0.trans (le_max_left _ _)
  · rw [mk_list_eq_mk]
    apply le_max_right

@[simp]
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α := by
  classical
  exact Eq.symm <|
    le_antisymm (mk_le_of_injective fun _ _ => Finset.singleton_inj.1) <|
      calc
        #(Finset α) ≤ #(List α) := mk_le_of_surjective List.toFinset_surjective
        _ = #α := mk_list_eq_mk α

theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ #α ^ c := by
  refine le_trans ?_ (by rw [← add_one_eq (aleph0_le_mk α)])
  induction' c using Cardinal.inductionOn with β
  fapply mk_le_of_surjective
  · intro f
    use Sum.inl ⁻¹' range f
    refine le_trans (mk_preimage_of_injective _ _ fun x y => Sum.inl.inj) ?_
    apply mk_range_le
  rintro ⟨s, ⟨g⟩⟩
  classical
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.choose h).val
               else Sum.inr (ULift.up 0)
  apply Subtype.eq; ext x
  constructor
  · rintro ⟨y, h⟩
    dsimp only at h
    by_cases h' : ∃ z : s, g z = y
    · rw [dif_pos h'] at h
      cases Sum.inl.inj h
      exact (Classical.choose h').2
    · rw [dif_neg h'] at h
      cases h
  · intro h
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    use g ⟨x, h⟩
    dsimp only
    rw [dif_pos this]
    congr
    suffices Classical.choose this = ⟨x, h⟩ from congr_arg Subtype.val this
    apply g.2
    exact Classical.choose_spec this

theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ max #α ℵ₀ ^ c := by
  trans #{ t : Set ((ULift.{u} ℕ) ⊕ α) // #t ≤ c }
  · refine ⟨Embedding.subtypeMap ?_ ?_⟩
    · apply Embedding.image
      use Sum.inr
      apply Sum.inr.inj
    intro s hs
    exact mk_image_le.trans hs
  apply (mk_bounded_set_le_of_infinite ((ULift.{u} ℕ) ⊕ α) c).trans
  rw [max_comm, ← add_eq_max] <;> rfl

theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    #{ t : Set α // t ⊆ s ∧ #t ≤ c } ≤ max #s ℵ₀ ^ c := by
  refine le_trans ?_ (mk_bounded_set_le s c)
  refine ⟨Embedding.codRestrict _ ?_ ?_⟩
  · use fun t => (↑) ⁻¹' t.1
    rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    apply Subtype.eq
    dsimp only at h ⊢
    refine (preimage_eq_preimage' ?_ ?_).1 h <;> rw [Subtype.range_coe] <;> assumption
  rintro ⟨t, _, h2t⟩; exact (mk_preimage_of_injective _ _ Subtype.val_injective).trans h2t

end computing

/-! ### Properties of `compl` -/
section compl

theorem mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
    #(sᶜ : Set α) = #α := by
  refine eq_of_add_eq_of_aleph0_le ?_ h2 (aleph0_le_mk α)
  exact mk_sum_compl s

theorem mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) :
    #((↑s)ᶜ : Set α) = #α := by
  apply mk_compl_of_infinite
  exact (finset_card_lt_aleph0 s).trans_le (aleph0_le_mk α)

theorem mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs : #s < #α)
    (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]

theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : (lift.{max v w, u} #α) = (lift.{max u w, v} #β))
    (h2 : lift.{max v w, u} #s = lift.{max u w, v} #t) :
    lift.{max v w} #(sᶜ : Set α) = lift.{max u w} #(tᶜ : Set β) := by
  cases nonempty_fintype α
  rcases lift_mk_eq.{u, v, w}.1 h1 with ⟨e⟩; letI : Fintype β := Fintype.ofEquiv α e
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.ofEquiv_card _).symm
  classical
    lift s to Finset α using s.toFinite
    lift t to Finset β using t.toFinite
    simp only [Finset.coe_sort_coe, mk_fintype, Fintype.card_coe, lift_natCast, Nat.cast_inj] at h2
    simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_coe_finset, Finset.card_compl,
      lift_natCast, Nat.cast_inj, h1, h2]

theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β) := by
  rw [← lift_inj.{u, u}]
  apply mk_compl_eq_mk_compl_finite_lift.{u, u, u}
  <;> rwa [lift_inj]

theorem mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h : #s = #t) :
    #(sᶜ : Set α) = #(tᶜ : Set α) :=
  mk_compl_eq_mk_compl_finite.{u} rfl h

end compl

/-! ### Extending an injection to an equiv -/

theorem extend_function {α β : Type*} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  classical
  have := h; cases' this with g
  let h : α ≃ β :=
    (Set.sumCompl (s : Set α)).symm.trans
      ((sumCongr (Equiv.ofInjective f f.2) g).trans (Set.sumCompl (range f)))
  refine ⟨h, ?_⟩; rintro ⟨x, hx⟩; simp [h, Set.sumCompl_symm_apply_of_mem, hx]

theorem extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  apply extend_function.{u, v} f
  cases' id h with g
  rw [← lift_mk_eq.{u, v, max u v}] at h
  rw [← lift_mk_eq.{u, v, max u v}, mk_compl_eq_mk_compl_finite_lift.{u, v, max u v} h]
  rw [mk_range_eq_lift.{u, v, max u v}]; exact f.2

theorem extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  cases fintypeOrInfinite α
  · exact extend_function_finite f h
  · apply extend_function f
    cases' id h with g
    haveI := Infinite.of_injective _ g.injective
    rw [← lift_mk_eq'] at h ⊢
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]

-- Porting note: we no longer express literals as `bit0` and `bit1` in Lean 4, so we can't use this
-- section Bit

-- /-!
-- This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
-- for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
-- `simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
-- is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
-- enough for practical situations, though.

-- For specific numbers, these inequalities could also be deduced from the corresponding
-- inequalities of natural numbers using `norm_cast`:
-- ```
-- example : (37 : cardinal) < 42 :=
-- by { norm_cast, norm_num }
-- ```
-- -/

-- theorem bit0_ne_zero (a : Cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 := by simp [bit0]

-- @[simp]
-- theorem bit1_ne_zero (a : Cardinal) : ¬bit1 a = 0 := by simp [bit1]

-- @[simp]
-- theorem zero_lt_bit0 (a : Cardinal) : 0 < bit0 a ↔ 0 < a := by
--   rw [← not_iff_not]
--   simp [bit0]

-- @[simp]
-- theorem zero_lt_bit1 (a : Cardinal) : 0 < bit1 a :=
--   zero_lt_one.trans_le (self_le_add_left _ _)

-- @[simp]
-- theorem one_le_bit0 (a : Cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
--   ⟨fun h => (zero_lt_bit0 a).mp (zero_lt_one.trans_le h), fun h =>
--     (one_le_iff_pos.mpr h).trans (self_le_add_left a a)⟩

-- @[simp]
-- theorem one_le_bit1 (a : Cardinal) : 1 ≤ bit1 a :=
--   self_le_add_left _ _

-- theorem bit0_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : bit0 c = c :=
--   add_eq_self h

-- @[simp]
-- theorem bit0_lt_aleph0 {c : Cardinal} : bit0 c < ℵ₀ ↔ c < ℵ₀ :=
--   by simp [bit0, add_lt_aleph_0_iff]

-- @[simp]
-- theorem aleph0_le_bit0 {c : Cardinal} : ℵ₀ ≤ bit0 c ↔ ℵ₀ ≤ c := by
--   rw [← not_iff_not]
--   simp

-- @[simp]
-- theorem bit1_eq_self_iff {c : Cardinal} : bit1 c = c ↔ ℵ₀ ≤ c := by
--   by_cases h : ℵ₀ ≤ c
--   · simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_aleph_0_le]
--   · refine' iff_of_false (ne_of_gt _) h
--     rcases lt_aleph_0.1 (not_le.1 h) with ⟨n, rfl⟩
--     norm_cast
--     dsimp [bit1, bit0]
--     linarith

-- @[simp]
-- theorem bit1_lt_aleph0 {c : Cardinal} : bit1 c < ℵ₀ ↔ c < ℵ₀ := by
--   simp [bit1, bit0, add_lt_aleph_0_iff, one_lt_aleph_0]

-- @[simp]
-- theorem aleph0_le_bit1 {c : Cardinal} : ℵ₀ ≤ bit1 c ↔ ℵ₀ ≤ c := by
--   rw [← not_iff_not]
--   simp

-- @[simp]
-- theorem bit0_le_bit0 {a b : Cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · rw [bit0_eq_self ha, bit0_eq_self hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit0_le_bit0

-- @[simp]
-- theorem bit0_le_bit1 {a b : Cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
--     have A : bit1 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact Nat.bit0_le_bit1_iff

-- @[simp]
-- theorem bit1_le_bit1 {a b : Cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
--   ⟨fun h => bit0_le_bit1.1 ((self_le_add_right (bit0 a) 1).trans h), fun h =>
--     (add_le_add_right (add_le_add_left h a) 1).trans (add_le_add_right (add_le_add_right h b) 1)⟩

-- @[simp]
-- theorem bit1_le_bit0 {a b : Cardinal} : bit1 a ≤ bit0 b ↔ a < b ∨ a ≤ b ∧ ℵ₀ ≤ a := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_true_iff]
--     refine' ⟨fun h => Or.inr h, fun h => _⟩
--     cases h
--     · exact le_of_lt h
--     · exact h
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) fun h => _
--     · have A : bit0 b < ℵ₀ := by simpa using hb
--       exact lt_irrefl _ ((A.trans_le ha).trans_le h)
--     · exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt And.left)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).le.trans hb) (Or.inl <| ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     simp [not_le.mpr ha]

-- @[simp]
-- theorem bit0_lt_bit0 {a b : Cardinal} : bit0 a < bit0 b ↔ a < b := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · rw [bit0_eq_self ha, bit0_eq_self hb]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit0_lt_bit0

-- @[simp]
-- theorem bit1_lt_bit0 {a b : Cardinal} : bit1 a < bit0 b ↔ a < b := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb]
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit0 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit0_eq_self hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact Nat.bit1_lt_bit0_iff

-- @[simp]
-- theorem bit1_lt_bit1 {a b : Cardinal} : bit1 a < bit1 b ↔ a < b := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb]
--   · rw [bit1_eq_self_iff.2 ha]
--     refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
--     have A : bit1 b < ℵ₀ := by simpa using hb
--     exact lt_irrefl _ ((A.trans_le ha).trans h)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     exact bit1_lt_bit1

-- @[simp]
-- theorem bit0_lt_bit1 {a b : Cardinal} : bit0 a < bit1 b ↔ a < b ∨ a ≤ b ∧ a < ℵ₀ := by
--   rcases le_or_lt ℵ₀ a with ha | ha <;> rcases le_or_lt ℵ₀ b with hb | hb
--   · simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha]
--   · rw [bit0_eq_self ha]
--     refine' iff_of_false (fun h => _) fun h => _
--     · have A : bit1 b < ℵ₀ := by simpa using hb
--       exact lt_irrefl _ ((A.trans_le ha).trans h)
--     · exact (hb.trans_le ha).not_le (h.elim le_of_lt And.left)
--   · rw [bit1_eq_self_iff.2 hb]
--     exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (Or.inl <| ha.trans_le hb)
--   · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
--     rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
--     norm_cast
--     simp only [ha, and_true_iff, Nat.bit0_lt_bit1_iff, or_iff_right_of_imp le_of_lt]

-- theorem one_lt_two : (1 : Cardinal) < 2 := by
--   -- This strategy works generally to prove inequalities between numerals in `cardinality`.
--   norm_cast
--   norm_num

-- @[simp]
-- theorem one_lt_bit0 {a : Cardinal} : 1 < bit0 a ↔ 0 < a := by simp [← bit1_zero]

-- @[simp]
-- theorem one_lt_bit1 (a : Cardinal) : 1 < bit1 a ↔ 0 < a := by simp [← bit1_zero]

-- end Bit

end Cardinal

section Initial

namespace Ordinal

/--
`ω_ o` is a notation for the *initial ordinal* of cardinality
`aleph o`. Thus, for example `ω_ 0 = ω`.
-/
scoped notation "ω_" o => ord <| aleph o

/--
`ω₁` is the first uncountable ordinal.
-/
scoped notation "ω₁" => ord <| aleph 1

lemma omega_lt_omega1 : ω < ω₁ := ord_aleph0.symm.trans_lt (ord_lt_ord.mpr (aleph0_lt_aleph_one))

section OrdinalIndices
/-!
### Cardinal operations with ordinal indices

Results on cardinality of ordinal-indexed families of sets.
-/
namespace Cardinal

open scoped Cardinal

/--
Bounding the cardinal of an ordinal-indexed union of sets.
-/
lemma mk_iUnion_Ordinal_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal}
    (ho : o.card ≤ c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) :
    #(⋃ j < o, A j) ≤ c := by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← o.enumIsoToType.symm.surjective.range_comp]
  apply ((mk_iUnion_le _).trans _).trans_eq (mul_eq_self hc)
  rw [mk_toType]
  exact mul_le_mul' ho <| ciSup_le' <| (hA _ <| typein_lt_self ·)

end Cardinal

end OrdinalIndices

end Ordinal

end Initial

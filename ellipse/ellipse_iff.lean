import Mathlib.Geometry.Synthetic.Avigad.Tactics
import Mathlib.Tactic.WLOG

variable [I : IncidenceGeometry] {a a1 a2 b b1 b2 c d e f g h i j k l m n o p q s x y :
  IncidenceGeometry.Point} {L M N O P Q R S T U W V X : IncidenceGeometry.Line}
  {α β : IncidenceGeometry.Circle} {r : ℝ}
namespace IncidenceGeometry
-- open Topology Filter

-- todolist
-- 0.将命题描述成中文，改写代码成不跳步。
-- 1.看看怎么将下面这种定义putnam_1963_a6，改写成这里的公理体系的写法：
  -- 可能还需要证明很多东西
-- 2.将两个椭圆的定义互相等价证明一下。


-- theorem putnam_1963_a6
-- (F1 F2 U V A B C D P Q : EuclideanSpace ℝ (Fin 2))
-- (r : ℝ)
-- (E : Set (EuclideanSpace ℝ (Fin 2)))
-- (hE : E = {H : EuclideanSpace ℝ (Fin 2) | dist F1 H + dist F2 H = r})
-- (M : EuclideanSpace ℝ (Fin 2))
-- (hM : M = midpoint ℝ U V)
-- (hr : r > dist F1 F2)
-- (hUV : U ∈ E ∧ V ∈ E ∧ U ≠ V)
-- (hAB : A ∈ E ∧ B ∈ E ∧ A ≠ B)
-- (hCD : C ∈ E ∧ D ∈ E ∧ C ≠ D)
-- (hdistinct : segment ℝ A B ≠ segment ℝ U V ∧ segment ℝ C D ≠ segment ℝ U V ∧ segment ℝ A B ≠ segment ℝ C D)
-- (hM : M ∈ segment ℝ A B ∧ M ∈ segment ℝ C D)
-- (hP : Collinear ℝ {P, A, C} ∧ Collinear ℝ {P, U, V})
-- (hQ : Collinear ℝ {P, B, D} ∧ Collinear ℝ {Q, U, V})
-- : M = midpoint ℝ P Q :=
-- sorry

/-- 点a在线L上，点b不在线L上。则，=》 点b不等于点a。
-- 思路：替换，矛盾 -/
theorem ne_of_online' (aL : OnLine a L) (bL : ¬OnLine b L) : b ≠ a :=
by
  intro ab
  rw [←ab] at aL
  exact bL aL

/-- a在圆A的圆心上，b和c也在圆A上。则，=》ab距离等于ac距离。
-- 思路：搜索相关公理。 -/
theorem length_eq_of_oncircle (aα : CenterCircle a α) (bα : OnCircle b α) (cα : OnCircle c α) :
    length a b = length a c := by
    have h1:= @on_circle_iff_length_eq I a b c α aα bα
    have h2:= h1.2
    apply h2
    exact cα

/-- 点a，b,c互不相同。则，=》存在一个点d，存在一个圆A，使得满足abd按顺序共线，且满足b是A的圆心，且满足c，d在圆A上。
-- 思路：倒推，需要一个点，一个圆。圆规画圆得出一个圆，然后直线和圆交点得出一个点。 -/
theorem B_circ_of_ne (ab : a ≠ b) (bc : b ≠ c)
: ∃ d α,
B a b d
∧
CenterCircle b α
∧
OnCircle c α
∧
OnCircle d α := by
rcases circle_of_ne bc with ⟨α, bα, cα⟩
have h1 := inside_circle_of_center bα
rcases pt_oncircle_of_inside_ne ab h1 with ⟨d, Babd, dα⟩;
exact ⟨d, α, Babd, bα, cα, dα⟩

-- 有趣思考：lean是如何考虑到所有abc三个点之间的相对关系，做到滴水不漏的呢？来看：
/-- 点a，b,c互不相同。则，=》存在一个点d，使得满足a,b,d按顺序共线；且使得bc距离等于bd距离 -/
-- 思路：就是用的之前的存在行定理，造出一个点，一个圆。
theorem length_eq_B_of_ne
(ab : a ≠ b)
(bc : b ≠ c)
: ∃ d,
B a b d
∧
length b c = length b d
:= by
  rcases B_circ_of_ne ab bc with ⟨d, α, Babd, bα, cα, dα⟩
  exact ⟨d, Babd, length_eq_of_oncircle bα cα dα⟩

/-- a,b,c严格按顺序共线。则，=》b和a不相同 -/
-- 思路：就是公理里面的严格，导致不同。
theorem ne_21_of_B (Babc : B a b c) : b ≠ a := Ne.symm $ ne_12_of_B Babc

/-- 任何一条直线L，则，=》存在点a，a在直线L上 -/
-- 思路：首先凭空造一个点，然后分类讨论是否在线上。
-- 不在线上就用“两点交一线”反推，反推需要“两线相交”。
-- “两线相交”用两点共线1，不同侧线2反推，反推需要“两点共线1”，“不同侧线2”
-- “两点共线1”用公理
-- “不同侧线2”用公理“直线两侧存在不同的点都不在直线上”
theorem online_of_line L : ∃ a, OnLine a L := by
  have h1 := more_pts ∅ Set.finite_empty
  rcases h1 with ⟨a, -⟩ -- 也就是舍弃了这个a2命题 -- rcases h1 with ⟨a, a2⟩ --
  by_cases (OnLine a L)
  { use a}
  {
    rcases diffSide_of_not_onLine h with ⟨b, -, abL⟩
    rcases line_of_pts a b with ⟨M, aM, bM⟩
    rcases pt_of_linesInter (lines_inter_of_not_sameSide aM bM abL) with ⟨c, cL, -⟩;
    exact ⟨c, cL⟩
  }

/-- 对于一条线，存在两个不同的点都在这条线上。 -/
-- 和这个online_of_line就差一个两点不同。
theorem online_ne_of_line L :
∃ c d,
c ≠ d
∧
OnLine c L
∧
OnLine d L
:= by
  rcases online_of_line L with ⟨a, aL⟩;
  rcases more_pts {a} (Set.finite_singleton a) with ⟨b, hb⟩;
  have h1:= ne_of_mem_of_not_mem (Set.mem_singleton a) hb -- 用到了集合的基础logic
  rcases circle_of_ne h1 with ⟨α, acen, -⟩;
  have h1:= (inside_circle_of_center acen)
  have h2:= lineCircleInter_of_inside_onLine aL h1
  rcases pts_of_lineCircleInter h2 with ⟨c, d, cd, cL, dL, -, -⟩;
  exact ⟨c, d, cd, cL, dL⟩

/-- 两个不同的点a，b的距离大于0 -/
-- 思路：用的公理length_nonneg
lemma len_pos_of_nq (ab : a ≠ b) : 0 < length a b :=
  (Ne.symm (not_imp_not.mpr length_eq_zero_iff.mp ab)).le_iff_lt.mp (length_nonneg a b) -- 用到logic，Core

/-- abc按顺序共线，则b和c不同 -/
theorem ne_23_of_B (Babc : B a b c) : b ≠ c := (ne_12_of_B $ (B_symm Babc)).symm

/-- abc按顺序共线，则任意两点距离都大于0，且ab+bc=ac -/
-- 思路：用的公理
theorem length_sum_perm_of_B (Babc : B a b c) : 0 < length a b ∧ 0 < length b c ∧
    0 < length a c ∧ length a b + length b c = length a c := by
  splitAll;
  exact len_pos_of_nq $ ne_12_of_B Babc;
  exact len_pos_of_nq $ ne_23_of_B Babc
  exact len_pos_of_nq $ ne_13_of_B Babc;
  exact length_sum_of_B Babc

/-- 两点ab不同，长度ab=cd，则cd两点也不同 -/
-- 思路：反证法，证明ab长度同时为0和大于0
theorem ne_of_ne_len (ab : a ≠ b) (ab_cd : length a b = length c d) : c ≠ d :=
  fun ac => by linarith [length_eq_zero_iff.mpr ac, len_pos_of_nq ab]

-- /-- 对于直线L，存在一个点不在直线L上。-/
-- theorem not_online_of_line L : ∃ a, ¬OnLine a L := by
--   rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
--   rcases circle_of_ne bc with ⟨α, bα, cα⟩
--   rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩
--   rcases pts_of_circlesInter (circlesInter_of_inside_on_circle cα bβ (inside_circle_of_center
--      bα) (inside_circle_of_center cβ)) with ⟨a, -, -, aα, aβ, -, -⟩
--   have bc_ba := (on_circle_iff_length_eq bα cα).mpr aα
--   have cb_ca := (on_circle_iff_length_eq cβ bβ).mpr aβ
--   refine ⟨a, fun aL => (by push_neg; splitAll; all_goals exact (fun Bet =>
--     by linarith[length_sum_perm_of_B Bet]) : ¬ (B b c a ∨ B c b a ∨ B b a c)) $
--     B_of_three_onLine_ne bc (ne_of_ne_len bc bc_ba) (ne_of_ne_len bc.symm cb_ca) bL cL aL⟩

/-- 对于直线L，存在一个点不在直线L上。-/
-- 思路：正反推思路相连了。
theorem not_online_of_line L : ∃ a, ¬OnLine a L := by
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  rcases circle_of_ne bc with ⟨α, bα, cα⟩
  rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩
  have h1:=(inside_circle_of_center cβ)
  have h2:= inside_circle_of_center bα
  have h3:= circlesInter_of_inside_on_circle cα bβ h2 h1
  rcases pts_of_circlesInter h3 with ⟨a, -, -, aα, aβ, -, -⟩
  have bc_ba := (on_circle_iff_length_eq bα cα).mpr aα
  have cb_ca := (on_circle_iff_length_eq cβ bβ).mpr aβ
  use a
  intro aL
  have h4:= (ne_of_ne_len bc.symm cb_ca)
  have h5:= (ne_of_ne_len bc bc_ba)
  have h6:= B_of_three_onLine_ne bc h5 h4 bL cL aL
  have h7:  ¬ (B b c a ∨ B c b a ∨ B b a c)
  := by
    push_neg
    splitAll
    all_goals {
      intro Bet
      have h8:= length_sum_perm_of_B Bet
      simp [bc_ba,← cb_ca] at h8
      linarith
    }
  exact h7 h6

/-- 如果a,b为圆心的两个圆相交，则，=》存在点c，线L，使得a在L上，使得b在L上，使得c在圆A上，c在圆B上，c不在线L上。 -/
-- 思路：为什么交点肯定有两个？相交应该不包含相切。
theorem online_of_circlesinter (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (αβ : CirclesInter α β) : ∃ c L, OnLine a L ∧ OnLine b L ∧ OnCircle c α ∧
    OnCircle c β ∧ ¬OnLine c L := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩;
  rcases not_online_of_line L with ⟨d, dL⟩;
  rcases pt_sameSide_of_circlesInter aL bL dL aα bβ αβ with ⟨c, cdL, cα, cβ⟩;
  exact ⟨c, L, aL, bL, cα, cβ, not_onLine_of_sameSide cdL⟩

-- 正着看证明方法太崎岖了，好像就一种办法一样，错觉吗？难道真的每种特定问题只有一种证明范式？

theorem not_sameSide_symm (abL : ¬SameSide a b L) : ¬SameSide b a L := fun baL =>
  abL (sameSide_symm baL)

lemma DiffSide_symm (abL : DiffSide a b L) : DiffSide b a L :=
  ⟨abL.2.1, abL.1, (not_sameSide_symm abL.2.2)⟩

theorem DiffSide_of_sameside_DiffSide (abL : SameSide a b L) (acL : DiffSide a c L) :
    DiffSide b c L := by
by_contra h; unfold DiffSide at h; push_neg at h; exact acL.2.2
 (sameSide_trans (sameSide_symm abL) (h (not_onLine_of_sameSide (sameSide_symm abL)) acL.2.1))

theorem DiffSide_of_circlesinter (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (αβ : CirclesInter α β) : ∃ c d L, OnLine a L ∧ OnLine b L ∧ OnCircle c α ∧
    OnCircle c β ∧ OnCircle d α ∧ OnCircle d β ∧ DiffSide c d L := by
rcases online_of_circlesinter aα bβ αβ with ⟨c, L, aL, bL, cα, cβ, cL⟩;
rcases diffSide_of_not_onLine cL with ⟨e, eL, ceL⟩; rcases pt_sameSide_of_circlesInter aL bL eL
 aα bβ αβ with ⟨d, deL, dα, dβ⟩; exact ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, DiffSide_symm
 (DiffSide_of_sameside_DiffSide (sameSide_symm deL) ⟨eL, cL, not_sameSide_symm ceL⟩)⟩

theorem online_of_col_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (col_abc : Colinear a b c) : OnLine c L :=
by rcases col_abc with ⟨L, aM, bM, cM⟩; rwa [line_unique_of_pts ab aM bM aL bL] at cM


theorem Triangle_of_ne_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (cL : ¬OnLine c L) :
    Triangle a b c := fun col => by exact cL (online_of_col_online ab aL bL col)

theorem EqTri_of_length_online (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (cL : ¬OnLine c L)
    (ab_ac : length a b = length a c) (bc_ba : length b c = length b a) : EqTri a b c :=
⟨Triangle_of_ne_online ab aL bL cL, by perma, by linperm, by linperm⟩

/-- Euclid I.1, construction of two equilateral Triangles -/
theorem iseqtri_iseqtri_DiffSide_of_ne (ab : a ≠ b) : ∃ c d L, OnLine a L ∧
    OnLine b L ∧ DiffSide c d L ∧ EqTri a b c ∧ EqTri a b d := by
rcases circle_of_ne ab with ⟨α, aα, bα⟩
rcases circle_of_ne (Ne.symm ab) with ⟨β, bβ, aβ⟩
rcases DiffSide_of_circlesinter aα bβ (circlesInter_of_inside_on_circle bα aβ
  (inside_circle_of_center aα) (inside_circle_of_center bβ)) with
  ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩
have ab_ac := (on_circle_iff_length_eq aα bα).mpr cα
have bc_ba := (on_circle_iff_length_eq bβ cβ).mpr aβ
have ab_ad := (on_circle_iff_length_eq aα bα).mpr dα
have bd_ba := (on_circle_iff_length_eq bβ dβ).mpr aβ
exact ⟨c, d, L, aL, bL, cdL, EqTri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
  EqTri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩


theorem sameSide_or_of_diffSide' (cL : ¬OnLine c L) (abL : DiffSide a b L) :
    SameSide a c L ∨ SameSide b c L := sameSide_or_of_diffSide abL.1 abL.2.1 cL abL.2.2

/-- Euclid I.1, construction of an equilateral Triangle on the sameside of a point -/
theorem iseqtri_sameside_of_ne (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (dL : ¬OnLine d L):
    ∃ c, ¬OnLine c L ∧ SameSide c d L ∧ EqTri a b c := by
  rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c1, c2, M, aM, bM, c1c2M, eqtri1, eqtri2⟩
  rcases sameSide_or_of_diffSide' dL (by rwa [line_unique_of_pts ab aM bM aL bL] at c1c2M)
    with c1dL | c2dL
  refine ⟨c1, not_onLine_of_sameSide c1dL, c1dL, eqtri1⟩
  refine ⟨c2, not_onLine_of_sameSide c2dL, c2dL, eqtri2⟩

theorem sss (ab_de : length a b = length d e) (bc_ef : length b c = length e f)
    (ac_df : length a c = length d f) : angle a b c = angle d e f ∧ angle b a c = angle e d f
    ∧ angle a c b = angle d f e := ⟨(SAS_iff_SSS (by linperm) bc_ef).mpr ac_df,
  (SAS_iff_SSS ab_de ac_df).mpr bc_ef, (SAS_iff_SSS (by linperm) (by linperm)).mpr ab_de⟩

theorem rightangle_of_angle_eq (Babc : B a b c) (aL : OnLine a L) (cL : OnLine c L)
    (dL : ¬OnLine d L) (dba_dbc : angle d b a = angle d b c) :
    angle d b a = rightangle ∧ angle d b c = rightangle := by
  have ang := (angle_eq_iff_rightangle aL cL dL Babc).mp $ by perma[dba_dbc]
  exact ⟨by perma[ang], by linperm⟩

theorem B_or_B_of_B_B (cd : c ≠ d) (Babc : B a b c) (Babd : B a b d) :
    B b c d ∨ B b d c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases B_of_three_onLine_ne (ne_23_of_B Babc) (ne_23_of_B Babd) cd bL
    (onLine_3_of_B Babc aL bL) (onLine_3_of_B Babd aL bL) with Bet | Bet | Bet
  left; exact Bet; exfalso; exact (not_B324_of_B123_B124 Babc Babd) Bet; right; exact Bet

theorem angle_extension_of_B (ac : a ≠ c) (Babb1 : B a b b1) : angle b a c = angle b1 a c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩;
  refine angle_extension ((ne_12_of_B Babb1).symm) ((ne_13_of_B Babb1).symm) ac.symm ac.symm aL bL
    (onLine_3_of_B Babb1 aL bL) aM cM cM (not_B_of_B Babb1) $ fun Bcac => (ne_13_of_B Bcac) rfl

theorem angle_extension_of_B_B (be : b ≠ e) (Babc : B a b c) (Babd : B a b d) :
    angle e b d = angle e b c := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_B_B cd Babc Babd with Bet | Bet; symm
  perma[angle_extension_of_B be Bet]; perma[angle_extension_of_B be Bet]


theorem ne_of_online (aL : OnLine a L) (bL : ¬OnLine b L) : a ≠ b :=
  fun ab => by rw [ab] at aL; exact bL aL

/-- Euclid I.11, Obtaining perpendicular angles from a point on a line -/
theorem perpendicular_of_online (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (fL : ¬OnLine f L) :
    ∃ e, SameSide e f L ∧ angle e b a = rightangle ∧ angle e b c = rightangle := by
  rcases length_eq_B_of_ne (ne_12_of_B Babc) (ne_21_of_B Babc) with ⟨d, Babd, ba_bd⟩
  rcases iseqtri_sameside_of_ne (ne_13_of_B Babd) aL (onLine_3_of_B Babd aL bL) fL
    with ⟨e, eL, efL, eqtri⟩
  have eba_ebd : angle e b a = angle e b d := (sss rfl eqtri.2.2.2 ba_bd).2.1
  have rightangles : angle e b a = rightangle ∧ angle e b c = rightangle :=
    rightangle_of_angle_eq Babc aL (onLine_3_of_B Babc aL bL) eL $ eba_ebd.trans
    $ angle_extension_of_B_B (ne_of_online bL eL) Babc Babd
  refine ⟨e, efL, rightangles⟩

theorem B_of_three_col_ne (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (col_abc : Colinear a b c) :
    B a b c ∨ B b a c ∨ B a c b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact B_of_three_onLine_ne ab ac bc aL bL cL

theorem ne_of_sameside' (cL : OnLine c L) (abL : SameSide a b L) : c ≠ a :=
  ne_of_online cL $ not_onLine_of_sameSide abL

theorem B_or_B_of_sameside (bc : b ≠ c) (aL : OnLine a L) (col : Colinear a b c)
    (bcL : SameSide b c L) : B a b c ∨ B a c b := by
  rcases B_of_three_col_ne (ne_of_sameside' aL bcL) (ne_of_sameside' aL $ sameSide_symm bcL)
    bc col with Bet | Bet | Bet
  left; exact Bet; exfalso; exact not_sameSide13_of_B123_onLine2 Bet aL $ bcL; right; exact Bet

theorem angle_extension_of_sameside (ab : a ≠ b) (bL : OnLine b L)
    (col : Colinear b c d) (cdL : SameSide c d L) : angle c b a = angle d b a := by
  by_cases cd : c = d; rw [cd]
  rcases B_or_B_of_sameside cd bL col cdL with Bet | Bet; symm
  repeat exact symm $ angle_extension_of_B (Ne.symm ab) Bet

theorem ne_32_of_B (Babc : B a b c) : c ≠ b := Ne.symm $ ne_23_of_B Babc

theorem sameside_of_DiffSide_DiffSide (abL : DiffSide a b L) (acL : DiffSide a c L) :
    SameSide b c L := (or_iff_right acL.2.2).mp
  (sameSide_or_of_diffSide abL.1 abL.2.1 acL.2.1 abL.2.2)

theorem online_3_of_Triangle (aL : OnLine a L) (bL : OnLine b L) (tri_abc : Triangle a b c) :
    ¬OnLine c L := fun cL => tri_abc ⟨L, aL, bL, cL⟩

theorem tri231_of_tri123 (tri_abc : Triangle a b c) : Triangle b c a :=
  fun col => by rcases col with ⟨L, bL, cL, aL⟩; exact tri_abc ⟨L, aL, bL, cL⟩

theorem offline_of_B_offline (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bN : OnLine b N)
    (dN : OnLine d N) (dL : ¬OnLine d L) : ¬OnLine a N :=
  online_3_of_Triangle bN dN (tri231_of_tri123 $ Triangle_of_ne_online (ne_12_of_B Babc) aL bL dL)

theorem DiffSide_of_B_offline (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bN : OnLine b N)
    (dN : OnLine d N) (dL : ¬OnLine d L) : DiffSide a c N :=
  ⟨offline_of_B_offline Babc aL bL bN dN dL, offline_of_B_offline (B_symm Babc)
  (onLine_3_of_B Babc aL bL) bL bN dN dL, not_sameSide13_of_B123_onLine2 Babc bN⟩

theorem sameside_of_B_DiffSide_sameside (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (bM : OnLine b M) (eM : OnLine e M) (dM : ¬OnLine d M) (edL : SameSide e d L)
    (cdM : ¬SameSide c d M) : SameSide a d M :=
   sameSide_symm $ sameside_of_DiffSide_DiffSide ⟨offline_of_B_offline
    (B_symm Babc) (onLine_3_of_B Babc aL bL) bL bM eM $ not_onLine_of_sameSide edL, dM, cdM⟩ $
    DiffSide_symm $ DiffSide_of_B_offline Babc aL bL bM eM $ not_onLine_of_sameSide edL

theorem ne_line_of_online (bM : OnLine b M) (bL : ¬OnLine b L) : L ≠ M :=
  fun LM => by rw [←LM] at bM; exact bL bM

theorem angle_add_of_sameside (aL : OnLine a L) (bL : OnLine b L) (aM : OnLine a M)
    (cM : OnLine c M) (cdL : SameSide c d L) (bdM : SameSide b d M) :
    angle b a c = angle d a b + angle d a c := by
  linarith[angle_symm b a d, (angle_add_iff_sameSide (ne_of_sameside' aM bdM) (ne_of_sameside'
    aL cdL) aL bL aM cM (not_onLine_of_sameSide $ sameSide_symm bdM) (not_onLine_of_sameSide $
    sameSide_symm cdL) $ ne_line_of_online cM $ not_onLine_of_sameSide cdL).mpr ⟨bdM, cdL⟩]


theorem online_of_sameside_inter (ab : a ≠ b) (aL : OnLine a L) (aM : OnLine a M) (bL : OnLine b L)
    (cM : OnLine c M) (cdL : SameSide c d L) : ¬OnLine b M :=
  fun bM => (not_onLine_of_sameSide cdL) (by rwa [line_unique_of_pts ab aM bM aL bL] at cM)


theorem DiffSide_of_sameside_sameside (aL : OnLine a L) (aM : OnLine a M) (aN : OnLine a N)
    (bL : OnLine b L) (cM : OnLine c M) (dN : OnLine d N) (dcL : SameSide d c L)
    (bcN : SameSide b c N) : DiffSide b d M :=
  ⟨online_of_sameside_inter (ne_of_sameside' aN bcN) aL aM bL cM $ sameSide_symm dcL,
  online_of_sameside_inter (ne_of_sameside' aL dcL) aN aM dN cM $ sameSide_symm bcN,
  not_sameSide_of_sameSide_sameSide aL aM aN bL cM dN (sameSide_symm dcL) bcN⟩

theorem sameside_of_B_sameside_sameside (Babc : B a b c) (bL : OnLine b L) (bM : OnLine b M)
    (bN : OnLine b N) (aL : OnLine a L) (eM : OnLine e M) (dN : OnLine d N) (edL : SameSide e d L)
    (cdM : SameSide c d M) : SameSide a e N :=
  sameside_of_DiffSide_DiffSide (DiffSide_symm $ DiffSide_of_B_offline Babc aL bL bN dN $
  not_onLine_of_sameSide $ sameSide_symm edL) (DiffSide_of_sameside_sameside bL bN bM
  (onLine_3_of_B Babc aL bL) dN eM edL cdM)

/-- Euclid I.13, A generalization of I.11. Instead of requiring the angles to be perpendicular,
  they can be arbitrary -/
theorem two_right_of_flat_angle (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L)
    (dL : ¬OnLine d L) : angle d b a + angle d b c = 2 * rightangle := by
  rcases line_of_pts b d with ⟨N, bN, dN⟩
  rcases perpendicular_of_online Babc aL bL dL with ⟨e, edL, eba_ra, ebc_ra⟩
  rcases line_of_pts e b with ⟨M, eM, bM⟩
  by_cases dM : OnLine d M; linarith[angle_extension_of_sameside (ne_12_of_B Babc) bL
    ⟨M, bM, eM, dM⟩ edL, angle_extension_of_sameside (ne_32_of_B Babc) bL ⟨M, bM, eM, dM⟩ edL]
  wlog cdM : SameSide c d M generalizing a c; linarith[this (B_symm Babc) (onLine_3_of_B Babc aL
    bL) ebc_ra eba_ra $ sameside_of_B_DiffSide_sameside Babc aL bL bM eM dM edL cdM]
  have ebc_add : angle d b c = angle e b c - angle d b e :=
    by linarith[angle_add_of_sameside bM eM bL (onLine_3_of_B Babc aL bL) cdM edL]
  have dba_add : angle d b a = angle e b d + angle e b a := angle_add_of_sameside bN dN bL aL
    (sameside_of_B_sameside_sameside Babc bL bM bN aL eM dN edL cdM) (sameSide_symm edL)
  linperm

theorem online_2_of_Triangle (aL : OnLine a L) (cL : OnLine c L) (tri_abc : Triangle a b c) :
    ¬OnLine b L := fun bL => tri_abc ⟨L, aL, bL, cL⟩

theorem tri132_of_tri123 (tri_abc : Triangle a b c) : Triangle a c b :=
  fun col => by unfold Colinear at col; simp_rw [And.comm] at col; exact tri_abc col

theorem tri312 (tri_abc : Triangle a b c) : Triangle c a b :=
  tri231_of_tri123 $ tri231_of_tri123 $ tri_abc

theorem tri321 (tri_abc : Triangle a b c) : Triangle c b a := tri132_of_tri123 $ tri312 tri_abc

theorem offline_of_online_offline (bc : b ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (bM : OnLine b M) (cM : OnLine c M) (aM : ¬OnLine a M) : ¬OnLine c L :=
  online_2_of_Triangle aL bL $ tri321 $ Triangle_of_ne_online bc bM cM aM

theorem angle_zero_of_online (ab : a ≠ b) (ac : a ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (cL : OnLine c L) (Bbac : ¬B b a c) : angle b a c = 0 :=
  (angle_zero_iff_onLine ab ac aL bL).mp ⟨cL, Bbac⟩


theorem B_of_col_sameside (bL : OnLine b L) (acL : SameSide a c L) :
    ¬B a b c := fun Babc => not_sameSide13_of_B123_onLine2 Babc bL $ acL

lemma angle_zero_of_lt_eq (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (dcL : SameSide d c L)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a d with ⟨M, aM, dM⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  by_cases bcM : SameSide b c M
  · linarith[angle_add_of_sameside aL bL aM dM dcL bcM, angle_symm c a b]
  by_cases cM : OnLine c M
  · exact angle_zero_of_online (ne_of_sameside' aL $ sameSide_symm dcL) (ne_of_sameside' aL dcL)
      aM cM dM (B_of_col_sameside aL $ sameSide_symm dcL)
  · linarith[angle_symm b a d, angle_add_of_sameside aL bL aN cN (sameSide_symm dcL) $
      sameSide_of_sameSide_not_sameSide ab aL aM aN bL dM cN cM dcL bcM, angle_symm d a c]


theorem DiffSide_of_B_offline'' (Babc : B a b c) (aN : ¬OnLine a N) (bN : OnLine b N) :
    DiffSide a c N :=
  ⟨aN, fun cN => aN $ onLine_3_of_B (B_symm Babc) cN bN, not_sameSide13_of_B123_onLine2 Babc bN⟩


theorem sameside_of_B_DiffSide (Babc : B a b c) (bL : OnLine b L) (aeL : DiffSide a e L) :
    SameSide e c L := sameside_of_DiffSide_DiffSide aeL $ DiffSide_of_B_offline'' Babc aeL.1 bL

theorem online_of_angle_zero (ab : a ≠ b) (ac : a ≠ c) (aL : OnLine a L) (bL : OnLine b L)
    (bac_0 : angle  b a c = 0) : OnLine c L ∧ ¬B b a c :=
  (angle_zero_iff_onLine ab ac aL bL).mpr bac_0

theorem ne_of_DiffSide (abL : DiffSide a b L) : a ≠ b :=
  fun ab => by rw [ab] at abL; exact abL.2.2 $ sameSide_rfl_of_not_onLine abL.1

theorem ne_line_of_online' (bM : OnLine b M) (bL : ¬OnLine b L) : M ≠ L :=
  Ne.symm $ ne_line_of_online bM bL

theorem B_of_col_DiffSide (col_abc : Colinear a b c) (bL : OnLine b L)
    (acL : DiffSide a c L) : B a b c := by
  rcases col_abc with ⟨M, aM, bM, cM⟩; exact B_of_onLine_inter (ne_of_online' bL acL.1)
    (ne_of_online bL acL.2.1) (ne_of_DiffSide acL) (ne_line_of_online' aM acL.1) aM bM cM bL acL.2.2


/-- Euclid I.14, the converse of I.13. If angles add to two right angles then you have betweeness-/
theorem flat_of_two_right_angle (bd : b ≠ d) (bL : OnLine b L) (dL : OnLine d L)
    (acL : DiffSide a c L) (two_ra : angle d b a + angle d b c = 2 * rightangle) : B a b c := by
  rcases line_of_pts a b with ⟨N, aN, bN⟩
  rcases length_eq_B_of_ne (ne_of_online' bL acL.1) bd with ⟨e, Babe, -⟩
  have : angle d b a + angle d b e = 2 * rightangle := two_right_of_flat_angle Babe aN bN $
    offline_of_online_offline bd aN bN bL dL acL.1
  have ebc_0 : angle e b c = 0 := angle_zero_of_lt_eq bd bL dL
    (sameside_of_B_DiffSide Babe bL acL) (by linarith)
  have cN := online_of_angle_zero (ne_23_of_B Babe) (ne_of_online bL acL.2.1)
      bN (onLine_3_of_B Babe aN bN) ebc_0
  exact B_of_col_DiffSide ⟨N, aN, bN, cN.1⟩ bL acL


theorem online_of_eq (ab : a = b) (aL : OnLine a L) : OnLine b L := by rwa [ab] at aL

theorem ne_12_of_tri (tri: Triangle a b c) : a ≠ b :=
  fun ac => by rcases line_of_pts a c with ⟨L, aL, cL⟩; exact tri ⟨L, aL, online_of_eq ac aL, cL⟩

theorem ne_13_of_tri (tri : Triangle a b c) : a ≠ c :=
  fun ac => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq ac aL⟩

theorem diffSide_of_not_onLine' (aL : ¬OnLine a L) : ∃ b, DiffSide a b L := by
  rcases diffSide_of_not_onLine aL with ⟨b, bL, abL⟩; exact ⟨b, aL, bL, abL⟩

theorem pts_line_circle_of_not_sameside (aα : CenterCircle a α) (bα : OnCircle b α)
    (abL : ¬SameSide a b L) : ∃ c d, c ≠ d ∧
    OnLine c L ∧ OnLine d L ∧ OnCircle c α ∧ OnCircle d α :=
  pts_of_lineCircleInter $ lineCircleInter_of_not_sameSide abL
  (by right; exact inside_circle_of_center aα) $ by left; exact bα

theorem pt_inter_of_not_sameside (abL : ¬SameSide a b L) :
    ∃ c M, OnLine a M ∧ OnLine b M ∧ OnLine c M ∧ OnLine c L := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases pt_of_linesInter $ lines_inter_of_not_sameSide
    aM bM abL with ⟨c, cL, cM⟩; refine ⟨c, M, aM, bM, cM, cL⟩


theorem pt_B_of_DiffSide (abL : DiffSide a b L) : ∃ c, OnLine c L ∧ B a c b := by
  rcases pt_inter_of_not_sameside abL.2.2 with ⟨c, M, aM, bM, cM, cL⟩
  refine ⟨c, cL, B_of_onLine_inter (Ne.symm $ ne_of_online cL abL.1) (ne_of_online cL abL.2.1)
    (ne_of_DiffSide abL) (Ne.symm $ ne_line_of_online bM abL.2.1) aM cM bM cL abL.2.2⟩

theorem sas (ab_de : length a b = length d e) (ac_df : length a c = length d f)
    (Abac : angle b a c = angle e d f) : length b c = length e f ∧ angle a b c = angle d e f ∧
    angle a c b = angle d f e := ⟨(SAS_iff_SSS ab_de ac_df).1 Abac, (sss ab_de ((SAS_iff_SSS ab_de
  ac_df).1 Abac) ac_df).1, (sss ab_de ((SAS_iff_SSS ab_de ac_df).1 Abac) ac_df).2.2⟩


theorem ne_23_of_tri (tri: Triangle a b c) : b ≠ c :=
  fun bc => by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq bc bL⟩

theorem B_of_length_eq_col (ab : a ≠ b) (ac : a ≠ c) (col_abc : Colinear a b c)
    (ab_cb : length a b = length c b) : B a b c := by
  rcases B_of_three_col_ne ab ac (ne_of_ne_len ab $ by linperm) col_abc
    with Babc | Bet | Bet; exact Babc; repeat {linperm[length_sum_perm_of_B Bet]}


theorem eq_of_length_zero (ab_0 : length a b = 0) : a = b := (length_eq_zero_iff).mp ab_0

theorem length_zero_of_eq (ab : a = b) : length a b = 0 := (length_eq_zero_iff).mpr ab

theorem ne_of_Triangle_length_eq (tri_abc : Triangle a b c) (bd_cd : length b d = length c d) :
    b ≠ d := fun bd => ne_23_of_tri tri_abc $ bd.trans (eq_of_length_zero $ bd_cd.symm.trans $
      length_zero_of_eq bd).symm

/-- Euclid I.10, bisecting a segment -/
theorem bisect_segment (ab : a ≠ b) : ∃ e, B a e b ∧ length a e = length b e := by
  rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c, d, L, aL, bL, cdL, eqtri_abc, eqtri_abd⟩
  rcases pt_B_of_DiffSide cdL with ⟨e, eL, Bced⟩
  have acd_bcd : angle a c d = angle b c d := (sss (by perma[eqtri_abc.2.2.2]) rfl $
    by perma[eqtri_abd.2.2.2]).1
  have ae_be : length a e = length b e := (sas eqtri_abc.2.2.2 rfl $ by
    linperm[angle_extension_of_B (Ne.symm $ ne_13_of_tri eqtri_abc.1) Bced,
    angle_extension_of_B (Ne.symm $ ne_23_of_tri eqtri_abc.1) Bced]).1
  refine ⟨e, B_of_length_eq_col (ne_of_Triangle_length_eq
    (tri312 eqtri_abc.1) ae_be) ab ⟨L, aL, eL, bL⟩ ae_be, ae_be⟩


/-- Euclid I.12, Obtaining perpendicular angles from a point off a line -/
theorem perpendicular_of_not_online (aL : ¬OnLine a L) : ∃ c d e, B c e d ∧ OnLine c L ∧ OnLine d L
    ∧ OnLine e L ∧ angle a e c = rightangle ∧ angle a e d = rightangle := by
  rcases diffSide_of_not_onLine' aL with ⟨b, abL⟩
  rcases circle_of_ne (ne_of_DiffSide abL) with ⟨α, aα, bα⟩
  rcases pts_line_circle_of_not_sameside aα bα abL.2.2 with ⟨c, d, cd, cL, dL, cα, dα⟩
  rcases bisect_segment cd with ⟨e, Bced, ce_de⟩
  have aec_aed : angle a e c = angle a e d := (sss (length_eq_of_oncircle aα cα dα) ce_de rfl).2.2
  have rightangles : angle a e c = rightangle ∧ angle a e d = rightangle :=
    rightangle_of_angle_eq Bced cL dL aL aec_aed
  refine ⟨c, d, e, Bced, cL, dL, onLine_2_of_B Bced cL dL, rightangles⟩

theorem online_1_of_Triangle (bL : OnLine b L) (cL : OnLine c L) (tri_abc : Triangle a b c) :
    ¬OnLine a L := fun aL => tri_abc ⟨L, aL, bL, cL⟩

lemma right_of_online_right (bd : b ≠ d) (tri_abc : Triangle a b c) (bL : OnLine b L) (cL :
    OnLine c L) (dL : OnLine d L) (abd : angle a b d = rightangle) : angle a b c = rightangle := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩
  by_cases cdM : SameSide c d M;
    linperm[angle_extension_of_sameside (ne_12_of_tri tri_abc) bM ⟨L, bL, cL, dL⟩ cdM]
  linperm[two_right_of_flat_angle (B_of_col_DiffSide ⟨L, cL, bL, dL⟩ bM ⟨online_3_of_Triangle aM
    bM tri_abc, offline_of_online_offline bd aM bM bL dL $ online_1_of_Triangle bL cL tri_abc,
    cdM⟩) cL bL (online_1_of_Triangle bL cL tri_abc)]

theorem ne_32_of_tri (tri : Triangle a b c) : c ≠ b := fun cb => (ne_23_of_tri tri) cb.symm

theorem iseqtri_of_ne (ab : a ≠ b) : ∃ c, EqTri a b c :=
  by rcases iseqtri_iseqtri_DiffSide_of_ne ab with ⟨c, -, -, -, -, -, eqtri, -⟩; exact ⟨c, eqtri⟩

theorem incirc_of_lt (aα : CenterCircle a α) (bα : OnCircle b α)
    (ac_ab : length a c < length a b) : InCircle c α := (in_circle_iff_length_lt aα bα).mp ac_ab


theorem B_circ_out_of_B (ab : a ≠ b) (Bacd : B a c d) (ab_ac : length a b = length a c) :
    ∃ e α, B a b e ∧ CenterCircle a α ∧ OnCircle d α ∧ OnCircle e α := by
  rcases circle_of_ne (ne_13_of_B Bacd) with ⟨α, aα, dα⟩;
  rcases pt_oncircle_of_inside_ne ab (incirc_of_lt aα dα (by linarith[length_sum_perm_of_B Bacd] :
  length a b < length a d)) with ⟨e, Babe, eα⟩; exact ⟨e, α, Babe, aα, dα, eα⟩

theorem ne_31_of_tri (tri : Triangle a b c) : c ≠ a := fun ca => (ne_13_of_tri tri) ca.symm

theorem length_eq_of_B_B (Bdbe: B d b e) (Bdaf : B d a f) (da_db : length d a = length d b)
    (de_df : length d e = length d f):
length a f = length b e := by linarith[length_sum_perm_of_B Bdbe, length_sum_perm_of_B Bdaf]


theorem length_eq_of_ne (a : Point) (bc : b ≠ c) : ∃ f, length a f = length b c := by
  by_cases ab : a = b; rw [ab]; exact ⟨c, rfl⟩
  rcases iseqtri_of_ne ab with ⟨d, eqtri⟩
  rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩
  rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩
  have be_bc := (length_eq_of_oncircle bα cα eα).symm
  have de_df := length_eq_of_oncircle dβ eβ fβ
  have af_be := length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 de_df
  exact ⟨f, af_be.trans be_bc⟩

theorem ne_of_ne_len' (cd : c ≠ d) (ab_cd : length a b = length c d) : a ≠ b :=
  ne_of_ne_len cd (ab_cd.symm)

theorem length_eq_B_of_ne_four (ab : a ≠ b) (cd : c ≠ d) :
    ∃ f, B a b f ∧ length c d = length b f := by
rcases length_eq_of_ne b cd with ⟨e, be_cd⟩
rcases length_eq_B_of_ne ab (ne_of_ne_len' cd be_cd) with ⟨f, Babf, be_bf⟩
exact ⟨f, Babf, by linarith⟩

theorem online_of_B_online (Babc : B a b c) (aL : OnLine a L) (cL : ¬OnLine c L) : ¬OnLine b L :=
  fun bL => cL (onLine_3_of_B Babc aL bL)

theorem sameside_of_B_online_3 (Babc : B a b c) (aL : OnLine a L) (cL : ¬OnLine c L) :
    SameSide b c L := sameSide_of_B_not_onLine_2 Babc aL $ online_of_B_online Babc aL cL

theorem nonzero_angle_of_offline (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (cL : ¬OnLine c L) : angle c a b ≠ 0 :=
  fun bac_0 => cL ((angle_zero_iff_onLine ab (ne_of_online aL cL) aL bL).mpr (by perma[bac_0])).1

theorem zero_lt_angle_of_offline (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L)
    (cL : ¬OnLine c L) : 0 < angle c a b :=
  lt_of_le_of_ne (angle_nonneg c a b) $ Ne.symm $ nonzero_angle_of_offline ab aL bL cL

theorem angle_lt_of_B_tri (Bcdb : B c d b) (tri_abc : Triangle a b c) :
    angle c a d < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases line_of_pts a c with ⟨M, aM, cM⟩
  have ang_split := angle_add_of_sameside aM cM aL bL (sameSide_symm $ sameside_of_B_online_3 Bcdb
    cM (online_2_of_Triangle aM cM tri_abc)) $ sameSide_symm $ sameside_of_B_online_3 (B_symm Bcdb)
    bL $ online_3_of_Triangle aL bL tri_abc
  linarith[angle_symm d a c, zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL bL (fun dL =>
    (online_3_of_Triangle aL bL tri_abc) $ onLine_3_of_B (B_symm Bcdb) bL dL)]

theorem tri_143_of_tri_col (ad : a ≠ d) (tri_abc : Triangle a b c) (col_abd : Colinear a b d) :
    Triangle a d c := fun col_adc => by rcases col_abd with ⟨L, aL, bL, dL⟩; exact tri_abc
                                          ⟨L, aL, bL, online_of_col_online ad aL dL col_adc⟩

theorem col_of_B (Babc : B a b c) : Colinear a b c := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact ⟨L, aL, bL, onLine_3_of_B Babc aL bL⟩

theorem angle_eq_of_iso (iso_abc : IsoTri a b c) : angle a b c = angle a c b :=
  (sas (iso_abc).2 (iso_abc).2.symm $ by perm).2.2.symm


theorem col_213_of_col (col_123 : Colinear a b c) : Colinear b a c := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, bL, aL, cL⟩

theorem B_oncircle_of_inside_outside (a_in_α : InCircle a α) (b_out_α : OutCircle b α) :
    ∃ c, B a c b ∧ OnCircle c α := pt_on_circle_of_inside_outside b_out_α.1 a_in_α b_out_α.2

theorem on_circle_of_oncircle_length (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_ac : length a b ≠ length a c) : ¬OnCircle c α :=
  fun cα => ab_ac (length_eq_of_oncircle aα bα cα)


theorem incircle_of_on_circle_length (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_ac : length a b ≤ length a c) : ¬InCircle c α :=
fun c_in_α => by linarith[(in_circle_iff_length_lt aα bα).mpr c_in_α]


theorem OutCircle_of_lt (aα : CenterCircle a α) (bα : OnCircle b α)
    (ab_lt_ac : length a b < length a c) : OutCircle c α := ⟨on_circle_of_oncircle_length aα bα
  (by linarith), incircle_of_on_circle_length aα bα (by linarith)⟩


theorem B_length_eq_of_ne_lt (cd : c ≠ d) (cd_lt_ab : length c d < length a b) :
    ∃ f, B a f b ∧ length a f = length c d := by
rcases length_eq_of_ne a cd with ⟨e, ae_cd⟩
rcases circle_of_ne (ne_of_ne_len' cd ae_cd) with ⟨α, aα, eα⟩
rcases B_oncircle_of_inside_outside (inside_circle_of_center aα)
  (OutCircle_of_lt aα eα (by rwa [← ae_cd] at cd_lt_ab)) with ⟨f, Bafb, fα⟩
have ae_af := length_eq_of_oncircle aα eα fα
exact ⟨f, Bafb, by linarith⟩

theorem ne_of_col_tri (col_abc : Colinear a b c) (tri_acd : Triangle d a c) : d ≠ b := by
  rcases col_abc with ⟨L, aL, bL, cL⟩; exact ne_of_online' bL $ online_1_of_Triangle aL cL tri_acd

theorem ne_of_col_tri' (col_abc : Colinear a b c) (tri_acd : Triangle d a c) : b ≠ d :=
  Ne.symm $ ne_of_col_tri col_abc tri_acd

theorem vertical_angle (Babc : B a b c) (Bdbe : B d b e) (aL : OnLine a L) (bL : OnLine b L)
    (dL : ¬OnLine d L) : angle a b d = angle c b e := by
  rcases line_of_pts d b with ⟨M, dM, bM⟩
  have dba_dbc : angle d b a + angle d b c = 2 * rightangle := two_right_of_flat_angle Babc aL bL dL
  have cbd_cbe : angle c b d + angle c b e = 2 * rightangle := two_right_of_flat_angle Bdbe dM bM $
    offline_of_online_offline (ne_23_of_B Babc) dM bM bL (onLine_3_of_B Babc aL bL) dL
  linperm


theorem vertical_angle' (Babc : B a b c) (Bdbe : B d b e) (col_abd : ¬Colinear a b d) :
    angle a b d = angle c b e := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact vertical_angle Babc Bdbe aL bL $ online_3_of_Triangle aL bL col_abd

theorem col_312 (col : Colinear a b c) : Colinear c a b := by
  rcases col with ⟨L, aL, bL, cL⟩; exact ⟨L, cL, aL, bL⟩

theorem tri_of_B_tri (Babc : B a b c) (tri_acd : Triangle d a c) : Triangle d b c :=
  tri321 $ tri_143_of_tri_col (ne_32_of_B Babc) (tri321 tri_acd) $ col_312 $ col_of_B Babc

theorem DiffSide_of_B_offline' (Babc : B a b c) (bL : OnLine b L) (aL : ¬OnLine a L) :
    DiffSide a c L :=
  ⟨aL, fun cL => aL $ onLine_3_of_B (B_symm Babc) cL bL, not_sameSide13_of_B123_onLine2 Babc bL⟩


theorem sameside_of_B_B (Babc : B a b c) (Bade : B a d e) (bL : OnLine b L) (dL : OnLine d L)
    (aL : ¬OnLine a L) : SameSide c e L :=
  sameside_of_DiffSide_DiffSide (DiffSide_of_B_offline' Babc bL aL) $ DiffSide_of_B_offline'
    Bade dL aL

theorem tri_of_B_B_base_tri (Bade : B a d e) (Bbdc : B b d c) (tri_abc : Triangle a b c) :
    Triangle a e b := tri_143_of_tri_col (ne_13_of_B Bade) (tri_of_B_tri (B_symm Bbdc) $
  tri132_of_tri123 tri_abc) (col_of_B Bade)


theorem offline_of_B_B_tri (Bade : B a d e) (Bbdc : B b d c) (aL : OnLine a L) (bL : OnLine b L)
    (tri_abc : Triangle a b c) : ¬OnLine e L :=
  fun eL => tri_of_B_B_base_tri Bade Bbdc tri_abc $ ⟨L, aL, eL, bL⟩


theorem internal_lt_external (Babc : B a b c) (tri_abd : Triangle a b d) :
    angle b d a < angle d b c := by
  rcases bisect_segment (ne_23_of_tri tri_abd) with ⟨e, Bbed, be_de⟩
  rcases col_of_B Bbed with ⟨L, bL, eL, dL⟩
  rcases col_of_B Babc with ⟨M, aM, bM, cM⟩
  rcases length_eq_B_of_ne (ne_of_col_tri ⟨L, bL, eL, dL⟩ tri_abd) (ne_of_col_tri' ⟨L, bL, eL, dL⟩
    tri_abd) with ⟨f, Baef, ea_ef⟩
  have aed_feb : angle a e d = angle f e b := vertical_angle' Baef (B_symm Bbed) $ tri_of_B_tri
    Bbed tri_abd
  have eda_ebf : angle e d a = angle e b f := (sas ea_ef (by perm; exact be_de.symm) aed_feb).2.2
  have ebc_split : angle e b c = angle f b e + angle f b c := angle_add_of_sameside bL eL bM cM
    (sameside_of_B_B Babc Baef bL eL $ online_1_of_Triangle bL dL tri_abd) $ sameside_of_B_online_3
    Baef aM $ offline_of_B_B_tri Baef Bbed aM bM tri_abd
  linperm[zero_lt_angle_of_offline (ne_23_of_B Babc) bM cM $ offline_of_B_B_tri Baef Bbed aM bM
    tri_abd, angle_extension_of_B (ne_23_of_B Babc) Bbed, angle_extension_of_B (ne_31_of_tri
    tri_abd) (B_symm Bbed)]

theorem tri213 (tri_abc : Triangle a b c) : Triangle b a c :=
  tri132_of_tri123 $ tri231_of_tri123 $ tri_abc


theorem internal_lt_external' (Babc : B a b c) (tri_abd : Triangle a b d) :
    angle b a d < angle d b c := by
  rcases length_eq_B_of_ne (ne_32_of_tri tri_abd) (ne_23_of_tri tri_abd) with ⟨e, Bdbe, -⟩
  have : angle b a d < angle a b e := internal_lt_external Bdbe (by perma)
  have : angle e b a = angle d b c := vertical_angle' (B_symm Bdbe) Babc $ tri213 $
    tri_143_of_tri_col (ne_23_of_B Bdbe) (by perma) $ col_213_of_col $ col_of_B Bdbe
  linperm

theorem ne_21_of_tri (tri : Triangle a b c) : b ≠ a := Ne.symm $ ne_12_of_tri tri


theorem ang_lt_of_len_lt (tri_abc : Triangle a b c) (len_lt : length c a < length c b) :
    angle c b a < angle c a b := by
  rcases B_length_eq_of_ne_lt (ne_31_of_tri tri_abc) len_lt with ⟨d, Bcdb, cd_ca⟩
  have : angle d b a < angle a d c := internal_lt_external' (B_symm Bcdb) $ tri321 $ tri_of_B_tri
    Bcdb $ tri132_of_tri123 tri_abc
  have : angle c a d = angle c d a := angle_eq_of_iso ⟨tri312 $ tri_of_B_tri (B_symm Bcdb) tri_abc,
    cd_ca.symm⟩
  have : angle c a d < angle c a b := angle_lt_of_B_tri Bcdb tri_abc
  linarith[angle_extension_of_B (ne_21_of_tri tri_abc) $ B_symm Bcdb, angle_symm c d a]


theorem len_lt_of_ang_lt (tri_abc : Triangle a b c) (ang_lt : angle c b a < angle c a b) :
    length c a < length c b := by
  push_contra cb_le_ca at cb_le_ca
  by_cases cb_ca : length c b = length c a
  · linarith[angle_eq_of_iso ⟨by perma, cb_ca.symm⟩]
  linarith[ang_lt_of_len_lt (by perma) $ lt_of_le_of_ne cb_le_ca cb_ca]

theorem col_132_of_col (col_123 : Colinear a b c) : Colinear a c b := by
  rcases col_123 with ⟨L, aL, bL, cL⟩; exact ⟨L, aL, cL, bL⟩


theorem len_lt_of_tri' (tri_abc : Triangle a b c) : length a b < length a c + length b c := by
  rcases length_eq_B_of_ne_four (ne_13_of_tri tri_abc) (ne_23_of_tri tri_abc) with ⟨d, Bacd, bc_cd⟩
  have : angle d b c < angle d b a := angle_lt_of_B_tri (B_symm Bacd) $ tri312 $ tri_143_of_tri_col
    (ne_13_of_B Bacd) (by perma) $ col_of_B Bacd
  have : angle c d b = angle c b d := angle_eq_of_iso ⟨tri_143_of_tri_col (ne_23_of_B Bacd)
    (by perma) $ col_213_of_col $ col_of_B Bacd, by perma[bc_cd.symm]⟩
  have : length a b < length a d := len_lt_of_ang_lt (tri321 $ tri_143_of_tri_col (ne_13_of_B Bacd)
    (tri132_of_tri123 tri_abc) $ col_of_B Bacd) $
    by linarith[angle_symm c b d, angle_symm d b a, angle_extension_of_B (ne_of_col_tri'
    (col_132_of_col $ col_of_B Bacd) $ tri213 tri_abc) $ B_symm Bacd]
  have : length a c + length c d = length a d := length_sum_of_B Bacd
  linarith

theorem len_lt_of_tri (tri_abc : Triangle a b c) : length a b < length a c + length b c ∧
    length b c < length b a + length c a ∧ length c a < length c b + length a b :=
  ⟨len_lt_of_tri' tri_abc, len_lt_of_tri' $ by perma, len_lt_of_tri' $ by perma⟩

theorem ne_of_oncircle (aα : OnCircle a α) (bα : ¬OnCircle b α) : a ≠ b :=
  fun ab => bα $ by rwa [ab] at aα

theorem B_or_B_of_circ_pt (ab : a ≠ b) (aα : CenterCircle a α) (bα : ¬OnCircle b α):
    ∃ c, (B a c b ∨ B a b c) ∧ OnCircle c α := by
  rcases pt_oncircle_of_inside_ne ab.symm $ inside_circle_of_center aα with ⟨d, Bbad, -⟩
  rcases pt_oncircle_of_inside_ne (ne_32_of_B Bbad) $ inside_circle_of_center aα with ⟨c, Bdac, cα⟩
  exact ⟨c, B_or_B_of_B_B (ne_of_oncircle cα bα) Bdac $ B_symm Bbad, cα⟩


theorem in_circle_of_lt_lt (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (cα : OnCircle c α) (dβ : OnCircle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : ∃ e, OnCircle e α ∧ InCircle e β := by
  by_cases bα : OnCircle b α; exact ⟨b, bα, inside_circle_of_center bβ⟩
  rcases B_or_B_of_circ_pt (mt length_eq_zero_iff.mpr $ by linarith[abs_lt.mp lt_cen]) aα bα with
   ⟨e, Bet, eα⟩
  rcases Bet with Bet | Bet
  repeat exact
    ⟨e, eα, incirc_of_lt bβ dβ $ by linarith[length_sum_of_B Bet, length_eq_of_oncircle aα cα eα,
                            abs_lt.mp lt_cen, length_symm e b]⟩

theorem circint_of_lt_lt (aα : CenterCircle a α) (bβ : CenterCircle b β)
    (cα : OnCircle c α) (dβ : OnCircle d β) (lt_cen : |length a c - length b d| < length a b)
    (cen_lt : length a b < length a c + length b d) : CirclesInter α β := by
  rcases in_circle_of_lt_lt aα bβ cα dβ lt_cen cen_lt with ⟨e, eα, eβ⟩
  rcases in_circle_of_lt_lt bβ aα dβ cα (by rw[abs_lt]; constructor; repeat
    linperm[abs_lt.mp lt_cen]) $ by linperm with ⟨f, fβ, fα⟩
  exact circlesInter_of_inside_on_circle eα fβ fα eβ

theorem Triangle_of_ineq (aL : OnLine a L) (bL : OnLine b L) (fL : ¬OnLine f L)
    (ab_lt_a1a2_b1b2 : length a b < length a1 a2 + length b1 b2)
    (a1a2_lt_ab_b1b2 : length a1 a2 < length a b + length b1 b2)
    (b1b2_lt_a1a2_ab : length b1 b2 < length a1 a2 + length a b) :
    ∃ e, length a e = length a1 a2 ∧ length b e = length b1 b2 ∧ SameSide e f L := by
  rcases length_eq_B_of_ne_four (Ne.symm (fun n => by linarith[length_zero_of_eq n] : a ≠ b))
    ((fun n => by linarith[length_zero_of_eq n] : a1 ≠ a2)) with ⟨c, Bbac, a1a2_ac⟩
  rcases length_eq_B_of_ne_four (fun n => by linarith[length_zero_of_eq n] : a ≠ b)
    ((fun n => by linarith[length_zero_of_eq n] : b1 ≠ b2)) with ⟨d, Babd, b1b2_bd⟩
  rcases circle_of_ne $ ne_23_of_B Bbac with ⟨α, aα, cα⟩
  rcases circle_of_ne $ ne_23_of_B Babd with ⟨β, bβ, dβ⟩
  rcases pt_sameSide_of_circlesInter aL bL fL aα bβ $ circint_of_lt_lt aα bβ cα dβ
    (by apply abs_lt.mpr; exact ⟨by linarith, by linarith⟩) $ by linarith with ⟨e, efL, eα, eβ⟩
  have : length a c = length a e := length_eq_of_oncircle aα cα eα
  have : length b d = length b e := length_eq_of_oncircle bβ dβ eβ
  exact ⟨e, by linarith, by linarith, efL⟩

theorem angle_extension_of_B' (ac : a ≠ c) (Babb1 : B a b b1) : angle c a b = angle c a b1 :=
  by perma[angle_extension_of_B ac Babb1]

theorem angle_copy (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (jL : ¬OnLine j L)
    (tri_cde : Triangle c d e) : ∃ h, angle h a b = angle e c d ∧ SameSide h j L := by
  rcases length_eq_B_of_ne_four ab (ne_12_of_tri tri_cde) with ⟨g, Babg, cd_bg⟩
  rcases length_eq_B_of_ne_four (ne_12_of_tri tri_cde) ab with ⟨f, Bcdf, ab_df⟩
  have cf_ag : length c f = length a g := by linarith[length_sum_of_B Babg, length_sum_of_B Bcdf]
  have ⟨cf_lt_ce_ef, _, _⟩ := len_lt_of_tri $ tri_143_of_tri_col (ne_13_of_B
    Bcdf) tri_cde $ col_of_B Bcdf; perm only [length] at *
  rcases Triangle_of_ineq aL (onLine_3_of_B Babg aL bL) jL (by rwa [cf_ag] at cf_lt_ce_ef) (by
    linarith) $ by linarith with ⟨h, ah_ce, gh_ef, hjL⟩
  have : angle h a g = angle e c f := (sss ah_ce (by perma[gh_ef]) cf_ag.symm).2.1
  exact ⟨h, by linarith[angle_extension_of_B' (ne_of_sameside' aL hjL) Babg, angle_extension_of_B'
                (ne_13_of_tri tri_cde) Bcdf], hjL⟩


theorem angle_copy' (ab : a ≠ b) (aL : OnLine a L) (bL : OnLine b L) (jL : ¬OnLine j L)
    (tri_cde : Triangle c d e) : ∃ h, angle h a b = angle e c d ∧ DiffSide h j L := by
  rcases diffSide_of_not_onLine jL with ⟨f, fL, jfL⟩
  rcases angle_copy ab aL bL fL tri_cde with ⟨h, hab_ecd, hfL⟩
  refine ⟨h, hab_ecd, DiffSide_of_sameside_DiffSide (sameSide_symm hfL) $ DiffSide_symm
    ⟨jL, fL, jfL⟩⟩

theorem offline_of_online_inter (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (aL : ¬OnLine a L) (dL : ¬OnLine d L)
    (eM : OnLine e M) (eN : OnLine e N) : ¬OnLine e L :=
  offline_of_online_offline (ne_of_online' eM $ offline_of_online_offline bc aM bM bL cL aL) bL cL
    cN eN $ offline_of_online_offline bc.symm dN cN cL bL dL

theorem Para_of_ang_eq (bc : b ≠ c) (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : DiffSide a d L)
    (cba_bcd : angle c b a = angle b c d) : Para M N := by
  intro e; push_contra eMN at eMN
  wlog aeL : SameSide a e L generalizing a b c d e M N; exact this bc.symm dN cN cL bL bM aM (by
    perma) (by linperm) e (by tauto) $ sameside_of_DiffSide_DiffSide adL ⟨adL.1,
    offline_of_online_inter bc aM bM bL cL cN dN adL.1 adL.2.1 eMN.1 eMN.2, aeL⟩
  have : angle c b e < angle b c d := internal_lt_external (B_of_col_DiffSide ⟨N, eMN.2, cN, dN⟩ cL
    $ DiffSide_of_sameside_DiffSide aeL adL) $ by perma[Triangle_of_ne_online bc bL cL $
                not_onLine_of_sameSide $ sameSide_symm aeL]
  linperm[angle_extension_of_sameside bc.symm bL ⟨M, bM, aM, eMN.1⟩ aeL]


theorem Para_of_offline (aM : ¬OnLine a M) : ∃ N, OnLine a N ∧ Para M N := by
  rcases online_ne_of_line M with ⟨b, c, bc, bM, cM⟩
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases angle_copy' (ne_of_online' bM aM) aL bL (offline_of_online_offline bc aL bL bM cM aM)
    (Triangle_of_ne_online bc bM cM aM) with ⟨d, bad_abc, cdL⟩; perm at *
  rcases line_of_pts a d with ⟨N, aN, dN⟩
  refine ⟨N, aN, Para_of_ang_eq (ne_of_online bM aM) cM bM bL aL aN dN cdL bad_abc.symm⟩

theorem sameside_online_of_DiffSide (dM : OnLine d M) (aM : OnLine a M) (aL : OnLine a L)
    (cdL : DiffSide c d L) : ∃ b, OnLine b M ∧ SameSide b c L := by
  rcases circle_of_ne (ne_of_online aL cdL.2.1) with ⟨α, acen, _⟩
  rcases pt_oncircle_of_inside_ne (ne_of_online aL cdL.2.1).symm (inside_circle_of_center acen)
    with ⟨b, Bdab, _⟩
  exact ⟨b, onLine_3_of_B Bdab dM aM, by perma[sameside_of_B_DiffSide Bdab aL (DiffSide_symm cdL)]⟩


theorem sameside_of_offline (bL : OnLine b L) (cL : ¬OnLine c L) (bM : ¬OnLine b M)
    (eL : OnLine e L) (eM : OnLine e M) : ∃ d, OnLine d M ∧ SameSide d c L := by
  rcases online_ne_of_line M with ⟨a, d, ad, aM, dM⟩
  wlog dL : ¬OnLine d L generalizing a d L; exact this bL cL eL d a ad.symm dM aM $
    offline_of_online_offline ad.symm bL (of_not_not dL) dM aM bM
  by_cases dcL : SameSide d c L; exact ⟨d, dM, dcL⟩
  exact sameside_online_of_DiffSide dM eM eL ⟨cL, dL, not_sameSide_symm dcL⟩

theorem ne_of_sameside (bL : OnLine b L) (acL : SameSide a c L) : a ≠ b :=
  (ne_of_online bL (not_onLine_of_sameSide acL)).symm

theorem DiffSide_of_B_sameside (Bcad : B c a d) (aL : OnLine a L) (ceL : SameSide c e L) :
    DiffSide d e L :=
  DiffSide_symm $ DiffSide_of_sameside_DiffSide ceL $ DiffSide_of_B_offline' Bcad aL $
    not_onLine_of_sameSide ceL

theorem length_eq_of_sameside (aL : OnLine a L) (bL : ¬OnLine b L) (aM : ¬OnLine a M)
    (dL : OnLine d L) (dM : OnLine d M) : ∃ e, OnLine e M ∧ DiffSide e b L ∧
    length e d = length a b := by
  rcases sameside_of_offline aL bL aM dL dM with ⟨f, fM, fbL⟩
  rcases length_eq_B_of_ne_four (ne_of_sameside dL fbL) (ne_of_online aL bL) with ⟨e, Bfde, ab_de⟩
  exact ⟨e, onLine_3_of_B Bfde fM dM, DiffSide_of_B_sameside Bfde dL fbL, by perma[ab_de.symm]⟩

theorem offline_of_Para (aM : OnLine a M) (ParaMN : Para M N) : ¬OnLine a N := by
  have := ParaMN a; tauto

theorem Para_symm (ParaMN : Para M N) : Para N M := fun e => by have := ParaMN e; tauto

theorem offline_of_Para' (aN : OnLine a N) (ParaMN : Para M N) : ¬OnLine a M := by
  have := ParaMN a; tauto

theorem ne_of_Para (aM : OnLine a M) (bN : OnLine b N) (ParaMN : Para M N) : a ≠ b :=
  ne_of_online aM $ offline_of_Para' bN ParaMN

theorem not_Para_of_inter (aM : OnLine a M) (aN : OnLine a N) : ¬Para M N := by
  intro ParaMN; have := ParaMN a; tauto

theorem alternate_eq_of_Para (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : DiffSide a d L)
    (ParaMN : Para M N) : angle a b c = angle b c d := by
  wlog bcd_lt_abc : angle b c d < angle a b c generalizing a b c d M N; by_cases angle a b c =
    angle b c d; exact h; push_neg at bcd_lt_abc; linperm[this dN cN cL bL bM aM (by perma)
    (Para_symm ParaMN) $ by linperm[lt_of_le_of_ne bcd_lt_abc h]]
  rcases length_eq_B_of_ne (ne_of_online' bL adL.1) (ne_of_online bL adL.1) with ⟨e, Babe, -⟩
  have : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_Para' cN ParaMN
  have : angle c b e + angle b c d < 2 * rightangle := by perm at *; linarith
  rcases unparallel_postulate (ne_of_Para bM cN ParaMN) (onLine_3_of_B Babe aM bM) bM bL cL cN dN
    (sameSide_symm $ sameside_of_B_DiffSide Babe bL adL) (by perma) with ⟨f, fM, fN, -⟩
  exfalso; exact not_Para_of_inter fM fN ParaMN

theorem interior_rightangles_of_Para (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L)
    (cL : OnLine c L) (cN : OnLine c N) (dN : OnLine d N) (adL : SameSide a d L)
    (ParaMN : Para M N) : angle a b c + angle b c d = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_of_sameside bL adL) (ne_of_sameside' bL adL) with ⟨e, Babe, -⟩
  have ras : angle c b a + angle c b e = 2 * rightangle :=
    two_right_of_flat_angle Babe aM bM $ offline_of_Para' cN ParaMN
  have : angle e b c = angle b c d := alternate_eq_of_Para (onLine_3_of_B Babe aM bM) bM bL cL
    cN dN (DiffSide_of_B_sameside Babe bL adL) ParaMN
  linperm

theorem correspond_of_Para (Babc : B a b c) (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M)
    (dM : OnLine d M) (cN : OnLine c N) (eN : OnLine e N) (deL : SameSide d e L)
    (ParaMN : Para M N) : angle a b d = angle b c e := by
  have : angle a b d + angle d b c = 2 * rightangle :=
    by perma[two_right_of_flat_angle Babc aL bL (not_onLine_of_sameSide deL)]
  have : angle d b c + angle b c e = 2 * rightangle :=
    interior_rightangles_of_Para dM bM bL (onLine_3_of_B Babc aL bL) cN eN deL ParaMN
  linarith

theorem sameside_of_sameside_DiffSide (aL : OnLine a L) (aM : OnLine a M) (aN : OnLine a N)
    (bL : OnLine b L) (cM : OnLine c M) (dN : OnLine d N) (cdL : SameSide c d L)
    (bdM : DiffSide b d M) : SameSide b c N :=
  sameSide_of_sameSide_not_sameSide (ne_of_online aM bdM.1) aL aM aN bL cM dN bdM.2.1 cdL bdM.2.2

theorem pt_of_online_not_sameside (aL : OnLine a L) (bL : OnLine b L) (abM : ¬SameSide a b M) :
    ∃ c, OnLine c M ∧ OnLine c L := pt_of_linesInter $ lines_inter_of_not_sameSide aL bL abM


theorem sameside_of_Para_online (aM : OnLine a M) (bM : OnLine b M) (ParaMN : Para M N) :
    SameSide a b N := by
  by_contra abO; rcases pt_of_online_not_sameside aM bM abO with ⟨c, cN, cM⟩
  exact not_Para_of_inter cM cN ParaMN

theorem ext_int_sum_of_tri (Bbcd : B b c d) (tri_abc : Triangle a b c) : angle a c d = angle b a c +
    angle a b c ∧ angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  rcases line_of_pts a c with ⟨N, aN, cN⟩
  rcases line_of_pts c d with ⟨O, cO, dO⟩
  rcases Para_of_offline (online_3_of_Triangle aL bL tri_abc) with ⟨M, cM, ParaLM⟩
  rcases length_eq_of_sameside aN (online_2_of_Triangle aN cN tri_abc) (offline_of_Para aL ParaLM)
    cN cM with ⟨e, eM, ebN, _⟩
  have bac_ace := alternate_eq_of_Para bL aL aN cN cM eM (by perma[ebN]) ParaLM
  have dce_cba := correspond_of_Para (B_symm Bbcd) dO cO cM eM bL aL (sameside_of_sameside_DiffSide
    cM cN cO eM aN (onLine_3_of_B (B_symm Bbcd) dO cO) (sameside_of_Para_online aL bL ParaLM) ebN)
    (by perma[ParaLM])
  have acd_split := angle_add_of_sameside cN aN cO dO
    (by perma[sameside_of_B_DiffSide Bbcd cN (by perma[ebN])]) (by perma
    [(sameside_of_sameside_DiffSide cM cN cO eM aN (onLine_3_of_B (B_symm Bbcd) dO cO)
    (sameside_of_Para_online aL bL ParaLM) ebN)])
  have flat_sum := two_right_of_flat_angle Bbcd (onLine_3_of_B (B_symm Bbcd) dO cO) cO
    (online_1_of_Triangle (onLine_3_of_B (B_symm Bbcd) dO cO) cO tri_abc)
  exact ⟨by linperm, by linperm⟩

theorem sum_two_right_of_tri (tri_abc : Triangle a b c) :
    angle a b c + angle b c a + angle c a b = 2 * rightangle := by
  rcases length_eq_B_of_ne (ne_23_of_tri tri_abc) (ne_32_of_tri tri_abc) with ⟨d, Bbcd, _⟩
  exact (ext_int_sum_of_tri Bbcd tri_abc).2

theorem zero_lt_angle_of_tri (tri_abc : Triangle a b c) : 0 < angle c a b := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact zero_lt_angle_of_offline (ne_12_of_tri tri_abc) aL
    bL (online_3_of_Triangle aL bL tri_abc)

lemma ne_of_perp_ineq (Bxdy : B x d y) (tri_abc : Triangle a b c) (bL : OnLine b L)
    (cL : OnLine c L) (xL : OnLine x L) (cab_le_ra : rightangle ≤ angle c a b)
    (ady : angle a d y = rightangle) : b ≠ d := by
  intro bd; rw[←bd] at Bxdy ady
  linperm[right_of_online_right (ne_23_of_B Bxdy) tri_abc bL cL (onLine_3_of_B Bxdy xL bL) ady,
    sum_two_right_of_tri tri_abc, (zero_lt_angle_of_tri (by perma[tri_abc]) : 0 < angle b c a)]

theorem angle_add_of_B (Bbcd : B b c d) (bL : OnLine b L) (cL : OnLine c L) (aL : ¬OnLine a L) :
    angle d a b = angle c a d + angle c a b := by
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases line_of_pts a d with ⟨N, aN, dN⟩
  exact angle_add_of_sameside aN dN aM bM (sameSide_symm $ sameside_of_B_online_3 (B_symm Bbcd) dN
    $ offline_of_online_offline (ne_13_of_B Bbcd).symm aN dN (onLine_3_of_B Bbcd bL cL) bL aL)
    (sameSide_symm $ sameside_of_B_online_3 Bbcd bM $ offline_of_online_offline (ne_13_of_B Bbcd)
    aM bM bL (onLine_3_of_B Bbcd bL cL) aL)


lemma not_B_of_right_le_right (tri_abc : Triangle a b c) (col_bcd : Colinear b c d)
    (adb : angle a d b = rightangle) (cab_le_ra : rightangle ≤ angle c a b) : ¬B d b c := by
  intro Bdbc; rcases col_bcd with ⟨L, bL, cL, dL⟩
  have split := angle_add_of_B Bdbc dL bL (online_1_of_Triangle bL cL tri_abc)
  have sum_three := sum_two_right_of_tri (Triangle_of_ne_online (ne_13_of_B Bdbc) dL cL
    (online_1_of_Triangle bL cL tri_abc))
  linperm[angle_nonneg b a d, (zero_lt_angle_of_tri (by
    perma[Triangle_of_ne_online (ne_13_of_B Bdbc) dL cL (online_1_of_Triangle bL cL tri_abc)]) :
    0 < angle d c a), angle_extension_of_B (ne_of_online dL $ online_1_of_Triangle bL cL
    tri_abc) Bdbc]

/--A big enough angle has its perpendicular on a Triangle side-/
lemma right_B_of_le_right (tri_abc : Triangle a b c) (cab_le_ra : rightangle ≤ angle c a b) :
    ∃ d, angle a d b = rightangle ∧ angle a d c = rightangle ∧ B b d c := by
  rcases line_of_pts b c with ⟨L, bL, cL⟩
  rcases perpendicular_of_not_online (online_1_of_Triangle bL cL tri_abc) with
    ⟨x, y, d, Bxdy, xL, _, dL, adx, ady⟩
  have adb := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[Triangle_of_ne_online (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady) bL dL
          (online_1_of_Triangle bL cL tri_abc)] : Triangle a d b) dL bL xL adx
  have adc := right_of_online_right (ne_21_of_B Bxdy)
    (by perma[Triangle_of_ne_online (ne_of_perp_ineq Bxdy (by perma[tri_abc] : Triangle a c b)
    cL bL xL (by perma[cab_le_ra]) ady) cL dL (online_1_of_Triangle bL cL tri_abc)] : Triangle
     a d c) dL cL xL adx
  have := B_of_three_col_ne (ne_of_perp_ineq Bxdy tri_abc bL cL xL cab_le_ra ady).symm
    (ne_of_perp_ineq Bxdy (by perma[tri_abc] : Triangle a c b) cL bL xL (by perma[cab_le_ra])
    ady).symm (ne_23_of_tri tri_abc) ⟨L, dL, bL, cL⟩
  have := not_B_of_right_le_right tri_abc ⟨L, bL, cL, dL⟩ adb cab_le_ra
  have := not_B_of_right_le_right (by perma[tri_abc] : Triangle a c b) ⟨L, cL, bL, dL⟩ adc
    (by perma[cab_le_ra])
  tauto

theorem online_ne_of_point_line a L : ∃ b, a ≠ b ∧ OnLine b L := by -- a和L还能这样简写啊～～～
  rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩
  by_cases c = a; use b; rw[h] at bc; exact ⟨bc.symm, bL⟩
  use c; exact ⟨Ne.symm h, cL⟩

theorem online_of_ne_ne (ac : a ≠ c) (LM : L ≠ M) (aL : OnLine a L) (cL : OnLine c L)
    (cM : OnLine c M) : ¬OnLine a M := fun aM => LM $ line_unique_of_pts ac aL cL aM cM

theorem right_of_Para_right (aM : OnLine a M) (bM : OnLine b M) (bL : OnLine b L) (cL : OnLine c L)
    (cN : OnLine c N) (dN : OnLine d N) (aL : ¬OnLine a L) (dL : ¬OnLine d L)
    (bcd : angle b c d = rightangle) (ParaMN : Para M N) : angle a b c = rightangle := by
  by_cases adL : SameSide a d L
  linperm[interior_rightangles_of_Para aM bM bL cL cN dN adL ParaMN]
  linperm[alternate_eq_of_Para aM bM bL cL cN dN ⟨aL, dL, adL⟩ ParaMN]


theorem Para_trans (MN : M ≠ N) (ParaLM : Para L M) (ParaLN : Para L N) : Para M N := by
  intro x; push_contra int at int
  rcases perpendicular_of_not_online (offline_of_Para' int.1 ParaLM)
    with ⟨c, d, y, Bcyd, cL, dL, yL, xyc, xyd⟩
  rcases line_of_pts x y with ⟨O, xO, yO⟩
  rcases online_ne_of_point_line x M with ⟨a, xa, aM⟩
  rcases sameside_of_offline yO (offline_of_online_offline xa yO xO int.1 aM
    $ offline_of_Para yL ParaLM) (offline_of_Para yL ParaLN) xO int.2 with ⟨b, bN, baO⟩
  wlog yaN : SameSide y a N generalizing x y a b c d N M O; exact this MN.symm ParaLN ParaLM x
    ⟨int.2, int.1⟩ c d y Bcyd cL dL yL xyc xyd O xO yO b (ne_of_sameside xO baO).symm bN a aM
    (by perma[baO]) $ sameside_of_sameside_DiffSide xO int.2 int.1 yO bN aM baO ⟨offline_of_Para
    yL ParaLN, offline_of_online_offline xa bN int.2 int.1 aM $ online_of_ne_ne
    (ne_of_sameside xO baO) MN.symm bN int.2 int.1, yaN⟩
  have split := angle_add_of_sameside int.2 bN xO yO yaN baO
  have axy := right_of_Para_right aM int.1 xO yO yL cL (not_onLine_of_sameSide $ sameSide_symm baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_Para' int.1 ParaLM)) xyc
    (Para_symm ParaLM)
  have bxy := right_of_Para_right bN int.2 xO yO yL cL (not_onLine_of_sameSide baO)
    (offline_of_online_offline (ne_21_of_B Bcyd) xO yO yL cL (offline_of_Para' int.1 ParaLM)) xyc
    (Para_symm ParaLN)
  linarith[zero_lt_angle_of_tri $ Triangle_of_ne_online (ne_of_sameside xO baO).symm int.2 bN
    (not_onLine_of_sameSide $ sameSide_symm yaN)]


lemma inter_sq_of_perp (Bbxc : B b x c) (aX : OnLine a X) (xX : OnLine x X)
    (pgram1 : Paragram b c d e L O P Q) (adL : DiffSide a d L) : ∃ l, OnLine l X ∧ OnLine l P := by
  have ⟨bL, cL, _, _, _, _, _, _, ParaLP, _⟩ := pgram1
  by_cases ParaXP : Para X P; have := onLine_2_of_B Bbxc bL cL; have := Para_trans
    (ne_line_of_online aX adL.1) (Para_symm ParaLP) (Para_symm ParaXP) x; tauto
  unfold Para at ParaXP; push_neg at ParaXP; exact ParaXP

theorem sameside_of_Para_online' (aN : OnLine a N) (bN : OnLine b N) (ParaMN : Para M N) :
    SameSide a b M := sameside_of_Para_online aN bN (Para_symm ParaMN)

theorem B_of_sq (Bbxc : B b x c) (xX : OnLine x X) (lX : OnLine l X) (lP : OnLine l P)
    (ParaQX : Para Q X) (ParaOX : Para O X) (pgram : Paragram b c d e L O P Q) : B e l d := by
  have ⟨_, _, cO, dO, dP, eP, eQ, bQ, _, _⟩ := pgram
  exact B_of_col_DiffSide ⟨P, eP, lP, dP⟩ lX $ DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameside_of_Para_online cO dO ParaOX) $ DiffSide_symm $ DiffSide_of_sameside_DiffSide
    (sameSide_symm $ sameside_of_Para_online eQ bQ ParaQX) $ DiffSide_of_B_offline' Bbxc xX $
    offline_of_Para bQ ParaQX

theorem sameside_of_pyth (Beld : B e l d) (aX : OnLine a X) (lX : OnLine l X)
    (pgram : Paragram b c d e L O P Q) (ParaQX : Para Q X) : SameSide a c Q := by
  have ⟨_, _, cO, dO, _, _, eQ, _, _, ParaOQ⟩ := pgram
  exact sameSide_trans (sameSide_trans (sameside_of_B_online_3 Beld eQ $ offline_of_Para dO ParaOQ)
    $ sameSide_symm $ sameside_of_Para_online' aX lX ParaQX) $ sameSide_symm $
    sameside_of_Para_online cO dO ParaOQ

theorem DiffSide_of_Paragram (bL : OnLine b L) (dL : OnLine d L)
    (pgram : Paragram a b c d M N O P) : DiffSide a c L := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  exact DiffSide_of_sameside_sameside bM bL bN aM dL cN (sameside_of_Para_online' cO dO ParaMO)
    (sameside_of_Para_online' aP dP ParaNP)

theorem ang_2_nonzero_of_tri (tri_abc : Triangle a b c) : angle b a c ≠ 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; linarith[zero_lt_angle_of_offline (ne_12_of_tri
    tri_abc) aL bL (online_3_of_Triangle aL bL tri_abc), angle_symm b a c]

theorem angle_zero_of_lt_eq_B (ab : a ≠ b) (Bbcd : B b c d) (tri_bad : Triangle b a d)
    (bad_bac : angle b a d = angle b a c) : angle c a d = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩; exact angle_zero_of_lt_eq ab aL bL (sameSide_symm $
    sameside_of_B_online_3 Bbcd bL (online_3_of_Triangle bL aL tri_bad)) bad_bac

theorem asa' (tri_abc : Triangle a b c) (tri_def : Triangle d e f) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e := by
  wlog df_le_ac : length d f ≤ length a c generalizing a b c d e f; have' := this tri_def tri_abc
    ab_de.symm bac_edf.symm abc_def.symm (by linarith); tauto
  by_cases ac_df : length a c = length d f; have := sas ab_de ac_df bac_edf; tauto
  rcases B_length_eq_of_ne_lt (ne_13_of_tri tri_def) $ Ne.lt_of_le (Ne.symm ac_df) df_le_ac
    with ⟨g, Bagc, ag_df⟩
  have : angle a b g = angle d e f :=
    (sas ag_df ab_de $ by linperm[angle_extension_of_B' (ne_12_of_tri tri_abc) Bagc]).2.2
  exfalso; exact ang_2_nonzero_of_tri (tri_of_B_tri Bagc $ tri213 tri_abc) $ angle_zero_of_lt_eq_B
    (ne_21_of_tri tri_abc) Bagc tri_abc $ by linarith

theorem ang_121_zero_of_ne (ab : a ≠ b) : angle a b a = 0 := by
  rcases line_of_pts a b with ⟨L, aL, bL⟩
  exact angle_zero_of_online ab.symm ab.symm bL aL aL $ fun Baba => ne_13_of_B Baba rfl


theorem ne_23_of_sa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf ab_de
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_12_of_tri tri_abc) ab_de).symm,
    zero_lt_angle_of_tri tri_abc]

theorem not_B_of_tri_ang (tri_abc : Triangle a b c) (ef : e ≠ f) (de : d ≠ e)
    (abc_def : angle a b c = angle d e f) : ¬B e d f := by
  intro Bedf; rcases col_of_B Bedf with ⟨L, eL, dL, fL⟩
  linperm [angle_zero_of_online de.symm ef eL dL fL $ not_B_of_B Bedf, zero_lt_angle_of_tri $
    tri213 tri_abc]

theorem Triangle_of_asa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    Triangle d e f := by
  intro col_def
  have df := ne_23_of_sa (tri213 tri_abc) (by linperm) abc_def
  have de := ne_of_ne_len (ne_12_of_tri tri_abc) ab_de
  rcases B_of_three_col_ne de df (ne_23_of_sa tri_abc ab_de bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa tri_abc ab_de bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem asa (tri_abc : Triangle a b c) (ab_de : length a b = length d e)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a c = length d f ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  asa' tri_abc (Triangle_of_asa tri_abc ab_de bac_edf abc_def) ab_de bac_edf abc_def

theorem tri124_of_Paragram (pgram : Paragram a b c d M N O P) : Triangle a b d := by
  have ⟨aM, bM, bN, cN, _, dO, _, aP, ParaMO, ParaNP⟩ := pgram
  exact Triangle_of_ne_online (ne_of_sameside' aP $ sameside_of_Para_online
    bN cN ParaNP) aM bM $ offline_of_Para dO $ Para_symm ParaMO

theorem len_ang_area_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    length a b = length c d ∧ angle b a d = angle b c d ∧ area a b d = area b c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  rcases line_of_pts b d with ⟨L, bL, dL⟩
  have abd_bdc : angle a b d = angle b d c := alternate_eq_of_Para aM bM bL dL
    dO cO (DiffSide_of_Paragram bL dL pgram) ParaMO
  have adb_dbc : angle a d b = angle d b c := alternate_eq_of_Para aP dP dL bL bN cN
    (DiffSide_of_Paragram bL dL pgram) $ Para_symm ParaNP; perm at adb_dbc
  have ⟨ba_dc, da_bc, bad_dcb⟩ := asa (by perma[tri124_of_Paragram pgram])
    (length_symm b d) (by perma : angle d b a = angle b d c) (by perma)
  have : area b a d = area d c b := area_eq_of_SSS ba_dc (length_symm b d) (by linperm[da_bc])
  perm at *; exact ⟨ba_dc, bad_dcb, this⟩

theorem area_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    area a b d = area b c d := (len_ang_area_eq_of_Parallelogram pgram).2.2

theorem ne_of_Para' (aM : OnLine a M) (bN : OnLine b N) (ParaMN : Para M N) : b ≠ a :=
  ne_of_online' aM $ offline_of_Para' bN ParaMN


theorem pgram_of_Para_len_eq (aL : OnLine a L) (bL : OnLine b L) (bO : OnLine b O)
    (dO : OnLine d O) (dM : OnLine d M) (cM : OnLine c M) (cN : OnLine c N) (aN : OnLine a N)
    (bP : OnLine b P) (cP : OnLine c P) (aPd : DiffSide a d P) (ParaLM : Para L M)
    (ab_cd : length a b = length c d) : Paragram a b d c L O M N := by
  have abc_bcd := alternate_eq_of_Para aL bL bP cP cM dM aPd ParaLM
  obtain ⟨-, -, bca_cbd⟩ := sas (by perma : length b a = length c d) (length_symm b c) (by perma)
  exact ⟨aL, bL, bO, dO, dM, cM, cN, aN, ParaLM, Para_symm $
    Para_of_ang_eq (ne_of_Para' bL cM ParaLM) aN cN cP bP bO dO aPd bca_cbd⟩


lemma Paragram_of_tri_Para (bc : b ≠ c) (bM : OnLine b M) (cM : OnLine c M) (aN : OnLine a N)
    (ParaMN : Para M N) : ∃ d L O, Paragram d a c b N L M O := by
  rcases line_of_pts a c with ⟨L, aL, cL⟩
  rcases line_of_pts a b with ⟨P, aP, bP⟩
  rcases length_eq_of_sameside bP (online_3_of_Triangle aP bP
    (by perma[Triangle_of_ne_online bc bM cM $ offline_of_Para' aN ParaMN]))
    (offline_of_Para bM ParaMN) aP aN with ⟨d, dN, dcP, da_bc⟩
  rcases line_of_pts d b with ⟨O, dO, bO⟩
  exact ⟨d, L, O, pgram_of_Para_len_eq dN aN aL cL cM bM bO dO aP bP dcP (by perma) da_bc⟩

theorem sameside_of_sameside_Para (aN : OnLine a N) (bN : OnLine b N) (acM : SameSide a c M)
    (ParaMN : Para M N) : SameSide b c M :=
  sameSide_trans (sameside_of_Para_online' aN bN ParaMN) acM

theorem DiffSide_of_sameside_Paragram (fL : OnLine f L) (cP : OnLine c P) (fP : OnLine f P)
    (afM : SameSide a f M) (pgram : Paragram a b c d L M N O) : DiffSide b d P := by
have ⟨_, bL, bM, cM, cN, dN, dO, aO, ParaLN, ParaMO⟩ := pgram
exact DiffSide_of_sameside_sameside cM cP cN bM fP dN (sameside_of_sameside_Para aO dO afM ParaMO)
  (sameside_of_Para_online bL fL ParaLN)


theorem DiffSide_of_sameside_2_Paragram (afM : SameSide a f M) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : DiffSide e d P := by
  have ⟨_, fL, fP, cP, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  exact DiffSide_of_sameside_DiffSide (sameside_of_Para_online' bQ eQ ParaPQ)
    (by perma[DiffSide_of_sameside_Paragram fL cP fP afM pgram1])

theorem offline_of_col_offline (bc : b ≠ c) (col_abc : Colinear a b c) (bL : OnLine b L)
    (aL : ¬OnLine a L) : ¬OnLine c L :=
  fun cL => aL $ online_of_col_online bc bL cL (by perma[col_abc])


theorem B_of_col_offline (bc : b ≠ c) (col_abc : Colinear a b c) (bL : OnLine b L)
    (aL : ¬OnLine a L) (acL : ¬SameSide a c L) : B a b c :=
  B_of_col_DiffSide col_abc bL ⟨aL, offline_of_col_offline bc col_abc bL aL, acL⟩


theorem sameside_of_not_B (bc : b ≠ c) (Babc : ¬B a b c) (bL : OnLine b L) (aL : ¬OnLine a L)
    (col_abc : Colinear a b c) : SameSide a c L := by
  by_contra acL; exact Babc $ B_of_col_offline bc col_abc bL aL acL


theorem B_of_B_2_Paragram (df : d ≠ f) (Badf : ¬B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : B e f d := by
  have ⟨aL, dL, dM, _, _, _, _, aO, _, ParaMO⟩ := pgram1; have ⟨eL, fL, fP, _, _, _, _, _, _, _⟩ :=
    pgram2; exact B_of_col_DiffSide ⟨L, eL, fL, dL⟩ fP $ DiffSide_of_sameside_2_Paragram
    (sameside_of_not_B df Badf dM (offline_of_Para' aO ParaMO) ⟨L, aL, dL, fL⟩) pgram1 pgram2

theorem len_eq_of_Parallelogram (pgram : Paragram a b c d M N O P) :
    length a b = length c d := (len_ang_area_eq_of_Parallelogram pgram).1

theorem DiffSide_of_DiffSide_Para (aO : OnLine a O) (bO : OnLine b O) (afM : DiffSide a f M)
    (ParaMO : Para M O) : DiffSide b f M :=
  DiffSide_of_sameside_DiffSide (sameside_of_Para_online' aO bO ParaMO) afM

theorem DiffSide_of_B_Para (Badf : B a d f) (aL : OnLine a L) (dL : OnLine d L)
    (dM : OnLine d M) (cM : OnLine c M) (cN : OnLine c N) (ParaLN : Para L N) : DiffSide a f M :=
  DiffSide_of_B_offline Badf aL dL dM cM $ offline_of_Para' cN ParaLN


theorem DiffSide_of_B_pgram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O) :
    DiffSide b f M := by
  have ⟨aL, dL, dM, cM, cN, _, bO, aO, ParaLN, ParaMO⟩ := pgram1
  exact DiffSide_of_DiffSide_Para aO bO (DiffSide_of_B_Para Badf aL dL dM cM cN ParaLN) ParaMO


theorem sameside_of_B_pgram_pgram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : SameSide b d P := by
  have ⟨_, dL, dM, cM, cN, bN, _, _, ParaLN, _⟩ := pgram1
  exact sameside_of_sameside_DiffSide cN cM pgram2.2.2.2.1 bN dM pgram2.2.2.1
    (sameside_of_Para_online dL pgram2.2.1 ParaLN) $ DiffSide_of_B_pgram Badf pgram1


theorem sameside_of_B_prgram_pgram_trans (Badf : B a d f)
    (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q) : SameSide d e P := by
  have ⟨_, _, _, _, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  exact sameSide_trans (sameside_of_B_pgram_pgram Badf pgram1 pgram2) $
    sameside_of_Para_online' bQ eQ ParaPQ

theorem sameside_of_B_prgram_pgram_trans' (Badf : B a d f)
    (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q) : SameSide a e P :=
  sameSide_trans (sameSide_of_B_not_onLine_2 (B_symm Badf) pgram2.2.2.1
    (not_onLine_of_sameSide $ by perma[sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2])) $
    sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2

lemma B_sameside_of_2_Paragram (Badf : B a d f) (pgram1 : Paragram a d c b L M N O)
    (pgram2 : Paragram e f c b L P N Q) : B f e a ∧ SameSide d e P := by
  have ad_cb := len_eq_of_Parallelogram pgram1; have ef_cb := len_eq_of_Parallelogram pgram2
  rcases B_or_B_of_sameside (fun ae => by rw [←ae] at ef_cb; linarith[length_sum_perm_of_B Badf])
    pgram2.2.2.1 ⟨L, pgram2.2.1, pgram1.1, pgram2.1⟩ $ sameside_of_B_prgram_pgram_trans' Badf
    pgram1 pgram2 with Bet | Bet
  linperm[length_sum_perm_of_B Bet, length_sum_perm_of_B Badf]
  exact ⟨Bet, sameside_of_B_prgram_pgram_trans Badf pgram1 pgram2⟩

theorem len_eq_of_Parallelogram' (pgram : Paragram a b c d M N O P) :
    length a d = length c b := by
    have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram; exact len_eq_of_Parallelogram
      ⟨aP, dP, dO, cO, cN, bN, bM, aM, Para_symm ParaNP, Para_symm ParaMO⟩

theorem saa' (tri_abc : Triangle a b c) (tri_def : Triangle d e f) (ac_df : length a c =
    length d f) (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a b = length d e ∧ length b c = length e f ∧ angle a c b = angle d f e := by
  wlog de_le_ab : length d e ≤ length a b generalizing a b c d e f; have := this tri_def tri_abc
     ac_df.symm bac_edf.symm abc_def.symm (by linarith); tauto
  by_cases ab_de : length a b = length d e; have := sas ab_de ac_df bac_edf; tauto
  rcases B_length_eq_of_ne_lt (ne_12_of_tri tri_def) $ Ne.lt_of_le (Ne.symm ab_de) de_le_ab
    with ⟨g, Bagb, ag_de⟩
  have : angle c g a = angle d e f :=
    by perma[(sas ag_de ac_df $ by linarith[angle_extension_of_B (ne_13_of_tri tri_abc) Bagb]).2.1]
  have : angle g b c < angle c g a := internal_lt_external' (B_symm Bagb) $
    tri_143_of_tri_col (ne_32_of_B Bagb) (tri213 tri_abc) $ by perma[col_of_B Bagb]
  linarith[angle_extension_of_B (ne_23_of_tri tri_abc) (B_symm Bagb)]

theorem ne_23_of_sa' (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) : e ≠ f := by
  intro ef; rw [ef] at bac_edf
  linperm[ang_121_zero_of_ne (ne_of_ne_len (ne_13_of_tri tri_abc) ac_df).symm,
    zero_lt_angle_of_tri tri_abc]

theorem Triangle_of_saa (de : d ≠ e) (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    Triangle d e f := by
  intro col_def
  have df := ne_of_ne_len (ne_13_of_tri tri_abc) ac_df
  rcases B_of_three_col_ne de df (ne_23_of_sa' tri_abc ac_df bac_edf) col_def with Bet | Bet | Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) df de.symm bac_edf) Bet
  exact (not_B_of_tri_ang tri_abc (ne_23_of_sa' tri_abc ac_df bac_edf) de abc_def) Bet
  exact (not_B_of_tri_ang (tri213 tri_abc) de df.symm $ by linperm) Bet

theorem saa (de : d ≠ e) (tri_abc : Triangle a b c) (ac_df : length a c = length d f)
    (bac_edf : angle b a c = angle e d f) (abc_def : angle a b c = angle d e f) :
    length a b = length d e ∧ length b c = length e f ∧ angle a c b = angle d f e :=
  saa' tri_abc (Triangle_of_saa de tri_abc ac_df bac_edf abc_def) ac_df bac_edf abc_def

theorem tri_of_sameside (bc : b ≠ c) (bL : OnLine b L) (cL : OnLine c L) (adL : SameSide a d L) :
    Triangle a b c := tri312 $ Triangle_of_ne_online bc bL cL $ not_onLine_of_sameSide adL


theorem sameside_of_quad (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M) (cM : OnLine c M)
    (cN : OnLine c N) (dN : OnLine d N) (dO : OnLine d O) (aO : OnLine a O) (abN : SameSide a b N)
    (cdL : SameSide c d L) (adM : SameSide a d M) : SameSide b c O := by
  rcases line_of_pts b d with ⟨P, bP, dP⟩
  perma[sameside_of_sameside_DiffSide dN dP dO cN bP aO (by perma) $
    by perma[DiffSide_of_sameside_sameside bL bP bM aL dP cM cdL adM]]


theorem B_diagonal_of_quad (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M)
    (cM : OnLine c M) (cN : OnLine c N) (dN : OnLine d N) (abN : SameSide a b N)
    (cdL : SameSide c d L) (adM : SameSide a d M) : ∃ e P O, B b e d ∧ B a e c ∧ OnLine a P ∧
    OnLine c P ∧ OnLine b O ∧ OnLine d O ∧ OnLine e P ∧ OnLine e O ∧
    DiffSide b d P ∧ DiffSide a c O := by
  rcases line_of_pts b d with ⟨O, bO, dO⟩; rcases line_of_pts a c with ⟨P, aP, cP⟩
  rcases line_of_pts a d with ⟨Q, aQ, dQ⟩
  have acO := DiffSide_of_sameside_sameside bL bO bM aL dO cM cdL adM
  have bdP := DiffSide_of_sameside_sameside aL aP aQ bL cP dQ (by perma) $
    sameside_of_quad aL bL bM cM cN dN dQ aQ abN cdL adM
  rcases pt_of_online_not_sameside aP cP acO.2.2 with ⟨e, eO, eP⟩
  exact ⟨e, P, O, B_of_col_DiffSide ⟨O, bO, eO, dO⟩ eP bdP,
    B_of_col_DiffSide ⟨P, aP, eP, cP⟩ eO acO, aP, cP, bO, dO, eP, eO, bdP, acO⟩

theorem area_add_of_B (Babc : B a b c) (tri_dac : Triangle d a c) :
    area d a b + area d c b = area d a c := by
rcases line_of_pts a b with ⟨L, aL, bL⟩; have cL := onLine_3_of_B Babc aL bL
exact (area_add_iff_B (ne_12_of_B Babc) (ne_23_of_B Babc) (Ne.symm (ne_13_of_B Babc)) aL bL cL
  (online_1_of_Triangle aL cL tri_dac)).mp Babc

theorem area_add_of_B_offline (Babc : B a b c) (aL : OnLine a L) (cL : OnLine c L)
    (dL : ¬OnLine d L) : area d a b + area d c b = area d a c :=
area_add_of_B Babc $ by perma[Triangle_of_ne_online (ne_13_of_B Babc) aL cL dL]


theorem quad_area_comm (aL : OnLine a L) (bL : OnLine b L) (bM : OnLine b M) (cM : OnLine c M)
    (cN : OnLine c N) (dN : OnLine d N) (abN : SameSide a b N) (cdL : SameSide c d L)
    (adM : SameSide a d M) : area a b d + area b c d = area a b c + area a c d := by
  rcases B_diagonal_of_quad aL bL bM cM cN dN abN cdL adM with
    ⟨e, P, O, Bbed, Baec, aP, cP, bO, dO, eP, eO, bdP, acO⟩
  linperm[area_add_of_B_offline Bbed bO dO acO.1, area_add_of_B_offline Bbed bO dO acO.2.1,
    area_add_of_B_offline Baec aP cP bdP.1, area_add_of_B_offline Baec aP cP bdP.2.1]


theorem Paragram_area_comm (pgram : Paragram a b c d M N O P) :
    area a b d + area b c d = area a b c + area a c d := by
  have ⟨aM, bM, bN, cN, cO, dO, dP, aP, ParaMO, ParaNP⟩ := pgram
  exact quad_area_comm aM bM bN cN cO dO (sameside_of_Para_online aM bM ParaMO)
    (sameside_of_Para_online' cO dO ParaMO) $ sameside_of_Para_online' aP dP ParaNP

theorem sameside_of_B_Para (Bfea : B f e a) (fP : OnLine f P) (eQ : OnLine e Q) (bQ : OnLine b Q)
    (ParaPQ : Para P Q) : SameSide a b P := sameSide_trans (sameSide_of_B_not_onLine_2 Bfea fP $
  offline_of_Para' eQ ParaPQ) $ sameside_of_Para_online' eQ bQ ParaPQ


theorem area_eq_of_Paragram (pgram1 : Paragram a d c b L M N O) (pgram2 : Paragram e f c b L P N Q):
    area a d b + area d b c = area e f b + area f b c := by
  wlog Badf : B a d f generalizing a b c d e f L M N O P Q; by_cases df : d = f; rw [←df] at pgram2
    ⊢; linperm [(len_ang_area_eq_of_Parallelogram pgram1).2.2, (len_ang_area_eq_of_Parallelogram
    pgram2).2.2]; exact (this pgram2 pgram1 $ B_of_B_2_Paragram df Badf pgram1 pgram2).symm
  have ⟨Bfea, deP⟩ := B_sameside_of_2_Paragram Badf pgram1 pgram2
  have ⟨aL, dL, dM, cM, cN, bN, bO, aO, ParaLN, ParaMO⟩ := pgram1
  have ⟨eL, fL, fP, cP, _, _, bQ, eQ, _, ParaPQ⟩ := pgram2
  have fdc_dab := correspond_of_Para (B_symm Badf) fL dL dM cM aO bO
    (sameside_of_Para_online' cN bN ParaLN) ParaMO
  have aeb_efc := correspond_of_Para (B_symm Bfea) aL eL eQ bQ fP cP
    (sameside_of_Para_online' bN cN ParaLN) $ Para_symm ParaPQ
  have dc_ab : length d c = length a b := by linperm[len_eq_of_Parallelogram' pgram1]
  have ae_df := (saa (ne_32_of_B Bfea) (tri_of_sameside (ne_of_Para fL cN ParaLN) fP cP deP) dc_ab
    (fdc_dab.trans (angle_extension_of_sameside (ne_of_Para' aL bN ParaLN) aO ⟨L, aL, dL, eL⟩ $
    by perma[(B_sameside_of_2_Paragram Bfea ⟨fL, eL, eQ, bQ, bN, cN, cP, fP, ParaLN, Para_symm
    ParaPQ⟩ ⟨dL, aL, aO, bO, bN, cN, cM, dM, ParaLN, Para_symm ParaMO⟩).2])) (aeb_efc.trans $
    angle_extension_of_sameside (ne_of_Para' fL cN ParaLN) fP ⟨L, fL, eL, dL⟩ $ by
    perma[deP]).symm).1.symm
  have ab_cd := len_eq_of_Parallelogram' pgram1; have eb_cf := len_eq_of_Parallelogram' pgram2
  have aeb_dfc := area_eq_of_SSS ae_df (by perma : length a b = length d c) $ by perma[eb_cf]
  have ar1 := Paragram_area_comm pgram1
  have ar2 := quad_area_comm aL fL fP cP cN bN (sameside_of_Para_online aL fL ParaLN)
    (sameside_of_Para_online' cN bN ParaLN) $ sameside_of_B_Para Bfea fP eQ bQ ParaPQ
  have ar3 := area_add_of_B_offline Badf aL fL $ offline_of_Para' cN ParaLN
  have ar4 := area_add_of_B_offline Bfea fL aL $ offline_of_Para' bN ParaLN
  linperm

theorem area_eq_of_tri (aL : OnLine a L) (dL : OnLine d L) (bM : OnLine b M) (cM : OnLine c M)
    (ParaLM : Para L M) : area a b c = area d b c := by
  by_cases bc : b = c; rw [bc]; linperm[degenerate_area c a, degenerate_area c d]
  rcases Paragram_of_tri_Para bc bM cM aL (by perma[ParaLM]) with ⟨e, N, O, pgram1⟩
  rcases Paragram_of_tri_Para bc bM cM dL (by perma[ParaLM]) with ⟨f, P, Q, pgram2⟩
  have pgram_eq := area_eq_of_Paragram pgram1 pgram2
  have half_pgram1 := area_eq_of_Parallelogram pgram1
  have half_pgram2 := area_eq_of_Parallelogram pgram2
  linperm

theorem twice_pgram_of_tri  (eL : OnLine e L) (pgram : Paragram a b c d L M N O) :
    area a b d + area b c d = 2 * area c d e := by
  have ⟨_, _, _, _, cN, dN, _, _, ParaLM, _⟩ := pgram
  have pgram_eq := area_eq_of_Parallelogram pgram
  have tri_eq := area_eq_of_tri pgram.2.1 eL cN dN ParaLM
  linperm


theorem sameside_of_B_sameside (Bbcd : B b c d) (dL : OnLine d L) (bL : ¬OnLine b L)
    (abL : SameSide a b L) : SameSide a c L :=
  sameSide_trans (sameSide_symm abL) $ sameSide_symm $ sameside_of_B_online_3 (B_symm Bbcd) dL bL


theorem quad_add_of_quad (Babc : B a b c) (Bdef : B d e f) (aL : OnLine a L) (bL : OnLine b L)
    (cM : OnLine c M) (fM : OnLine f M) (dN : OnLine d N) (eN : OnLine e N) (acN : SameSide a c N)
    (feL : SameSide f e L) (adM : SameSide a d M) :
    area a c f + area a f d = area a b e + area a e d + area b c e + area f e c := by
  rcases B_diagonal_of_quad aL (onLine_3_of_B Babc aL bL) cM fM (onLine_3_of_B Bdef dN eN) eN acN
    feL $ sameside_of_B_sameside Bdef fM (not_onLine_of_sameSide $ sameSide_symm adM) adM
    with ⟨g, P, O, Bcge, Bagf, aP, fP, cO, eO, gP, gO, ceP, afO⟩
  linperm[area_add_of_B_offline Bagf aP fP ceP.1, area_add_of_B_offline Bdef dN
    (onLine_3_of_B Bdef dN eN) (not_onLine_of_sameSide acN), area_add_of_B_offline Bagf aP fP
    ceP.2.1, area_add_of_B_offline Bcge cO eO afO.2.1, area_add_of_B_offline Bcge cO eO afO.1,
    area_add_of_B_offline Babc aL (onLine_3_of_B Babc aL bL)
    (not_onLine_of_sameSide (by perma[feL]))]

-- 反向看

/--  -/
theorem pythagoras (tri_abc : Triangle a b c) (ang : angle c a b = rightangle)
    (sq1 : Square c d e b) (sq2 : Square a g f b) (sq3 : Square a h k c)
    (pgram1 : Paragram b c d e L O P Q) (pgram2 : Paragram g a b f T N R S) (pgram3 : Paragram h a c k U M W V)
    (adL : DiffSide a d L) (bhM : DiffSide b h M) (cgN : DiffSide c g N) :
    area b c d + area b d e = area a b f + area a g f + area a h k + area a c k := by
  unfold Square at sq1 sq2 sq3
  have ⟨bL, cL, cO, dO, dP, eP, eQ, bQ, ParaLP, ParaOQ⟩ := pgram1
  have ⟨gT, aT, aN, bN, bR, fR, fS, gS, ParaTR, ParaNS⟩ := pgram2
  have ⟨hU, aU, aM, cM, cW, kW, kV, hV, ParaUW, ParaMV⟩ := pgram3
  have Bcag := flat_of_two_right_angle (ne_12_of_tri tri_abc) aN bN cgN (by linperm)
  have Bbah := flat_of_two_right_angle (ne_13_of_tri tri_abc) aM cM bhM (by linperm)
  rcases right_B_of_le_right tri_abc (by linarith) with ⟨x, axb, axc, Bbxc⟩
  rcases line_of_pts a x with ⟨X, aX, xX⟩
  rcases inter_sq_of_perp Bbxc aX xX pgram1 adL with ⟨l, lX, lP⟩
  have ParaQX := Para_of_ang_eq (ne_12_of_B Bbxc) eQ bQ bL (onLine_2_of_B Bbxc bL cL) xX aX
    (DiffSide_of_sameside_DiffSide (sameside_of_Para_online' dP eP ParaLP) (DiffSide_symm adL))
    (by linperm[angle_extension_of_B (ne_of_Para bL eP ParaLP) Bbxc])
  have ParaOX := Para_of_ang_eq (ne_32_of_B Bbxc) dO cO cL (onLine_2_of_B Bbxc bL cL) xX aX
    (DiffSide_symm adL) (by linperm[angle_extension_of_B (ne_of_Para cL dP ParaLP) $ B_symm Bbxc])
  have Beld := B_of_sq Bbxc xX lX lP ParaQX ParaOX pgram1
  have fbc_split := angle_add_of_sameside bR fR bL cL (sameSide_symm $ sameside_of_Para_online aT
    (onLine_3_of_B (B_symm Bcag) gT aT) ParaTR) $ sameside_of_sameside_DiffSide bR bN bL fR aN cL
    (sameside_of_Para_online aT (onLine_3_of_B (B_symm Bcag) gT aT) ParaTR) $
    DiffSide_of_sameside_DiffSide (sameSide_symm $ sameside_of_Para_online' fS gS ParaNS) $
    DiffSide_symm cgN
  have abe_split := angle_add_of_sameside bN aN bQ eQ (sameside_of_sameside_DiffSide bQ bL bN eQ cL
    aN (sameSide_symm $ sameside_of_pyth Beld aX lX pgram1 ParaQX) $ DiffSide_of_sameside_DiffSide
    (sameside_of_Para_online' dP eP ParaLP) $ DiffSide_symm adL) $ sameside_of_pyth Beld aX lX
    pgram1 ParaQX
  have bck_split := angle_add_of_sameside cL bL cW kW (sameside_of_sameside_DiffSide cW cM cL kW aM
    bL (sameside_of_Para_online aU (onLine_3_of_B (B_symm Bbah) hU aU) ParaUW) $
    DiffSide_of_sameside_DiffSide (sameside_of_Para_online' hV kV ParaMV) $ DiffSide_symm bhM)
    (sameSide_symm $ sameside_of_Para_online aU (onLine_3_of_B (B_symm Bbah) hU aU) ParaUW)
  have acd_split := angle_add_of_sameside cM aM cO dO (sameside_of_sameside_DiffSide cO cL cM dO bL
    aM (sameSide_symm $ sameside_of_pyth (B_symm Beld) aX lX ⟨cL, bL, bQ, eQ, eP, dP, dO, cO,
    ParaLP, Para_symm ParaOQ⟩ ParaOX) $ DiffSide_symm adL) $ sameside_of_pyth (B_symm Beld) aX lX
    ⟨cL, bL, bQ, eQ, eP, dP, dO, cO, ParaLP, Para_symm ParaOQ⟩ ParaOX
  have ⟨ae_fc, _, _⟩ := sas (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) $ by linperm
  have tri1_eq := area_eq_of_SSS (by linperm : length b a = length b f)
    (by linperm : length b e = length b c) ae_fc
  have ⟨ad_kb, _, _⟩ := sas (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) $ by linperm
  have tri2_eq := area_eq_of_SSS (by linperm : length c a = length c k)
    (by linperm : length c d = length c b) ad_kb
  have tri_req1 := twice_pgram_of_tri aX
    ⟨xX, lX, lP, eP, eQ, bQ, bL, onLine_2_of_B Bbxc bL cL, Para_symm ParaQX, Para_symm ParaLP⟩
  have tri_req2 := twice_pgram_of_tri (onLine_3_of_B (B_symm Bcag) gT aT) pgram2
  have tri_req3 := twice_pgram_of_tri aX
    ⟨lX, xX, onLine_2_of_B Bbxc bL cL, cL, cO, dO, dP, lP, Para_symm ParaOX, ParaLP⟩
  have tri_req4 := twice_pgram_of_tri (onLine_3_of_B (B_symm Bbah) hU aU) pgram3
  have sq_split := quad_add_of_quad Bbxc Beld bL (onLine_2_of_B Bbxc bL cL) cO dO eP lP
    (sameside_of_Para_online bL cL ParaLP) (sameside_of_Para_online' dP lP ParaLP)
    $ sameside_of_Para_online' bQ eQ ParaOQ
  have right_half := quad_area_comm (onLine_2_of_B Bbxc bL cL) cL cO dO dP lP
    (sameside_of_Para_online (onLine_2_of_B Bbxc bL cL) cL ParaLP)
    (sameside_of_Para_online' dP lP ParaLP) $ sameside_of_Para_online' xX lX ParaOX
  linperm
  done

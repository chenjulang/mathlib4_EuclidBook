import Mathlib.Geometry.Synthetic.Avigad.Tactics
import Mathlib.Geometry.Synthetic.Avigad.EuclidBookI
import Mathlib.Tactic.WLOG

variable [I : IncidenceGeometry] {a a1 a2 b b1 b2 c d e f g h i j k l m n o p q s x y :
  IncidenceGeometry.Point} {L M N O P Q R S T U W V X : IncidenceGeometry.Line}
  {α β : IncidenceGeometry.Circle} {r : ℝ}
namespace IncidenceGeometry
-- open Topology Filter

-- todolist
-- 0.将命题描述成中文，改写代码成不跳步。 -- ok
-- 1.将两个椭圆的定义互相等价证明一下。
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

-- todo 证明或者定义：点和线的距离等于点到垂足点的长度。


/--  椭圆的第一种定义：
存在一个定点(S)，一条定直线(XM)，e是一个小于1的常数，点P满足：SP = e * PM 。
所有这样的点P组成的曲线就是椭圆形。
-/
def Point_on_Ellipse (P:Point) (S : Point) (XM :Line) (E : ℝ) : Prop :=
  (length P S) = E * (distance P XM)
